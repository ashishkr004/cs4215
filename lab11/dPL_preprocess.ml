(* PLEASE DO NOT CHANGE THIS FILE *)

open DPL_unify
open Debug.Basic
open DPL
module C = DPLc

let vnames = new generator "var"




(* let set_source_file (arg:string) =  *)
(*   source_files := arg :: !source_files *)

(* let process_cmd_line () =  *)
(*   Arg.parse option_flag set_source_file usage *)

let usage = "usage: " ^ Sys.argv.(0) ^ " [options] <filename>"

let triple_to_type_decl (t: (string * string list * (string * dPL_type list) list)): id * dPL_type_decl = 
    match t with
    | (id0,tvars,data) ->
        (id0, {ty_def_name = id0; ty_def_param = tvars; ty_def_data = data })

let add_type_decl_to_env (t: (string * string list * (string * dPL_type list) list) list) =      
    let rec helper lst =
    match lst with
    |  x::xs -> 
            let (id,td) = triple_to_type_decl x in
            ty_dict#add id td; helper xs 
    | [] -> () in
    helper t

(* calling dPL parser *)

let parse_file (filename:string) : (string * ('a list * dPL_nexpr)) =
    DPL_parser.parse_file filename

let find_position i =
    let (n,_,_) = ty_dict # find_tag i in
    n

let nest_2_simp p =
    match p with
    | PVar _ -> failwith "var pattern detected"
    | PCons (i,_,lst) ->
        let p = find_position i in
        (i,p,List.map (fun v -> match v with
        | PVar v -> v
        | _ -> failwith "nested pattern detected") lst)

let rec custom_nest_2_simp (aux) (p:DPL.dPL_pat) (e:DPL.dPL_pat DPL.dPL_expr_gen):((DPL.id * int * DPL.id list) * (DPL.id * int * DPL.id list) DPL.dPL_expr_gen) =
    match p with
    | PVar _ -> failwith "var pattern detected"
    | PCons (i,_,lst) ->
        let nested_cons = List.filter (fun x ->
            match x with
            | PCons _ -> true
            | _ -> false
        ) lst in
        let fn_init = fun fvar ->
            let map_p = fun v -> match v with
                | PVar v -> v
                | PCons _ -> fvar
            in (map_p)
        in
        let p = find_position i in
        match List.map (fun x ->
            let i = vnames # fresh_id in
            let target_e = Match(Var(i), [(x,e)]) in
            (i, target_e)
        ) nested_cons with
        | (fvar, target_e)::[] ->
            let (mpv) = fn_init fvar in
            ((i,p, (List.map mpv lst)), aux target_e)
        | [] ->
            let (mpv) = fn_init "_" in
            ((i,p, (List.map mpv lst)), aux e)
        | (_,_)::xs -> failwith "support for multiple elements nested at a level is not implemented"
        | _ -> failwith "something went wrong"

            

let norm_match (e:dPL_nexpr) : dPL_expr =
    let rec aux e =
    match e with
    | Unit -> Unit
    | IntConst i -> IntConst i
    | BoolConst b -> BoolConst b 
    | Var v -> Var v
    | UnaryPrimApp (op,arg) 
            -> UnaryPrimApp (op,aux arg) 
    | BinaryPrimApp (op,arg1,arg2)
            -> BinaryPrimApp (op,aux arg1,aux arg2) 
    | Throw e 
            -> Throw (aux e)
    | TryCatch (e1,v,e2) 
            -> TryCatch (aux e1,v,aux e2)
    | Cond (e1,e2,e3) 
            -> Cond (aux e1,aux e2,aux e3)
    | Match (em, lst) ->
        begin
            let (first_ty, _) = List.hd lst in
            match first_ty with
            | PCons (id, n, _) ->
                begin
                    match ty_dict#find_tag id with
                    | n, ty_list, ty_decl ->
                        begin
                            let simple = List.map (fun (p,e)->(custom_nest_2_simp aux p e)) lst in
                            let ordered = List.sort (fun ((_,n1,_), _) ((_,n2,_), _) ->
                                if n1 < n2 then
                                    -1
                                else if n1 > n2 then
                                    1
                                else 0
                            ) simple in
                            let rec insert_missing = fun ordered_lst def_lst i ->
                                match ordered_lst, def_lst with
                                | ((idx,_,_), _)::oxs, (idy, _)::dxs when idx = idy -> (List.hd ordered_lst)::(insert_missing oxs dxs (i+1))
                                | [], (idy, _)::dxs
                                | _, (idy, _)::dxs ->
                                    let rec create_param_lst = fun x ->
                                        begin
                                            if x = 0
                                            then
                                                []
                                            else
                                                "_"::(create_param_lst (x-1))
                                        end
                                    in
                                    let param_lst = create_param_lst (List.length ty_decl.ty_def_data) in
                                    ((idy, (i+1), []), Throw(IntConst(i+1)))::(insert_missing ordered_lst dxs (i+1))
                                | [], [] -> []
                            in
                            let ins = insert_missing ordered ty_decl.ty_def_data 0 in
                            Match(aux em, ins)
                        end
                end
            | PVar _ -> failwith "TODO?"
        (* | _ -> raise "Failed to find type" *)
        end
            
    | Constr (i,tag,args) ->
        let n =  find_position i in
        Constr (i,n,List.map aux args)
    | HasType (e,t) 
        -> HasType (aux e,t)
    | Appln (e1,t,args) 
        -> Appln(aux e1,t,List.map aux args)
    | Func (te,args,body) 
        -> Func (te,args,aux body)
    | Let (lst,t,body) 
        -> Let (List.map (fun (v,t,e)-> (v,t,aux e)) lst,t,aux body)
    | RecFunc (te,id,args,body) 
        ->  RecFunc (te,id,args,aux body)
    in aux e

let parse_file (filename:string) : string * dPL_nexpr =
    let (s,(l,e)) = (parse_file filename) in
    let _ = add_type_decl_to_env l in
    (s,e)

let pre_proc (e:dPL_nexpr) : dPL_expr
    = norm_match e

