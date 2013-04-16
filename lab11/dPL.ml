open Debug.Basic

type op_id = string
type id = string

type dPL_type =
  | BoolType
  | IntType
  | Void
  | Arrow of dPL_type * dPL_type
  | TVar of id
  | TError
  (* | Pair of dPL_type * dPL_type *)
  (* | Sum of dPL_type * dPL_type *)
  | TDef of id * (dPL_type list)
  | TUniv of id list * dPL_type
        (* inner type should not have 
           further universal quantifiers *)

type dPL_type_decl =
    { ty_def_name : id; (* name of type def *)
      ty_def_param : id list; (* type vars *)
      ty_def_data : (id * dPL_type list) list; 
   }


let rec get_ctypes_constr name n lst = 
  match lst with
    | []         -> (-1, false, [TError])
    | (nm,t)::tl -> if (nm = name) then (n+1,true,t) else  get_ctypes_constr name (n+1) tl

let exists_constr name lst = 
  let (n, ex, t) =  get_ctypes_constr name 0 lst in 
  (n, ex, t)

let rec find_constr name lst = 
  match lst with
    | []        -> raise Not_found
    | (_,d)::tl -> 
          let (tag_no, exists, ty_lst) =  exists_constr name d.ty_def_data in
          if (not exists) then find_constr name tl
          else (tag_no, ty_lst, d)

(* this will be used to store each algebraic
   type that has been declared *)

class dict_class =
object (self)
  val mutable dict = Environ.empty_env

  method add v t =
    (* add a type declaration *)
    dict <- Environ.add_env dict v t

  method get_env = dict

  method get_decl v =
    (* get a type declaration *)
    Environ.get_val dict v

  method find_tag c : int * dPL_type list * dPL_type_decl  =
    (* find a constructor tag *)
    try
       find_constr c dict
    with _ -> raise Not_found

  method is_tag_in_dt (c: id) (dt: dPL_type_decl) :  bool  =
       List.exists (fun (i,_) -> i = c ) dt.ty_def_data

  method  find_tag_in_dt (c:id) (dt: dPL_type_decl) : int * dPL_type list =
    (* find a constructor tag *)
    try
      (* let (id0, ty_lst) = List.find (fun (i,_)-> i = c ) dt.ty_def_data in *)
      let (pos, _, ty_lst) =  exists_constr c dt.ty_def_data in
      (pos, ty_lst)
    with _ -> raise Not_found 

  method find_tag_types (c:id)  :  (id * dPL_type list) option =
    (* find a constructor tag *)
    let (_, _, dt) = self#find_tag c in
    let (id0, ty_lst) = List.find (fun (i,_)->i=c) dt.ty_def_data in
    Some (dt.ty_def_name, ty_lst)

end;;

let ty_dict = new dict_class

(* abstract syntax tree for dPL *)
type dPL_pat =
    PVar of id
  | PCons of id * int * (dPL_pat list)

type dPL_spat = id * int * id list

type 'pat dPL_expr_gen =
  | Unit
  | BoolConst of bool
  | IntConst of int
  | Var of id
  | UnaryPrimApp of op_id * ('pat dPL_expr_gen)
  | BinaryPrimApp of op_id * ('pat dPL_expr_gen) * ('pat dPL_expr_gen)
  | Cond of ('pat dPL_expr_gen) * ('pat dPL_expr_gen) * ('pat dPL_expr_gen)
  | HasType of ('pat dPL_expr_gen) * dPL_type
  | TryCatch of ('pat dPL_expr_gen) * id  * ('pat dPL_expr_gen)
  | Throw of ('pat dPL_expr_gen)
  | Constr of id * int * ('pat dPL_expr_gen) list
        (* only exact application allowed *)
  | Match of ('pat dPL_expr_gen) * ('pat * ('pat dPL_expr_gen)) list
        (* pattern-matching *)
  | Func of dPL_type option * (id list) * ('pat dPL_expr_gen) 
        (* min of one parameter *)
  | RecFunc of dPL_type option * id * (id list) * ('pat dPL_expr_gen) 
        (* min of one parameter *)
  | Appln of ('pat dPL_expr_gen) * dPL_type option * (('pat dPL_expr_gen) list) 
        (* at least one argument *)
  | Let of ((dPL_type option * id * ('pat dPL_expr_gen)) list) * dPL_type option * ('pat dPL_expr_gen)
        (* min of one binding; type declaration can be optional *)

type dPL_expr =  dPL_spat dPL_expr_gen

type dPL_nexpr =  dPL_pat dPL_expr_gen




(* DEFINE EXCEPTIONS *)
let divide_by_zero = IntConst(0)
let invalid_pattern_matching = IntConst(1)
let index_out_of_bounds = IntConst(2)
(* END DEFINE EXCEPTIONS *)

type dPL_typedef = id * (id list) * dPL_type

type dPL_def = id * dPL_expr * dPL_type

type dPL_prog = dPL_typedef list * dPL_def list


(* let pr_id e = e *)
(* let pr_lst s f xs = String.concat s (List.map f xs) *)
(* let pr_list_brk open_b close_b f xs  = open_b ^(pr_lst "," f xs)^close_b *)
(* let pr_list f xs = pr_list_brk "[" "]" f xs *)
(* let pr_opt_bracket p f e =  *)
(*   if p e then "("^(f e)^")" *)
(*   else f e *)

(* display dPL_type *)
(* PLEASE do not change *)
let string_of_dPL_type (e:dPL_type):string =
  let rec pr t =  
    pr_opt_bracket (fun e -> match e with Arrow _ -> true | _ ->false)
        aux t
  and aux e =
    match e with
      | BoolType -> "bool"
      | IntType -> "int"
      | Void -> "void"
      | TVar id -> id
      | TError -> "TError"
      | Arrow (t1,t2) -> (pr t1)^"->"^(aux t2)
      | TDef (i,ts) -> "("^i^" "^(pr_list_space pr ts)^")"
      | TUniv (vs,t) -> "(forall "^(pr_list pr_id vs)^(aux t)^")"
  in aux e

let string_of_dPL_npat (pat: dPL_pat): string=
  let rec aux p = 
    match p with 
      | PVar i -> i
      | PCons (i,n,plst) -> "(" ^ i ^ "{" ^ (string_of_int n) ^ "} " ^ (pr_list_space aux plst) ^ ")"
  in
  aux pat

let string_of_dPL_pat (pat: dPL_spat): string=
    match pat with 
      | (i,n,plst) -> "(" ^ i ^ "{" ^ (string_of_int n) ^ "} " ^ (pr_list_space pr_id plst) ^ ")"


let rec fvt t =
  match t with
    | BoolType | IntType | Void | TError -> []
    | TVar id -> [id]
    | Arrow (t1,t2) -> (fvt t1)@ (fvt t2)
    | TDef (_,ts) -> List.concat (List.map fvt ts)
    | TUniv (vs,t) -> diff (fvt t) vs

(* display dPL expr in prefix form *)
(* PLEASE do not change *)
let string_of_dPL_gen pr_pat (e:'p dPL_expr_gen):string =
  let pr_type t = "{"^(string_of_dPL_type t)^"}" in
  let pr_type_opt t = match t with
    | Some t -> pr_type t
    | None -> ""
  in
  let rec aux e =
  match e with
    | Unit-> "()"
    | BoolConst v -> "Bool("^(string_of_bool v)^")"
    | IntConst v -> "Int("^(string_of_int v)^")"
    | Var v -> "Var("^v^")"
    | UnaryPrimApp (op,arg) -> op^"["^(aux arg)^"]"
    | BinaryPrimApp (op,arg1,arg2) -> op^"["^(aux arg1)^","^(aux arg2)^"]"
    | HasType (ex,t) -> "("^(aux ex)^":"^(pr_type t)^")"
    | TryCatch (e1,id,e2) -> "try "^(aux e1)^" catch "^ id ^" with "^(aux e2)^" end"
    | Throw e -> "throw("^(aux e)^")"
    | Cond (e1,e2,e3) -> "if "^(aux e1)^" then "^(aux e2)
          ^" else "^(aux e3)^" end"
    | Func (t,args,body) -> "fun "^(pr_type_opt t)^" "^(pr_lst " " pr_id args)^" -> "^(aux body)^" end"
    | RecFunc (t,r,args,body) -> "recfun "^r^" "^(pr_type_opt t)^" "^(pr_lst " " pr_id args)^" -> "^(aux body)^" end"
    | Appln (e,t,args) -> "Appln["^(aux e)^
          (match t with
            | Some t -> ":"^(string_of_dPL_type t)
            | None -> "")^"; "^(pr_lst ";" aux args)^"]"
    | Constr (i,_,args) -> "("^i^" "^(pr_lst ";" aux args)^")"
    | Match (e1,lst) -> "\n(match "^(aux e1)^" with \n" ^ (pr_lst ";\n"
          (fun (p,e)-> (pr_pat p)^ " -> "^(aux e)) lst)^" end) \n"
    | Let (lst,t,body) -> 
          let pr (t,v,e) = (pr_type_opt t)^" "^v^" = "^(aux e)
          in "let "^(pr_lst ";" pr lst)^" in "^(pr_type_opt t)^(aux body)^" end"
  in aux e

let string_of_dPL (e:dPL_expr):string = string_of_dPL_gen string_of_dPL_pat e

let string_of_ndPL (e:dPL_nexpr):string = string_of_dPL_gen string_of_dPL_npat e


let string_of_dPL_type_decl (t: dPL_type_decl):string = 
  t.ty_def_name^" "^(pr_list pr_id t.ty_def_param)^" ="^
      (pr_list (fun (i,ts) -> i^" "^(pr_list string_of_dPL_type ts)) t.ty_def_data)

(* let string_of_ndPL (e:dPL_nexpr):string = *)
(*   let pr_type t = "{"^(string_of_dPL_type t)^"}" in *)
(*   let pr_type_opt t = match t with *)
(*     | Some t -> pr_type t *)
(*     | None -> "" *)
(*   in *)
(*   let rec aux e = *)
(*   match e with *)
(*     | Unit-> "()" *)
(*     | BoolConst v -> "Bool("^(string_of_bool v)^")" *)
(*     | IntConst v -> "Int("^(string_of_int v)^")" *)
(*     | Var v -> "Var("^v^")" *)
(*     | UnaryPrimApp (op,arg) -> op^"["^(aux arg)^"]" *)
(*     | BinaryPrimApp (op,arg1,arg2) -> op^"["^(aux arg1)^","^(aux arg2)^"]" *)
(*     | HasType (ex,t) -> "("^(aux ex)^":"^(pr_type t)^")" *)
(*     | TryCatch (e1,id,e2) -> "try "^(aux e1)^" catch "^ id ^" with "^(aux e2)^" end" *)
(*     | Throw e -> "throw("^(aux e)^")" *)
(*     | Cond (e1,e2,e3) -> "if "^(aux e1)^" then "^(aux e2) *)
(*           ^" else "^(aux e3)^" end" *)
(*     | Func (t,args,body) -> "fun "^(pr_type_opt t)^" "^(pr_lst " " pr_id args)^" -> "^(aux body)^" end" *)
(*     | RecFunc (t,r,args,body) -> "recfun "^r^" "^(pr_type_opt t)^" "^(pr_lst " " pr_id args)^" -> "^(aux body)^" end" *)
(*     | Appln (e,t,args) -> "Appln["^(aux e)^ *)
(*           (match t with *)
(*             | Some t -> ":"^(string_of_dPL_type t) *)
(*             | None -> "")^"; "^(pr_lst ";" aux args)^"]" *)
(*     | Constr (i,_,args) -> "("^i^" "^(pr_lst ";" aux args)^")" *)
(*     | Match (e1,lst) -> "\nmatch "^(aux e1)^" with \n" ^ (pr_lst ";\n" *)
(*           (fun (p,e)->  (string_of_dPL_npat p)^ " -> "^(aux e)) lst)^" end \n" *)
(*     | Let (lst,t,body) ->  *)
(*           let pr (t,v,e) = (pr_type_opt t)^" "^v^" = "^(aux e) *)
(*           in "let "^(pr_lst ";" pr lst)^" in "^(pr_type_opt t)^(aux body)^" end" *)
(*   in aux e *)


(* removing vars in ys that occur in xs *)


(* free vars of an expression *)
let rec fv (e:dPL_expr) : id list =
  match e with
    | Unit | BoolConst _  | IntConst _ -> []
    | Var i -> [i]
    | UnaryPrimApp (_,arg) -> fv arg
    | BinaryPrimApp (_,arg1,arg2) -> (fv arg1)@(fv arg2)
    | Cond (e1,e2,e3) -> (fv e1)@(fv e2)@(fv e3)
    | HasType (ex,t) -> (fv ex)
    | Throw ex -> (fv ex)
    | TryCatch (e1,id,e2) -> (fv e1)@(diff (fv e2) (remove_anon [id]))
    | Func (_,vs,body) -> diff (fv body) (remove_anon vs)
    | RecFunc (_,i,vs,body) -> diff (fv body) (remove_anon (i::vs))
    | Appln (e1,_,es) -> (fv e1)@(List.concat (List.map fv es))
    | Constr (_,_,es) -> List.concat (List.map fv es)
    | Match (e1,lst) -> (fv e1)@(List.concat (List.map 
          (fun ((i,_,vs),e)-> diff (fv e) (remove_anon vs)) lst))
    | Let (lst,_,body) -> 
          let bv = List.map (fun (_,i,_)->i) lst in
          let vs = List.concat ((fv body)::(List.map (fun (_,i,e)->fv e) lst)) in
          diff vs bv

