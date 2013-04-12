open DPL

(* module C = DPLc *)

open Debug.Basic


include DPL_unify

let rec insert ans i j p =
  match ans with
    | [] -> [([i;j],[p])]
    | ((vs,ps) as r)::rest ->
          let (i,j,flag) =
            if List.mem i vs then (i,j,true)
            else if List.mem j vs then (j,i,true)
            else (i,j,false) in
          if flag then
            let (p2,rest) = List.partition (fun (vs,_) -> List.mem j vs) rest in
            (match p2 with
              | [] -> (j::vs,p::ps)::rest
              | [(vs2,ps2)] ->(vs@vs2,p::ps@ps2)::rest)
          else r::(insert rest i j p)

let merge_eqs lst =
  List.fold_left (fun ans ((i,TVar j) as p)
    -> insert ans i j p) [] lst

let find_eqs subs =
     List.partition (fun (i,j) -> 
         match j with TVar _ -> true
           | _ -> false) subs

let choose_target vs =
  let aux vs =
    match vs with
      | v::rs -> 
            let u = TVar v in
            let subs = List.map (fun j -> (j,u)) rs in
            subs
      | _ -> failwith "problem with choose_target"

  in aux vs

let choose_target vs =
  Debug.no_1 "choose_target" (pr_list pr_id) pr_subs choose_target vs

let norm_eqs lst =
  let res = merge_eqs lst in
  let res = List.map (fun (vs,ps) ->
      let subs = choose_target vs in
      subs
      (* List.map (fun (i,_) -> (i,TVar target)) ps *)
  ) res in
  List.concat res


let norm_subs s =
  let lst = List.map (fun (i,t)->(TVar i,t)) s in
  Some ((unify lst))

let norm_subs subs = 
  Debug.no_1 "norm_subs" pr_subs (pr_opt pr_subs) norm_subs subs


let unify_option opt t =
  let (subs,t1) = opt in
  let (s,tf) = unify_type t1 t in
  (s@subs,tf)

let unify_option opt t =
  let pr1 = pr_pair pr_subs string_of_dPL_type in
  let pr2 = string_of_dPL_type in
  Debug.no_2 "unify_option" pr1 pr2 pr1 unify_option opt t 


let unify_option_two opt1 opt2 =
  let (s1,t1) = opt1 in
  let (s2,t2) = opt2 in
  let (s,t) = unify_type t1 t2 in
  (s@s1@s2,t)

let tnames = new generator "tv"
let vnames = new generator "var"

let fresh_tv () = 
  let i = tnames # fresh_id
  in TVar i

let create_fn_type args =
  let bt = fresh_tv () in
  (bt, List.fold_right 
      (fun (s1,t1) (s2,t2) -> (s1@s2,Arrow(t1,t2))) args ([],bt))


let create_fn_type args =
  let pr2 = pr_opt (pr_pair pr_subs string_of_dPL_type) in
  let pr = pr_list pr2 in
  let pr3 = pr_pair string_of_dPL_type pr2 in
  Debug.no_1 "create_fn_type" pr pr3 create_fn_type args


let create_fn_type_bare args bt =
  List.fold_right (fun f b -> Arrow (f,b)) args bt


(* this method apply type-substitution to the
   type annotations in expr *)
let apply_type_subs subs (e:dPL_expr) : dPL_expr =
  let apply t = match t with
    | Some t -> Some (apply_subs subs t)
    | None -> None in
  let rec aux e =
    match e with
      | BoolConst _ | IntConst _ | Unit
      | Var _ -> e
      | Throw e -> Throw (aux e)
      | TryCatch (e1,i,e2) -> 
            TryCatch(aux e1,i,aux e2)
      | Constr (id,tag,args) -> Constr (id,tag,List.map aux args)
      | Match (e,lst) -> Match (aux e,List.map (fun ((i,tag,vs),e) -> ((i,tag,vs),aux e)) lst)
      | HasType (e,t) -> HasType (aux e,apply_subs subs t)
      | UnaryPrimApp (op,arg) ->
            let varg = aux arg in
            (UnaryPrimApp (op,varg))
      | BinaryPrimApp (op,arg1,arg2) ->
            let varg1 = aux arg1 in
            let varg2 = aux arg2 in
            (BinaryPrimApp (op,varg1,varg2))
      | Cond (e1,e2,e3) ->
            let v1 = aux e1 in
            let v2 = aux e2 in
            let v3 = aux e3 in
            Cond (v1,v2,v3)
      | Func (t,vs,body) ->
            let nbody = aux body in
            Func (apply t,vs,nbody)
      | RecFunc (t,f,vs,body) ->
            let nbody = aux body in
            RecFunc (apply t,f,vs,nbody)
      | Appln (f,t,args) ->
            begin
              let args = List.map aux args in
              let f = aux f in
              Appln(f,apply t,args)
            end
      | Let (ls,t,body) ->
            let ls = List.map (fun (t,v,e)-> (apply t,v,aux e)) ls in
            Let(ls,apply t,aux body)
  in aux e

type outcome = subst * dPL_type

let remove_anon xs = List.filter (fun (i,_)->not(i="_")) xs

let inst_type t =
  match t with
    | TUniv(vs,t) ->
          let nvs = tnames # fresh_ids (List.length vs) in
          let subs = List.combine vs nvs in
          let subs = List.map (fun (i,j) -> (i,TVar j)) subs in
          apply_subs subs t
    | _ -> t

let inst_type t =
  let pr = string_of_dPL_type in
  Debug.no_1 "inst_type" pr pr inst_type  t 

let well_formed_data_constructor_helper (id0: DPL.id) (lst_len: int) (td: dPL_type_decl) =
  let (pos,param_lst) = ty_dict#find_tag_in_dt id0 td in
  if (lst_len < List.length param_lst) then
    fail_type "insufficient parameters for data constructor"
  else 
    if (lst_len > List.length param_lst) then
      fail_type "data constructor has too many parameters"
    else
      (pos, param_lst)

let well_formed_data_constructor_id_param (id0: DPL.id) (idlst: DPL.id list) (td: dPL_type_decl) =
  let (pos, param_lst) = well_formed_data_constructor_helper id0 (List.length idlst) td in
  let lst = List.combine param_lst idlst in (* param *)
  let env_ls = List.map (fun (t,v)->(v,t)) lst in
  env_ls

let well_formed_data_constructor_id_param_subs (id0: DPL.id) (idlst: DPL.id list) (td: dPL_type_decl) subs =
  let (pos, param_lst) = well_formed_data_constructor_helper id0 (List.length idlst) td in
  let param_lst2 = List.map (apply_subs subs) param_lst in
  let lst = List.combine param_lst2 idlst in (* param *)
  let env_ls = List.map (fun (t,v)->(v,t)) lst in
  (pos, env_ls)

let well_formed_data_constructor_id_param_subs (id0: DPL.id) (idlst: DPL.id list) (td: dPL_type_decl) subs =
  Debug.no_1 "wfdc_subs" pr_subs pr_subs (well_formed_data_constructor_id_param_subs id0 idlst td) subs

let well_formed_data_constructor (id0: DPL.id) args  =
  let (_, td) = try ty_dict#find_tag id0
  with Not_found -> fail_type ("Constructor " ^ id0 ^ " is not defined") in
  (td, well_formed_data_constructor_helper id0 (List.length args) td)
  
let fresh_defn_type td =
  let para =td.ty_def_param in
  let npara = List.map (fun i -> TVar i) (tnames # fresh_ids (List.length para)) in
  let subs = List.combine para npara in
  (TDef(td.ty_def_name, npara),subs)

(* check the list of pattern to see which type
   the patterns belong to*)
let infer_pat_type lst =
  match lst with
    | ((i,_,_),_)::xs ->
          let (_,td) = try ty_dict#find_tag i
          with Not_found -> fail_type ("Constructor " ^ i ^ " is not defined") in
          let same_type = List.fold_left (fun answ ((i0,_,_),_) ->  answ && (ty_dict#is_tag_in_dt i0 td) ) true  xs in
          if same_type then
            let (t,subs) = fresh_defn_type td in
            (t, td, subs)
          else
            fail_type ("Expected type for pattern match clauses is:" ^ td.ty_def_name)
    | []    -> fail_type "pattern match should have at leat one branch"

(* type: 
     (DPL.id * 'a * 'b) list -> 
     DPL.dPL_type * DPL.dPL_type_decl * (DPL.id * DPL.dPL_type) list *)

let infer_pat_type lst =
  let pr1 = pr_list (fun ((i,_,l),_)-> i ^ (pr_list (fun x -> x) l)) in
  let pr2 (t,_,s) = (pr_pair string_of_dPL_type pr_subs) (t,s) in
  Debug.no_1 "infer_pat_type" pr1 pr2 infer_pat_type lst

let simplify_subs s = 
  match norm_subs s with
    | Some s -> s
    | None -> fail_type "problem simplifying subs"


(* Check if a pattern match construction has duplicated patterns, that is check to see if it uses the same 
   constructor twice. If this is not the case, then add all missing patterns, if any.
 *)
let force_exact_match expr td =
  match expr with 
    | Match(e, lst) ->
          let patterns = List.map (fun  ((_, tag, _), _)  -> tag) lst in
          let patterns = List.sort (fun x y -> (x - y)) patterns in
          let duplicates = List.exists (fun (x,y) ->  x==y ) (List.combine (0::patterns) (patterns@[0])) in
          if (duplicates) then fail_type "duplicated pattern in match not allowed"
          else
            let zero_2_n = Array.init (List.length td.ty_def_data) (fun i -> i + 1) in
            let missing_tags = List.filter (fun x -> not(List.exists (fun y -> x == y) patterns )) (Array.to_list zero_2_n) in
            let missing_patterns = List.map (fun i -> 
                let (id, typ_lst) = List.nth td.ty_def_data (i-1) in
                let new_branch = ((id, i, List.map (fun t -> vnames # fresh_id) typ_lst), (Throw invalid_pattern_matching)) in
                new_branch
            ) missing_tags in
            Match(e, lst@missing_patterns)
    | _ -> fail_type "[dPL_type.ml: force_exact_match] Should never reach here. Only pattern match expressions allowed here" 
 
(* type inference, note that exception is raised *)
(*    if no suitable type is inferred *)
let type_infer (env:env_type) (e:dPL_expr) : outcome * dPL_expr =
  let rec infer env e =
    let infer_and_unify env exp ty =
      let ((si,t),ne) = infer env exp in
      let (su,t) = unify_type t ty in
      ((su@si,t) ,ne) in
    match e with
      | Unit -> ( ([],Void),e)
      | IntConst _ -> ( ([],IntType),e)
      | BoolConst _ -> ( ([],BoolType),e)
      | Var v -> 
            (match get_type env v with 
              | Some t -> 
                    let t1 = inst_type t in
                    Debug.ninfo_pprint ("*** Var "^v);
                    Debug.ninfo_hprint (add_str "t" pr_type) t;
                    Debug.ninfo_hprint (add_str "t1" pr_type) t1;
                    (([],t1),e)
              | _ -> fail_type ((string_of_dPL e) ^ " has no type assigned" ))
      | UnaryPrimApp (op,arg) ->
            begin
              match op with
                | "~" ->
                      let (at2,na2) = infer env arg in
                      (unify_option at2 IntType,UnaryPrimApp (op,na2))
                | "\\" ->
                      let (at2,na2) = infer env arg in
                      (unify_option at2 BoolType,UnaryPrimApp (op,na2))
                | _ -> fail_type "unknown operator"
            end
      | BinaryPrimApp (op,arg1,arg2) ->
            begin
              match op with
                | "-" | "+" | "*" | "/"  ->
                      let (at1,na1) = infer env arg1 in
                      let (at2,na2) = infer env arg2 in
                      let (s1,_ ) = unify_option at1 IntType in
                      let (s2,_ ) = unify_option at2 IntType in
                      ((s1@s2,IntType),BinaryPrimApp (op,na1,na2))
                | "<" | ">" | "=" ->
                      let (at1,na1) = infer env arg1 in
                      let (at2,na2) = infer env arg2 in
                      let (s1,_ ) = unify_option at1 IntType in
                      let (s2,_ ) = unify_option at2 IntType in
                      ((s1@s2,BoolType),BinaryPrimApp (op,na1,na2))
                | "&" | "|" ->
                      let (at1,na1) = infer env arg1 in
                      let (at2,na2) = infer env arg2 in
                      let (s1,_ ) = unify_option at1 BoolType in
                      let (s2,_ ) = unify_option at2 BoolType in
                      ((s1@s2,BoolType),BinaryPrimApp (op,na1,na2))
                | _ -> fail_type "unknown operaor"
            end
      | Throw e ->
            let (t,ne) = infer env e in
            (* Hint : use unify_option and TError *)
            let (s1,res) = unify_option t TError in
	    ((s1,TError), Throw ne)
      | TryCatch (e1,v,e2) ->
            let env2 = (remove_anon [(v,IntType)])@env in
            let (t1,ne1) = infer env e1 in
            let (t2,ne2) = infer env2 e2 in
	    let (_, et1) = t1
	    and (_, et2) = t2 in
	    if et1 = TError then
		(([], et2), TryCatch(ne1,v,ne2))
	    else
		(([], et1), TryCatch(ne1,v,ne2))
      | Cond (e1,e2,e3) ->
            let (t1,ne1) = infer env e1 in
            let (t2,ne2) = infer env e2 in
            let (t3,ne3) = infer env e3 in
	    let (s1,_) = unify_option t1 BoolType in
	    let (s2,tp2) = unify_option t2 (fresh_tv()) in
	    let (s3,tp3) = unify_option t3 (fresh_tv()) in
	    if tp2 = tp3 then
		((s1@s2@s3,tp2), Cond(ne1,ne2,ne3))
	    else
		failwith "Could not be unified"
      | Match (em, lst) -> 
            (* first infer type for matching expression *)
            let (ans,nem) = infer env em in
            let (pt,td,subs) = infer_pat_type lst in
            if ((List.length lst) > (List.length td.ty_def_data)) then fail_type ("Only exact pattern match allowed")
            else
              begin
                Debug.tinfo_pprint "*** Match ";
                Debug.tinfo_hprint (Environ.string_of string_of_dPL_type_decl) ty_dict#get_env; 
                Debug.tinfo_hprint (add_str "em" string_of_dPL) em;
                Debug.tinfo_hprint (add_str "ans" (pr_pair pr_subs string_of_dPL_type)) ans;
                Debug.tinfo_hprint (add_str "pt" string_of_dPL_type) pt;
                let (sm,tym) = unify_option ans pt in 
                let (s,expr) = match lst with 
                  | [] -> fail_type ("Pattern match should have at least one branch")
                  | ((i,_,ilst),ex)::xs -> 
                        (* get alg data type name for the first pattern, and the types of constructor parameters  *)
                        let  (tag_no, env_ls) =  well_formed_data_constructor_id_param_subs i ilst td subs in
                        let (t1,e1) = infer (env_ls@env) ex in (* add to env parameter type info of pattern *)
                        (* infer result type for all other branches *)
                        let cases_xs = List.map (fun ((i0, _, ilst0), e0) ->
                            let  (pos, env_ls0) = well_formed_data_constructor_id_param_subs i0 ilst0 td subs in
                            (pos, infer (env_ls0@env) e0) ) xs in
                        (* positions list * ((alg data type name) list * (infer result) list )*)
                        let (tags, cases_xs) = List.split cases_xs in
                        (* (alg data type name) list * (infer result) list *)
                        let (out_xs, ne_xs) = List.split cases_xs in
                        let (sb, tp) = List.fold_left (fun t1 t2 -> unify_option_two t1 t2 ) t1 out_xs in
                        let n_lst = List.combine lst (e1::ne_xs) in
                        let n_lst = List.combine n_lst (tag_no::tags) in
                        let nlst  = List.map (fun ((((i,_, ilst), _), nex), tag) -> ((i,tag,ilst),nex)) n_lst in
                        let nsubs = sm@sb in
                        Debug.ninfo_pprint "*** Match 2 ";
                        Debug.ninfo_hprint (add_str "nsubs" pr_subs) nsubs;
                        Debug.ninfo_hprint (add_str "tp" pr_type) tp;
                        ((sm@sb,tp), Match(nem,nlst)) 
                in
                let expr = force_exact_match expr td in
                (s, expr)
              end
      | Constr (i,tag,args) ->
            let (td, (position, arg_types)) =  well_formed_data_constructor i args in
            Debug.ninfo_pprint "*** Constr";
            Debug.ninfo_hprint (add_str "i" (pr_id)) i;
            Debug.ninfo_hprint (add_str "arg_types" (pr_list string_of_dPL_type)) arg_types;
            Debug.ninfo_hprint (add_str "td formal" (pr_list pr_id)) td.ty_def_param;
            let (new_type,subs) = fresh_defn_type td in
            let narg_types = List.map (apply_subs subs) arg_types in
            Debug.ninfo_hprint (add_str "narg_types" (pr_list string_of_dPL_type)) narg_types;
            let lst = List.combine args narg_types in  
            let (s,t,nelst,_) = List.fold_left (fun (s0,t0,nelst,env) (arg_e,arg_t) -> 
                let ((s,nt),ne) = infer_and_unify env arg_e arg_t in ( s@s0,t0@[nt], (nelst@[ne]), env) ) 
              ([],[], [], env) lst in 
            Debug.ninfo_hprint (add_str "s" (pr_subs)) s;
            ((s,new_type), Constr(i,position,nelst))
      | HasType (e,t) ->
            infer_and_unify env e t 
      | Appln (e1,_,args) ->
	  begin
              let (nt1,ne1) = infer env e1 in
              let ans = List.map (infer env) args in
              let (subs_lst,args_lst) = List.split ans in
              let (bt,(s,ft)) = create_fn_type subs_lst in
              (* Hint : use unify_option and apply_subs *)
              let (unify_subs, unify_result) = unify_option nt1 ft in
              let s3 = s@unify_subs in
              let new_body_type = apply_subs s3 bt in
              ((s3,new_body_type), Appln (ne1, Some unify_result, args_lst))
	  end
      (* begin *)
      (* let (nt1,ne1) = infer env e1 in *)
      (* let ans = List.map (infer env) args in *)
      (* let (types_lst,args_lst) = List.split ans in *)
      (* let (bt,(s,arg_tp_lst)) = create_fn_type types_lst in *)
      (* let (s1, _) = unify_option nt1 bt in *)
      (* let at = List.map (fun (_,t) -> apply_subs s t) types_lst in *)
      (* ((s1, bt), Appln (ne1, Some arg_tp_lst, args_lst)) *)
      (* Hint : use unify_option and apply_subs *)
      (* failwith "TO BE IMPLEMENTED" *)
      (* end *)
      | Let (lst,_,body) ->
            begin
              (* tlst :(DPL.id * (((DPL.id * DPL.dPL_type) list * DPL.dPL_type) * DPL.dPL_expr)) list *)
              let tlst = List.map (fun (ot,v,e) -> (v,infer env e)) lst in
              (* need to generalise the inferred type of tlst *)
              let fv_env = List.concat (List.map (fun (_,t)-> fvt t) env) in
              let pr (i,((s,t),e)) = i^(pr_subs s)^(pr_type t) in  
              Debug.ninfo_hprint (add_str "tlst" (pr_list pr)) tlst;
              (* (pr_lst (fun (i,((s,t),e)) -> (i^(pr_subs s)^(pr_type t))))) tlst; *)
              (* Debug.ninfo_hprint (Environ.string_of string_of_dPL_type) env; *)
              let (s2,nlst) = List.fold_right 
                (fun (v,((s1,t1),e1)) (s2,ls) -> 
                    let gen_ty vs t = if vs=[] then t else TUniv(vs,t) in
                    let subs = s1@s2 in
                    let nsubs = simplify_subs subs in
                    let t1 = apply_subs nsubs t1 in
                    let fv = diff (fvt t1) fv_env in
                    let t1g = gen_ty fv t1 in
                    Debug.ninfo_pprint "*** LET bound";
                    Debug.ninfo_hprint (add_str "subs-s1" pr_subs) s1;
                    Debug.ninfo_hprint (add_str "subs-s2
" pr_subs) s2;
                    Debug.ninfo_hprint (add_str "nsubs" pr_subs) nsubs;
                    Debug.ninfo_hprint (add_str "t1" string_of_dPL_type) t1;
                    Debug.ninfo_hprint (add_str "fv" (pr_list pr_id)) fv;
                    Debug.ninfo_hprint (add_str "gen" string_of_dPL_type) t1g;
                    (subs,(Some t1g,v,e1)::ls)) tlst ( ([],[])) in
              let env_ls = List.map (fun (Some t,v,_)->(v,t)) nlst in
              let ((s,bt),nbody) = infer (env_ls@env) body in
              ((s@s2,bt),Let(nlst,Some bt,nbody))
            end
      | Func (te,args,body) ->
            let env_ls = List.map (fun v -> (v,fresh_tv())) args in
            let ((s,bt),nbody) = infer (env_ls@env) body in
            (* let s = norm_subs s in *)
            let at = List.map (fun (_,t) -> apply_subs s t) env_ls in
            let nft = create_fn_type_bare at bt in
            ((s,nft),Func(Some nft,args,nbody))
      | RecFunc (te,id,args,body) -> 
            (* Hint : similar to Func but remember to give a type to
               function body and associate it with recursive id *)
	  let env_ls = List.map (fun v -> (v, fresh_tv())) args in
	  let id_t = fresh_tv() in
	  let ((s,bt), nbody) = infer ((id, id_t)::env_ls@env) body in
		  (* let (s1, rslt) = unify_option id_t te in *)
	  let at = List.map (fun (_,t) -> apply_subs s t) ((id, bt)::env_ls) in
	  let nft = create_fn_type_bare at bt in
	  ((s,nft), RecFunc(te, id, args, nbody))
  in 
  let ((subs,t),e) = infer env e in
  match norm_subs subs with
    | Some s -> ((s,apply_subs s t),apply_type_subs s e)
    | _ -> fail_type " type check fails" 

let type_infer (env:env_type) (e:dPL_expr) : outcome * dPL_expr =
    let pr = string_of_dPL in
    let pr_out = pr_pair (pr_pair pr_subs string_of_dPL_type) pr in
    Debug.no_2 "type_infer" (Environ.string_of string_of_dPL_type) pr pr_out type_infer env e

(* type inference, note that None is returned  *)
(*    if no suitable type is inferred *)


(* number of arguments for full application *)
(* Ex: num_of_arg (int->(int->int)->int) ==> 2 *)
let rec num_of_arg rt =
  match rt with
    | Arrow (_,t2) -> 1+(num_of_arg t2)
    | _ -> 0

(* determine if sufficient argument for type *)
(* if insufficient - return fresh id and residual type *)
(* get_partial int->int->int [2] ===> Some (["_tmp_1"],int->int *)
(* get_partial int->int->int [] ===> Some (["_tmp_1";"_tmp_2"],int->int->int *)
let get_partial (t:dPL_type) (args:'b list) =
  if not(!pa_removal_flag) then None
  else
    match extr_arg_type t args with
      | None -> None
      | Some (ls,rt) -> 
            let narg = num_of_arg rt in
            if narg=0 then None
            else Some (rt,(names # fresh_strs "_pa_var" narg))


let rec build_type ls bt =
  match ls with
    | [] -> bt
    | (Some t,_,_)::ls -> Arrow(t,build_type ls bt)

(* 
   preprocessing to remove 
    (i) partial application 
    (ii) let construct
    (iii) sort the branches in pattern match according to the pattern constructor definition

   S.dPL_expr --> C.dPL_expr
*)
let trans_exp (e:dPL_expr) : C.dPL_expr  =
  let rec aux e =
    match e with
      | Unit -> C.Unit
      | BoolConst v -> C.BoolConst v
      | IntConst v -> C.IntConst v
      | Var v -> C.Var v
      | HasType (e,_) -> aux e
      | Throw e -> C.Throw (aux e)
      | Constr (i,tag,es) -> C.Constr (i,tag,List.map aux es)
      | UnaryPrimApp (op,arg) ->
            let varg = aux arg in
            (C.UnaryPrimApp (op,varg))
      | BinaryPrimApp (op,arg1,arg2) ->
            let varg1 = aux arg1 in
            let varg2 = aux arg2 in
            (C.BinaryPrimApp (op,varg1,varg2))
      | Cond (e1,e2,e3) ->
            let v1 = aux e1 in
            let v2 = aux e2 in
            let v3 = aux e3 in
            C.Cond (v1,v2,v3)
      | Match(e1, lst) ->
            let ne1 = aux e1 in
            (* order the branches according to their tag_no (index in type def) *)
            let lst = List.sort (fun ((_,tag1,_),_) ((_,tag2,_),_) ->  (tag1 - tag2)) lst in 
            let nlst =  List.map (fun ((i,tag,ilst),ex) -> (i, ilst, aux ex)) lst in
            C.Match (ne1, nlst)
      | Func (Some t,vs,body) ->
            let nbody = aux body in
            C.Func (t,vs,nbody)
      | RecFunc (Some t,f,vs,body) ->
            let nbody = aux body in
            C.RecFunc (t,f,vs,nbody)
      | TryCatch(e1,v,e2) ->
            let ne1 = aux e1 in
            let ne2 = aux e2 in
            C.TryCatch(ne1,v,ne2)
      | Appln (f,t,args) ->
            begin
              match t with
                | Some t1 ->
                      begin
                        let args = List.map aux args in
                        let f = aux f in
                        match get_partial t1 args with
                          | None ->  C.Appln (f,t1,args)
                          | Some (t2,ns) -> C.Func(t2,ns,C.Appln(f,t1,args@(List.map (fun v -> C.Var v) ns)))
                      end
                | _ -> failwith "missing type : not possible"
            end
      | Let (ls,Some t,body) ->
            let vs = List.map (fun (t,v,e)-> v) ls in
            let args = List.map (fun (t,v,e)-> aux e) ls in
            let nbody = aux body in
            let nft = build_type ls t in
            C.Appln (C.Func(nft,vs,nbody),nft,args)
      | _ -> failwith "error in trans_exp"
  in aux e
(* let source_files = ref [] *)



