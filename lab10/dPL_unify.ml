open DPL

module C = DPLc

open Debug.Basic

exception Type_error of string

let fail_type s = raise (Type_error s)

type env_type = dPL_type Environ.et
let tail_optimize_flag = ref false
let pa_removal_flag = ref true
let stack_size = ref 10000

let option_flag = [
  ("--tail", Arg.Set tail_optimize_flag, "Enable tail-call optimization.")
  ;("--dis-pa", Arg.Clear pa_removal_flag, "Disable partial application Removal.")
  ;("-stk-size", Arg.Set_int stack_size,
    "Size of Stack Memory (default is 10000)")

]


(* if (v,r) in env, return Some r *)
(* otherwise, return None *)
let get_type env v = Environ.get_val env v


let pr_subs = pr_list (pr_pair pr_id string_of_dPL_type)
let pr_type = string_of_dPL_type
let pr_expr = string_of_dPL


(* match a function type t with its parameters args *)
(* and return its residual *)
(* extr_arg_type (t1->t2->t3->t4) [e1,e2] 
   ==> Some ([(e1,t1);(e2,t2)], t3->t4) *)
(* match a function type t with its parameters args *)
(* and return its residual *)
(* extr_arg_type (t1->t2->t3->t4) [e1,e2] ==> Some ([(e1,t1);(e2,t2)], t3->t4) *)
(* use test harness below and run ./splt *)
let extr_arg_type (t:dPL_type) (args:'a list) : (('a * dPL_type) list * dPL_type) option =
  let rec aux env t args =
    match args,t with
      | [],_ -> Some (List.rev env,t)
      | v::vs,Arrow (t1,t2) -> aux ((v,t1)::env) t2 vs
      | _,_ -> None
  in aux [] t args

let extr_arg_type_test (t:dPL_type) (args:int list) : ((int * dPL_type) list * dPL_type) option =
  let pr1 = string_of_dPL_type in
  let pr2 = pr_list string_of_int in
  let pr2a = pr_list (pr_pair string_of_int pr1) in
  let pr3 = pr_option (pr_pair pr2a pr1) in
  Debug.no_2 "extr_arg_type_test" pr1 pr2 pr3 extr_arg_type t args

(* test harness below to debug extr_arg_type *)
(* please comment them after fixing bug *)
(* let t1 = Arrow (IntType,Arrow (IntType,IntType)) *)
(* let _ = extr_arg_type_test t1 [1] *)
(* let _ = extr_arg_type_test t1 [1;2] *)
(* let _ = extr_arg_type_test t1 [1;2;3] *)

type subst = (id * dPL_type) list

type type_outcome = subst option

let rec apply_one id tt te = 
  match te with 
    | BoolType | IntType | Void | TError -> te
    | TVar i -> 
          if i=id then tt
          else te
    | Arrow (t1,t2) -> Arrow (apply_one id tt t1,apply_one id tt t2)
    | TDef (i,ts) -> TDef (i,List.map (apply_one id tt) ts)
    | TUniv (vs,t) -> 
          (* e may be bound to vs *)
          if List.mem id vs then te
          else TUniv (vs,apply_one id tt t)

let apply_id subs id =
  try
    snd(List.find (fun (v,_)->v=id) subs)
  with _ -> TVar id

let rec apply_subs subs te = 
  match te with 
    | BoolType | IntType | Void | TError -> te
    | TVar _ -> List.fold_left (fun e (i,t) -> apply_one i t e) te subs
    | Arrow (t1,t2) -> Arrow (apply_subs subs t1,apply_subs subs t2)
    | TDef (id,ts) -> TDef (id,List.map (apply_subs subs) ts)
    | TUniv (vs,t) -> 
          (* e may be bound to vs *)
          let nsubs = List.filter (fun (v,e) -> not(List.mem v vs)) subs in
          TUniv (vs,apply_subs nsubs t)

let apply_subs subs te = 
  let pr2 = string_of_dPL_type in
  let pr = pr_subs in
  Debug.no_2 "apply_subs" pr pr2 pr2 apply_subs subs te 


    (* equality of two types *)
let rec eq_type t1 t2 =
  match t1,t2 with
    | Arrow (b1,b2),Arrow (c1,c2) -> 
          (eq_type  b1 c1) && eq_type b2 c2
    | TDef(i,gs),TDef(j,ks) ->
          (try
            (i=j) && (List.for_all (fun (a,b)->eq_type a b) (List.combine gs ks))
          with _ -> false)
    | TUniv(vs1,e1),TUniv(vs2,e2) ->
          begin
            try
              let s = List.combine vs1 vs2 in
              let s = List.map (fun (i,j)->(i,TVar j)) s in
              eq_type (apply_subs s e1) e2
            with _ -> false
          end
    | _,_ ->  t1=t2

let occurs x t
      = List.mem x (fvt t)

    (* unifying two types *)
let unify_aux (t1:dPL_type) (t2:dPL_type) 
      : (id * dPL_type) list * (dPL_type * dPL_type) list  =
  match t1,t2 with
    | BoolType,BoolType
    | IntType,IntType
    | Void,Void ->  ([],[])
    | Arrow (b1,b2),Arrow (c1,c2) -> 
       ([],[(b1,c1);(b2,c2)])
    | TUniv(vs1,e1),TUniv(vs2,e2) ->
          if eq_type t1 t2 then ([],[])
          else fail_type "could not unify two universal types"
    | TDef(i,gs),TDef(j,ks) ->
          begin
            try
              if i=j then
                ([],(List.combine gs ks))
              else fail_type "unify_type : mismatched TDef ids"
            with _ -> fail_type "unify_type : mismatched TDef arguments"
          end
    | TError, t ->  ([],[])
    | t, TError ->  ([],[])
    | TVar i,TVar j ->
          let r = String.compare i j in
          if r=0 then ([],[])
          else if r<0 then ([(i,t2)],[])
          else ([(j,t1)],[])
    | TVar i, t | t,TVar i ->
          if occurs i t
          then fail_type "unify_type : occurs check"
          else ([(i,t)],[])
    | _,_ ->  fail_type ((string_of_dPL_type t1) ^ " and " ^ (string_of_dPL_type t2) ^" can not be unified")


let pick_pair s = s

let rec unify s =
  match pick_pair s with
    | [] -> []
    | (t1,t2)::rest ->
          let (s,more)=unify_aux t1 t2 in
          let s2 = (unify (List.map (fun (p1,p2) -> apply_subs s p1,apply_subs s p2) (more@rest))) in
          (s@s2)

let unify_one p1 p2 = unify [(p1,p2)] 

(* this select most general unified type from t1,t2 *)
let rec mgt t1 t2 = 
  match t1,t2 with
    | TError, t ->  t
    | t, TError ->  t
    | Arrow (b1,b2),Arrow (c1,c2) -> 
          Arrow (mgt c1 b1,mgt b2 c2)
    | TDef(i,gs),TDef(_,ks) ->
          TDef (i,List.map (fun (a,b)->mgt a b) (List.combine gs ks))
    | _,t2 -> t2

let unify_type t1 t2 =
  let s = unify_one t1 t2 in
  (s, mgt (apply_subs s t1) (apply_subs s t2))

let unify_type t1 t2 = 
  let pr = string_of_dPL_type in
  let pr_subs = pr_list (pr_pair pr_id pr) in
  Debug.no_2 "unify_type" pr pr (pr_pair pr_subs pr) unify_type t1 t2

let unify_test t1 t2 =
  try
    Some (unify_type t1 t2)
  with _ -> None

(* let t0a = Arrow(TVar"a",IntType) *)
(* let t0b = Arrow(BoolType,TVar"a") *)
(* let t0c = Arrow(BoolType,TVar"b") *)
(* let t1 = TUniv (["a"],TVar"a") *)
(* let t2 = TUniv (["a"],Arrow(TVar"a",IntType)) *)
(* let t3 = TUniv (["b"],Arrow(TVar"b",IntType)) *)
(* let _ = unify_test t3 t2 *)
(* let _ = unify_test t1 t2 *)
(* let _ = unify_test IntType BoolType *)
(* let _ = unify_test IntType t3 *)
(* let _ = unify_test t0a t0b *)
(* let _ = unify_test t0a t0c *)

(* let t4a = Arrow(TVar"a",Arrow(TVar "b",TVar "c")) *)
(* let t4b = Arrow(TVar"a",Arrow(TDef ("list",[TVar "d"]),TVar "e")) *)
(* let _ = unify_test t4a t4b *)
(* let t4c = Arrow(TVar"a",Arrow(TDef ("list",[TVar "d"]),TVar "d")) *)
(* let _ = unify_test TError  (TVar "a") *)
(* let _ = unify_test IntType TError *)
(* let _ = unify_test t4a t4c *)
(* let _ = unify_test (TVar "a") (Arrow ((TVar "c"),IntType)) *)
(* let _ = unify_test (Arrow ((TVar "c"),IntType)) (TVar "a") *)
(* let _ = unify_test (Arrow ((TVar "a"),IntType)) (TVar "a") *)
(* let _ = unify_test (TDef ("list",[TVar "d"]))  (TDef ("list",[IntType])) *)
(* let _ = unify_test (TDef ("list",[TVar "d"]))  (TDef ("list",[TError])) *)
(* let _ = unify_test (TDef ("list",[IntType]))  (TDef ("list",[TError])) *)
(* let _ = unify_test (TDef ("list",[TError])) (TDef ("list",[IntType])) *)
(* let _ = unify_test (TVar "a") (TVar "b") *)
(* let _ = unify_test (TVar "b") (TVar "a") *)
(* let _ = unify_test (TVar "b") (TVar "b") *)








