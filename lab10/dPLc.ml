(* PLEASE DO NOT CHANGE THIS FILE *)

module S = DPL

type op_id = S.op_id
type id = S.id
type dPL_type = S.dPL_type

open Debug.Basic

(* AST for core language *)
type dPL_expr =
  | Unit 
  | BoolConst of bool
  | IntConst of int
  | Var of id
  | UnaryPrimApp of op_id * dPL_expr
  | BinaryPrimApp of op_id * dPL_expr * dPL_expr
  | Throw of dPL_expr
  | TryCatch of dPL_expr * id * dPL_expr
  | Constr of id * int * dPL_expr list
        (* only exact application allowed *)
  | Match of dPL_expr * (id * (id list) * dPL_expr) list
        (* should have full set of patterns, and sorted by constructor id *)
  | Cond of dPL_expr * dPL_expr * dPL_expr
  | Func of dPL_type * (id list) * dPL_expr 
        (* min of one parameter *)
  | RecFunc of dPL_type * id * (id list) * dPL_expr 
        (* min of one parameter *)
  | Appln of dPL_expr * dPL_type * (dPL_expr list) 
        (* all applications fully applied *)

(* display dPL expr in prefix form *)
(* PLEASE do not change *)
let string_of_dPL (e:dPL_expr):string =
  let pr_type t = "{"^(S.string_of_dPL_type t)^"}" in
  let rec aux e =
  match e with
    | Unit -> "()"
    | BoolConst v -> "Bool("^(string_of_bool v)^")"
    | IntConst v -> "Int("^(string_of_int v)^")"
    | Var v -> "Var("^v^")"
    | Throw e -> "throw("^(aux e)^")"
    | Constr (i,tag,args) -> "("^i^(pr_lst " " aux args)^")"
    | Match (e1,lst) -> "\nmatch "^(aux e1)^" with\n"^(pr_lst ";\n"
          (fun (i, ilst, e)-> i ^ " " ^(pr_lst " " pr_id ilst)^"->"^(aux e)) lst)^" end\n"
    | UnaryPrimApp (op,arg) -> op^"["^(aux arg)^"]"
    | BinaryPrimApp (op,arg1,arg2) -> op^"["^(aux arg1)^","^(aux arg2)^"]"
    | Cond (e1,e2,e3) -> "if "^(aux e1)^" then "^(aux e2)^" else "^(aux e3)
    | TryCatch (e1,id,e2) -> "\ntry "^(aux e1)^" \ncatch "^id^" -> "^(aux e2)^" end"
    | Func (t,args,body) -> "fun "^(pr_type t)^" "^(pr_lst " " pr_id args)^" -> "^(aux body)^" end"
    | RecFunc (t,r,args,body) -> "recfun "^r^" "^(pr_type t)^" "^(pr_lst " " pr_id args)^" -> "^(aux body)^" end"
    | Appln (e,t,args) -> "Appln["^(aux e)^"; "^(pr_lst ";" aux args)^"]"
  in aux e


(* free vars of an expression *)
let rec fv (e:dPL_expr) : id list =
  match e with
    | Unit | BoolConst _  | IntConst _ -> []
    | Var i -> [i]
    | UnaryPrimApp (_,arg) -> fv arg
    | BinaryPrimApp (_,arg1,arg2) -> (fv arg1)@(fv arg2)
    | Cond (e1,e2,e3) -> (fv e1)@(fv e2)@(fv e3)
    | Constr (i,_,es) -> List.concat (List.map fv es)
    | Throw ex -> (fv ex)
    | TryCatch (e1,id,e2) -> (fv e1)@(diff (fv e2) (remove_anon [id]))
    | Match (e1,lst) -> (fv e1)@(List.concat (List.map (fun (_,ilst,e)->diff (fv e) (remove_anon ilst)) lst))
    | Func (_,vs,body) -> diff (fv body) (remove_anon vs)
    | RecFunc (_,i,vs,body) -> diff (fv body) (remove_anon (i::vs))
    | Appln (e1,_,es) -> (fv e1)@(List.concat (List.map fv es))


