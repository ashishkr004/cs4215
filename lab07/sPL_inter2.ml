open SPL_type
open Debug.Basic
open SPL_inter
open SPLc
module S = SPL


type sPL_value =
  | BOT (* denotes an error *)
  | VInt of int 
  | VBool of bool
  | CLS of ((sPL_value ref) Environ.et) * (id list) * sPL_expr 

let string_of_sPL_value (e:sPL_value):string =
  match e with
    | BOT -> "BOT"
    | VBool v -> "Bool("^(string_of_bool v)^")"
    | VInt v -> "Int("^(string_of_int v)^")"
    | CLS (_,args,body) -> "closure "^(pr_lst " " pr_id args)^" -> "^(string_of_sPL body)^" end"

(* ref type used here to build circular closure for
   recursive methods *)
type env_val = (sPL_value ref) Environ.et

let string_of_unary op arg =
  "("^op^" "^(string_of_sPL_value arg)^")"

let string_of_binary op arg1 arg2 = 
  "("^op^" "^(string_of_sPL_value arg1)^" "^(string_of_sPL_value arg2)^")"

let contract_unary op arg : sPL_value =
  if arg==BOT then arg
  else
    match op with
      | "~" ->
            begin
              match arg with
                | VInt v -> VInt (-v)
                | _ -> failwith ("unable to contract for "^(string_of_unary op arg))
            end
      | "\\" ->
            begin
              match arg with
                | VBool v -> VBool (not v)
                | _ -> failwith ("unable to contract for "^(string_of_unary op arg))
            end
      | _ -> failwith ("illegal unary op "^op)

let contract_binary op arg1 arg2 : sPL_value = 
    (* assumes fully-applied application *)
    (* you may use pair_fn_args *)
    (* evaluate f to a closure to evaluate under its
       environment *)
    if arg1==BOT || arg2==BOT then BOT
    else
        match op with
          | "+" ->
              begin
                  match arg1,arg2 with
                    | VInt v1,VInt v2 -> VInt (v1+v2)
                    | _,_ -> failwith ("unable to contract "^(string_of_binary op arg1 arg2))
              end
          | "-" ->
              begin
                  match arg1,arg2 with
                    | VInt v1,VInt v2 -> VInt (v1-v2)
                    | _,_ -> failwith ("unable to contract"^(string_of_binary op arg1 arg2))
              end
          | "*" ->
              begin
                  match arg1,arg2 with
                    | VInt v1,VInt v2 -> VInt (v1*v2)
                    | _,_ -> failwith ("unable to contract"^(string_of_binary op arg1 arg2))
              end
          | "/" ->
              begin
                  match arg1,arg2 with
                    | VInt v1,VInt v2 -> VInt (v1/v2)
                    | _,_ -> failwith ("unable to contract"^(string_of_binary op arg1 arg2))
              end
          | "|" ->
              begin
                  match arg1,arg2 with
                    | VBool v1,VBool v2 -> VBool (v1||v2)
                    | _,_ -> failwith ("unable to contract"^(string_of_binary op arg1 arg2))
              end
          | "&" ->
              begin
                  match arg1,arg2 with
                    | VBool v1,VBool v2 -> VBool (v1&v2)
                    | _,_ -> failwith ("unable to contract"^(string_of_binary op arg1 arg2))
              end
          | "<" ->
              begin
                  match arg1,arg2 with
                    | VInt v1,VInt v2 -> VBool (v1<v2)
                    | _,_ -> failwith ("unable to contract"^(string_of_binary op arg1 arg2))
              end
          | ">" ->
              begin
                  match arg1,arg2 with
                    | VInt v1,VInt v2 -> VBool (v1>v2)
                    | _,_ -> failwith ("unable to contract"^(string_of_binary op arg1 arg2))
              end
          | "=" ->
              begin
                  match arg1,arg2 with
                    | VInt v1,VInt v2 -> VBool (v1=v2)
                    | _,_ -> failwith ("unable to contract"^(string_of_binary op arg1 arg2))
              end
          | _ -> failwith ("illegal binary op "^op)
          
let rec eval_apply (nf:sPL_value) (args: sPL_value list) : sPL_value=
  match nf with
    | CLS(tenv,vs,body) ->
          let (subs,remain) = pair_fn_args vs args in
          let nenv = Environ.extend_env tenv (List.map (fun (i,v)->(i,ref v)) subs) in
          let ans = (evaluate nenv body) in
          if remain==[] then ans
          else eval_apply ans remain
    | _ -> failwith ("WARNING : not a function value for Appln!")

(* interpreter with environment and closure *)
and evaluate (env:env_val) (e:sPL_expr): sPL_value = 
    match e with
      | BoolConst v -> VBool v
      | IntConst v -> VInt v
      | UnaryPrimApp (op,arg) ->
          let varg = evaluate env arg in
          contract_unary op varg
      | BinaryPrimApp (op,arg1,arg2) ->
          let varg1 = evaluate env arg1 in
          let varg2 = evaluate env arg2 in
          contract_binary op varg1 varg2
      | Var v -> 
          (* fetch corresponding variable from env *)
          (* take note of the ref type *)
          begin
              match Environ.get_val env v with
                | Some res -> !res
                | _ -> failwith ("tried to evaluate invalid var: "^v)
          end
      | Func (t,vs,body) -> 
          (* build a closure for this function *)
          begin
              let globals = List.filter (fun v -> List.for_all (fun i -> v <> i) vs) (fv body)
              in
              let fn_args = Environ.build_env env globals
              in let clean_env = List.filter (fun (i, _) -> List.exists (fun (v, _) -> v = i) fn_args) env
              in CLS (clean_env, vs, body)
          end
      | RecFunc (t,i,vs,body) -> 
          (* build a circular closure for this function *)
          begin
              let globals = List.filter (fun v -> List.for_all (fun i -> v <> i) (i::vs)) (fv body)
              in let fn_args = Environ.build_env env globals
                 in let clean_env = List.filter (fun (i, _) -> List.exists (fun (v,_) -> v = i) fn_args) env
                    in let circular = Environ.extend_env clean_env [(i, ref (evaluate env e))]
              in CLS (circular, vs, body)
          end
      | Cond(e1,e2,e3) ->
          begin
              match evaluate env e1 with
                | VBool b ->
                    if b then evaluate env e2
                    else evaluate env e3
                | _ -> 
                    failwith ("WARNING : not a bool value for Cond!")
          end
      | Appln (f,t,args) ->
          (* assumes fully-applied application *)
          (* you may use pair_fn_args *)
          (* evaluate f to a closure to evaluate under its environment *)
          begin
              let evaled_args = List.map (evaluate env) args
              and                       (* eval_apply (CLS) *)
                      eval_f = evaluate env f
              in
              eval_apply eval_f evaled_args
              (* failwith "to implement" *)
          end

let evaluate env e = evaluate env (e)
let usage = "usage: " ^ Sys.argv.(0) ^ " [options] <filename>"

(* calling sPL parser *)
let parse_file (filename:string) : (string * S.sPL_expr) =
  SPL_parser.parse_file filename

(* main program *)
let main =
  (* Read the arguments of command *)
  Arg.parse [] (fun s -> file := s) usage; 
  if String.length !file == 0 then print_endline usage else 
    let _ = print_endline "LOADING sPL program .." in
    let (s,p) = parse_file !file in
    let _ = print_endline ("  "^s) in
    let _ = print_endline (" AS ==> "^(S.string_of_sPL p)) in
    let _ = print_endline "TYPE CHECKING program .." in
    let (v,np) = type_infer [] p in
    match v with
      | None -> print_endline " ==> type error detected"
      | Some t ->
            begin
              print_endline (" ==> inferred type "^(S.string_of_sPL_type t));
              let _ = print_string "TRANSFORMING ==> " in
              let np = trans_exp np in
              let _ = print_endline (string_of_sPL np) in
              let _ = print_string "EVALUATING ==> " in
              let r = evaluate [] np in
              print_endline (string_of_sPL_value r)
            end

