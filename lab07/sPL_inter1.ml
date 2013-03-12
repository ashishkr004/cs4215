open SPL_type
open Debug.Basic
open SPL_inter
open SPLc
module S = SPL
let usage = "usage: " ^ Sys.argv.(0) ^ " [options] <filename>"

(* Interpreter using Substitution *)
let rec eval (e:sPL_expr): sPL_expr = 
    match e with
    | BoolConst _ | IntConst _ -> e
    | UnaryPrimApp (op,arg) ->
        let varg = eval arg in
        contract (UnaryPrimApp (op,varg))
    | BinaryPrimApp (op,arg1,arg2) ->
        let varg1 = eval arg1 in
        let varg2 = eval arg2 in
        contract (BinaryPrimApp (op,varg1,varg2))
    | Var v ->
        print_endline ("WARNING : var is not a value!"); e 
    | Func (_,_,_) | RecFunc (_,_,_,_) -> e
  (* do not evaluate inside function body *)
    | Cond(e1,e2,e3) ->
        begin
            match eval e1 with
            | BoolConst b ->
                if b then eval e2
                else eval e3
            | _ -> 
                print_endline ("WARNING : not a bool value for Cond!");e
        end
    | Appln (f,t,args) ->
        begin
            let nf = eval f in
            let args = List.map (eval) args in
            match nf with
            | Func(t1,vs,body) -> 
                let (subs,remain) = pair_fn_args vs args in
                let ans = (eval (apply_subs subs body)) in
                if remain==[] then ans
                else eval (Appln (ans,t1,remain))
            | RecFunc(t1,r,vs,body) ->
              (* similar to case based on Func *)
                let (subs, remain) = pair_fn_args (r::vs) (nf::args) in
                let ans = (eval (apply_subs subs body)) in
                if remain == [] then ans
                else eval (Appln (ans,t1,remain))
            | _ -> 
                print_endline ("WARNING : not a function value for Appln!");e
        end

let evaluate env e = eval e

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
                print_endline (string_of_sPL r)
            end
