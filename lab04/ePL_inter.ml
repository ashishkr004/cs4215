open EPL

(* use primitive rule to contract op[v1,v2] or op[v] to a value *)
(* raise an exception if we cannot directly contract *)
let rec contract (e:ePL_expr): ePL_expr = 
  match e with
    | BoolConst _ | IntConst _ -> e
    | UnaryPrimApp (op,arg) ->
          begin
          match op with
            | "~" ->
                  begin
                  match arg with
                    | IntConst v -> IntConst (-v)
                    | _ -> failwith ("unable to contract for "^(string_of_ePL e))
                  end
            | "\\" ->
                  failwith ("to be implemented ")
            | _ -> failwith ("illegal unary op "^op)
          end
    | BinaryPrimApp (op,arg1,arg2) ->
          begin
          match op with
            | "+" ->
                  begin
                  match arg1,arg2 with
                    | IntConst v1,IntConst v2 -> IntConst (v1+v2)
                    | _,_ -> failwith ("unable to contract "^(string_of_ePL e))
                  end
            | "-" ->
                  begin
                  match arg1,arg2 with
                    | IntConst v1,IntConst v2 -> IntConst (v1-v2)
                    | _,_ -> failwith ("unable to contract"^(string_of_ePL e))
                  end
            | "*" ->
                  begin
                  match arg1,arg2 with
                    | IntConst v1,IntConst v2 -> IntConst (v1*v2)
                    | _,_ -> failwith ("unable to contract"^(string_of_ePL e))
                  end
            | "/" ->
                  begin
                  match arg1,arg2 with
                    | IntConst v1,IntConst v2 -> IntConst (v1/v2)
                    | _,_ -> failwith ("unable to contract"^(string_of_ePL e))
                  end
            | "|" ->
                  failwith ("to be implemented ")
            | "&" ->
                  failwith ("to be implemented ")
            | "<" ->
                  failwith ("to be implemented ")
            | ">" ->
                  failwith ("to be implemented ")
            | "=" ->
                  failwith ("to be implemented ")
            | _ -> failwith ("illegal binary op "^op)
          end

(* check if an expression is reducible or irreducible *)
let reducible (e:ePL_expr) : bool = 
  match e with
    | BoolConst _ | IntConst _ -> false
    | UnaryPrimApp _ | BinaryPrimApp _ -> true

(* if expr is irreducible, returns it *)
(* otherwise, perform a one-step reduction *)
let rec oneStep (e:ePL_expr): ePL_expr = 
  match e with
    | BoolConst _ | IntConst _ -> e
    | UnaryPrimApp (op,arg) ->
          if reducible arg then UnaryPrimApp(op,oneStep arg)
          else contract e
    | BinaryPrimApp (op,arg1,arg2) ->
          if reducible arg1 
          then BinaryPrimApp(op,oneStep arg1,arg2)
          else 
            if reducible arg2
            then BinaryPrimApp(op,arg1,oneStep arg2)
            else contract e

(* keep reducing until we get a irreducible expr *)
(* or has an exception due to wrong operator or type error *)
let rec evaluate (e:ePL_expr): ePL_expr = 
  if (reducible e) then evaluate (oneStep e)
  else e


(* sample expr in AST form *)
let e1 = IntConst 42
let e2 = 
  BinaryPrimApp ("+",
    BinaryPrimApp("*",
      UnaryPrimApp("~",IntConst 15),
      IntConst 7),
    IntConst 2)
let e2a = 
  BinaryPrimApp (">",IntConst 7,IntConst 10)
let e2b = 
  BinaryPrimApp ("=",
    IntConst 10,
    BinaryPrimApp("+",IntConst 3,IntConst 7))

let e3 = 
  BinaryPrimApp ("|",
    BinaryPrimApp("&",
      UnaryPrimApp("\\",BoolConst false),
      BoolConst true),
    BoolConst true)
let e4 = 
  BinaryPrimApp ("+",IntConst 15,BoolConst true)
let e5 = 
  BinaryPrimApp ("!",IntConst 15,BoolConst true)
let e5 = 
  BinaryPrimApp (">",BoolConst false,BoolConst true)
let e6 = 
  BinaryPrimApp ("*",
     BinaryPrimApp ("+",IntConst 1,IntConst 2),
     IntConst 3)
let e7 = 
  BinaryPrimApp ("+",
     IntConst 1,
     BinaryPrimApp ("*",IntConst 2,IntConst 3))

(* type checking method *)
let rec type_check (e:ePL_expr) (t:ePL_type) : bool =
  match e,t with
    | IntConst _, IntType -> true
    | BoolConst _, BoolType -> 
          failwith ("to be implemented ")
    | UnaryPrimApp (op,arg), _ ->
          begin
          match op,t with
            | "~",IntType ->
                  type_check arg IntType
            | "\\",BoolType ->
                  failwith ("to be implemented ")
            | _,_ -> false
          end
    | BinaryPrimApp (op,arg1,arg2), _ ->
          begin
          match op,t with
            | "+",IntType | "-",IntType | "*",IntType | "/",IntType ->
                  (type_check arg1 IntType) && (type_check arg2 IntType)
            | "<",BoolType | ">",BoolType | "=",BoolType ->
                  failwith ("to be implemented ")
            | "|",BoolType | "&",BoolType ->
                  failwith ("to be implemented ")
            | _,_ -> false
          end
    | _, _ -> false


(* type inference, note that None is returned 
   if no suitable type is inferred *)
let type_infer (e:ePL_expr) : ePL_type option =
  match e with
    | IntConst _ -> Some IntType
    | BoolConst _ -> 
          failwith ("to be implemented ")
    | UnaryPrimApp (op,arg) ->
          begin
          match op with
            | "~" -> 
                  if (type_check arg IntType) then Some IntType
                  else None
            | "\\" ->
                  failwith ("to be implemented ")
            | _ -> None
          end
    | BinaryPrimApp (op,arg1,arg2) ->
          begin
          match op with
            | "-" | "+" | "*" | "/"  -> 
                  if (type_check arg1 IntType) && (type_check arg2 IntType) 
                  then Some IntType
                  else None
            | "<" | ">" | "=" ->
                  failwith ("to be implemented ")
            | "&" | "|" ->
                  failwith ("to be implemented ")
            | _ ->
                  failwith ("uncognizer operator"^op)
          end


(* test driver for evaluation *)
let testCommand e =
  print_endline ("ePL expr:"^(string_of_ePL e));
  print_endline ("oneStep :"^(string_of_ePL (oneStep e)));
  print_endline ("evaluate:"^(string_of_ePL (evaluate e)))

(* test driver for type inference *)
let testType e =
  (* let s = (string_of_ePL e) in *)
  let v = type_infer e in
  match v with 
    | Some t -> print_endline ("  inferred type : "^(string_of_ePL_type t));
    | None -> print_endline ("  type error ")

(* let _ = testCommand e2  *)
(* let _ = testCommand e2a  *)
(* let _ = testCommand e2b  *)
(* let _ = testCommand e3 *)

(* let _ = testType e1 *)
(* let _ = testType e2 *)
(* let _ = testType e2a  *)
(* let _ = testType e2b  *)
(* let _ = testType e3 *)
(* let _ = testType e4 *)
(* let _ = testType e5 *)

(* let _ = testType e6 *)
(* let _ = testCommand e6 *)
(* let _ = testType e7 *)
(* let _ = testCommand e7 *)
(* let _ = testType e4 *)
(* let _ = testCommand e4 *)

(* calling ePL parser *)
let parse_file (filename:string) : (string * ePL_expr) =
  EPL_parser.parse_file filename
 
(* set up for command argument
   using Sys and Arg modules *)
let usage = "usage: " ^ Sys.argv.(0) ^ " <filename>"
let file = ref "" 

(* main program *)
let main =
  (* Read the arguments of command *)
  Arg.parse [] (fun s -> file := s) usage; 
  if String.length !file == 0 then print_endline usage else 
  let _ = print_endline "Loading ePL program .." in
  let (s,p) = parse_file !file in
  let _ = print_endline ("  "^s) in
  let _ = print_endline ("  as "^(string_of_ePL p)) in
  let _ = print_endline "Type checking program .." in
  let _ = testType p in
  let _ = print_string "Evaluating ==> " in
  let r = evaluate p in
  print_endline (string_of_ePL r)
