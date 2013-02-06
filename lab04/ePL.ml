type op_id = string

(* abstract syntax tree for ePL *)
type ePL_expr =
  | BoolConst of bool
  | IntConst of int
  | UnaryPrimApp of op_id * ePL_expr
  | BinaryPrimApp of op_id * ePL_expr * ePL_expr

(* display ePL expr in prefix form *)
let rec string_of_ePL (e:ePL_expr):string =
  match e with
    | BoolConst v -> "BoolConst("^(string_of_bool v)^")"
    | IntConst v -> "IntConst("^(string_of_int v)^")"
    | UnaryPrimApp (op,arg) -> op^"["^(string_of_ePL arg)^"]"
    | BinaryPrimApp (op,arg1,arg2) -> op^"["^(string_of_ePL arg1)^","^(string_of_ePL arg2)^"]"


type ePL_type =
  | BoolType
  | IntType

let string_of_ePL_type (e:ePL_type):string =
  match e with
    | BoolType -> "Bool"
    | IntType -> "Int"

type eVML_inst =
  | LDCI of int
  | LDCB of int (* 0 - false; 1 - true *)
  | PLUS | MINUS | TIMES | DIV | AND | NEG
  | NOT | OR | LT | GT | EQ | DONE

type eVML_prog = eVML_inst list

let iSeq : eVML_prog = [LDCI 1; LDCI 2; PLUS; DONE]

let iArr : eVML_inst array = Array.of_list iSeq

let decode_bool x = 
  match x with
    | 0 -> false
    | _ -> true

let string_of_eVML x =
  match x with
    | LDCI i -> "LDCI "^(string_of_int i)
    | LDCB b -> "LDCB "^(string_of_bool (decode_bool b))
    | PLUS -> "PLUS"
    | MINUS -> "MINUS"
    | TIMES -> "TIMES"
    | DIV -> "DIV"
    | AND -> "AND"
    | NEG -> "NEG"
    | NOT -> "NOT"
    | OR -> "OR"
    | LT -> "LT"
    | GT  -> "GT"
    | EQ  -> "EQ"
    | DONE -> "DONE"

let pr_lst s f xs = String.concat s (List.map f xs)
let pr_list_brk open_b close_b f xs  = open_b ^(pr_lst "," f xs)^close_b
let pr_list f xs = pr_list_brk "[" "]" f xs

(* printing a list of eVML instructions *)
let string_of_eVML_list (xs:eVML_inst list) =
  pr_list string_of_eVML xs
