open EPL

(* type checking method *)
let rec type_check (e:ePL_expr) (t:ePL_type) : bool =
  match e,t with
    | IntConst _, IntType -> true
    | BoolConst _, BoolType -> true
    | UnaryPrimApp (op,arg), _ ->
      begin
        match op,t with
          | "~",IntType ->
            type_check arg IntType
          | "\\",BoolType ->
            type_check arg BoolType
          | _,_ -> false
      end
    | BinaryPrimApp (op,arg1,arg2), _ ->
      begin
        match op,t with
          | "+",IntType | "-",IntType | "*",IntType | "/",IntType ->
            (type_check arg1 IntType) && (type_check arg2 IntType)
          | "<",BoolType | ">",BoolType | "=",BoolType ->
            (type_check arg1 IntType) && (type_check arg2 IntType)
          | "|",BoolType | "&",BoolType ->
            (type_check arg1 BoolType) && (type_check arg2 BoolType)
          | _,_ -> false
      end
    | _, _ -> false


(* type inference, note that None is returned 
   if no suitable type is inferred *)
let type_infer (e:ePL_expr) : ePL_type option =
  match e with
    | IntConst _ -> Some IntType
    | BoolConst _ -> 
      Some BoolType
    | UnaryPrimApp (op,arg) ->
      begin
        match op with
          | "~" -> 
            if (type_check arg IntType) then Some IntType
            else None
          | "\\" ->
            if (type_check arg BoolType) then Some BoolType
            else None
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
            if (type_check arg1 IntType) && (type_check arg2 IntType) 
            then Some BoolType
            else None
          | "&" | "|" ->
            if (type_check arg1 BoolType) && (type_check arg2 BoolType) 
            then Some BoolType
            else None
          | _ ->
            failwith ("uncognizer operator"^op)
      end
