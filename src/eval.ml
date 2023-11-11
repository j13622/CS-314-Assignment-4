open Ast

exception TypeError
exception UndefinedVar
exception DivByZeroError

(* Remove shadowed bindings *)
let prune_env (env : environment) : environment =
  let binds = List.sort_uniq compare (List.map (fun (id, _) -> id) env) in
  List.map (fun e -> (e, List.assoc e env)) binds

(* Print env to stdout *)
let print_env_std (env : environment): unit =
  List.fold_left (fun _ (var, value) ->
      match value with
        | Int_Val i -> Printf.printf "- %s => %s\n" var (string_of_int i)
        | Bool_Val b -> Printf.printf "- %s => %s\n" var (string_of_bool b)
        | Closure _ -> ()) () (prune_env env)

(* Print env to string *)
let print_env_str (env : environment): string =
  List.fold_left (fun acc (var, value) ->
      match value with
        | Int_Val i -> acc ^ (Printf.sprintf "- %s => %s\n" var (string_of_int i))
        | Bool_Val b -> acc ^ (Printf.sprintf "- %s => %s\n" var (string_of_bool b))
        | Closure _ -> acc
      ) "" (prune_env env)


(***********************)
(****** Your Code ******)
(***********************)

(* evaluate an arithmetic expression in an environment *)
let rec eval_expr (e : exp) (env : environment) : value =
  match e with 
  | Var (v) -> 
    let x = List.assoc_opt v env in
    (match x with
    | Some y -> y
    | None -> raise UndefinedVar
    )
  | Number (v) -> Int_Val v
  | Plus (v1, v2) -> 
    let x = (eval_expr v1 env) in
    let y = (eval_expr v2 env) in
    (match x with
    | Int_Val (z1) -> 
      (match y with
        | Int_Val (z2) -> Int_Val (z1+z2)
        | _ -> raise TypeError
      )
    | _ -> raise TypeError
    )
  | Minus (v1, v2) -> 
    let x = (eval_expr v1 env) in
    let y = (eval_expr v2 env) in
    (match x with
    | Int_Val (z1) -> 
      (match y with
        | Int_Val (z2) -> Int_Val (z1-z2)
        | _ -> raise TypeError
      )
    | _ -> raise TypeError
    )
  | Times (v1, v2) ->
    let x = (eval_expr v1 env) in
    let y = (eval_expr v2 env) in
    (match x with
    | Int_Val (z1) -> 
      (match y with
        | Int_Val (z2) -> Int_Val (z1*z2)
        | _ -> raise TypeError
      )
    | _ -> raise TypeError
    )
  | Div (v1, v2) ->
    let x = (eval_expr v1 env) in
    let y = (eval_expr v2 env) in
    (match x with
    | Int_Val (z1) -> 
      (match y with
        | Int_Val (0) -> raise DivByZeroError
        | Int_Val (z2) -> Int_Val (z1/z2)
        | _ -> raise TypeError
      )
    | _ -> raise TypeError
    )
  | Mod (v1, v2) ->
    let x = (eval_expr v1 env) in
    let y = (eval_expr v2 env) in
    (match x with
    | Int_Val (z1) -> 
      (match y with
        | Int_Val (0) -> raise DivByZeroError
        | Int_Val (z2) -> Int_Val (z1 mod z2)
        | _ -> raise TypeError
      )
    | _ -> raise TypeError
    )
  | Eq (v1, v2) ->
    let x = (eval_expr v1 env) in
    let y = (eval_expr v2 env) in
    (match x with
    | Int_Val (z1) ->
      (match y with
      | Int_Val (z2) -> Bool_Val (z1 = z2)
      | _ -> raise TypeError
      )
    | Bool_Val(z1) -> 
      (match y with
      | Bool_Val (z2) -> Bool_Val (z1 = z2)
      | _ -> raise TypeError
      )
    | _ -> raise TypeError
    )
  | Leq (v1, v2) ->
    let x = (eval_expr v1 env) in
    let y = (eval_expr v2 env) in
    (match x with
    | Int_Val (z1) -> 
      (match y with
        | Int_Val (z2) -> Bool_Val (z1 <= z2)
        | _ -> raise TypeError
      )
    | _ -> raise TypeError
    )
  | Lt (v1, v2) ->
    let x = (eval_expr v1 env) in
    let y = (eval_expr v2 env) in
    (match x with
    | Int_Val (z1) -> 
      (match y with
        | Int_Val (z2) -> Bool_Val (z1 < z2)
        | _ -> raise TypeError
      )
    | _ -> raise TypeError
    )
  | Not v -> 
    let x = (eval_expr v env) in
    (match x with
    | Bool_Val (y) -> Bool_Val (not y)
    | _ -> raise TypeError
    )
  | And (v1, v2) ->
    let x = (eval_expr v1 env) in
    let y = (eval_expr v2 env) in
    (match x with
    | Bool_Val (z1) -> 
      (match y with
        | Bool_Val (z2) -> Bool_Val (z1 && z2)
        | _ -> raise TypeError
      )
    | _ -> raise TypeError
    )
  | Or (v1, v2) ->
    let x = (eval_expr v1 env) in
    let y = (eval_expr v2 env) in
    (match x with
    | Bool_Val (z1) -> 
      (match y with
        | Bool_Val (z2) -> Bool_Val (z1 || z2)
        | _ -> raise TypeError
      )
    | _ -> raise TypeError
    )
  | True -> Bool_Val (true)
  | False -> Bool_Val (false)
  | App (v1, v2) ->
    let x = (eval_expr v1 env) in
    let y = (eval_expr v2 env) in
    (match x with
    | Closure (z1, z2, z3) ->
      let fin_env = ((z2, y)::z1) in
      eval_expr z3 fin_env
    | _ -> raise TypeError
    )
  | Fun (v1, v2) -> Closure (env, v1, v2)


(* evaluate a command in an environment *)
let rec eval_command (c : com) (env : environment) : environment =
  match c with
  | While (v1, v2) ->
    let guard = eval_expr v1 env in
    (match guard with
    | Bool_Val (true) ->
      let new_env = eval_command v2 env in
      eval_command c new_env
    | Bool_Val (false) -> env
    | _ -> raise TypeError
    )
  | For (v1, v2) ->
    let guard = eval_expr v1 env in
    (match guard with
    | Int_Val (0) -> env
    | Int_Val (n) ->
      let new_env = eval_command v2 env in
      eval_command (For (Number (n - 1), v2)) new_env
    | _ -> raise TypeError
    )
  | Cond (v1, v2, v3) ->
    let guard = eval_expr v1 env in
    (match guard with
    | Bool_Val (true) -> eval_command v2 env
    | Bool_Val (false) -> eval_command v3 env
    | _ -> raise TypeError
    )
  | Comp (v1, v2) ->
    let next_env = eval_command v1 env in
    eval_command v2 next_env
  | Assg (v1, v2) ->
    let x = List.assoc_opt v1 env in
    let z = eval_expr v2 env in
    (match x with
    | Some (y) ->
      (match y, z with
      | Int_Val _, Int_Val _ -> (v1, z)::env
      | Bool_Val _, Bool_Val _ -> (v1, z)::env
      | Closure _, Closure _ -> (v1, z)::env
      | _, _ -> raise TypeError
      )
    | None -> raise UndefinedVar
    )
  | Declare (v1, v2) ->
    (match v1 with
    | Int_Type -> (v2, Int_Val(0))::env
    | Bool_Type -> (v2, Bool_Val(false))::env
    | Lambda_Type -> (v2, Closure (env, "x", Var "x"))::env
    )
  | Skip -> env