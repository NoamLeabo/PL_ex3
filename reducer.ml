(* Reducers (interpreters) for lambda-calculus. *)

open Utils
open Parser

exception OutOfVariablesError

(* 
  List of all possible variable names.
  Generated using ASCII values for lowercase (a-z) and uppercase (A-Z).
*)
let possible_variables = List.map (fun x -> char_to_string (char_of_int x)) ((range 97 123) @ (range 65 91))

(* 
  Generates a fresh variable name that is not in the set of used variables. 
  If all variables are exhausted, raises an exception.
*)
let fresh_var used_vars : string = 
  if StringSet.is_empty (StringSet.diff (string_set_from_list possible_variables) used_vars) 
  then raise (OutOfVariablesError)
  else StringSet.choose (StringSet.diff (string_set_from_list possible_variables) used_vars)

(* 
  Returns the set of free variables in a lambda calculus term. 
  Free variables are those not bound by an abstraction.
*)
let rec fv term =
  match term with
  | Variable x -> StringSet.singleton x  (* A variable itself is free. *) (* FV(x) = {x} *)
  | Abstraction (x, t) -> StringSet.remove x (fv t)  (* Remove bound variable from free variables. *) (* FV(λx. t) = FV(t) - {x} *)
  | Application (t1, t2) -> StringSet.union (fv t1) (fv t2)  (* Union of free variables from both terms. *) (* FV(t1 t2) = FV(t1) ∪ FV(t2) *)

(* 
  Substitutes a variable with a replacement term in the given lambda term.
  Handles alpha-conversion to avoid variable capture.
*)
let rec substitute var replacement term =
  match term with
  | Variable x ->
      if x = var then replacement  (* Replace x with the replacement term if it matches var *)
      else term  (* Otherwise, return the variable unchanged *)

  | Abstraction (x, t) ->
      if x = var then
        term  (* If the bound variable matches var, do nothing as it is not free in this scope *)
      else if StringSet.mem x (fv replacement) then
        (* Perform alpha-conversion to avoid variable capture. *)
        let new_var = fresh_var (StringSet.union (fv t) (fv replacement)) in
        let new_body = substitute x (Variable new_var) t in
        Abstraction (new_var, substitute var replacement new_body)
      else
        Abstraction (x, substitute var replacement t)

  | Application (t1, t2) ->
      Application (substitute var replacement t1, substitute var replacement t2)

(* 
  Implements a single reduction step using Call-By-Value (CBV) semantics.
  Reduces only when arguments are fully evaluated.
*)
let rec reduce_cbv term =
  match term with
  | Parser.Variable _ -> None  (* Variables are irreducible. *)
  | Parser.Abstraction _ -> None  (* Abstractions are already values. *)
  | Parser.Application (Parser.Abstraction (x, body), t2) ->
      (* Reduces (λx. body) t2 if t2 is a value. *)
      (match reduce_cbv t2 with
      | None -> Some (substitute x t2 body)  (* Substitute t2 into the body. *)
      | Some t2' -> Some (Parser.Application (Parser.Abstraction (x, body), t2')))
  | Parser.Application (t1, t2) ->
      (* Try reducing t1 first. *)
      (match reduce_cbv t1 with
      | Some t1' -> Some (Parser.Application (t1', t2))
      | None -> (
          (* If t1 is a value, try reducing t2. *)
          match reduce_cbv t2 with
          | Some t2' -> Some (Parser.Application (t1, t2'))
          | None -> None))

(* 
  Implements a single reduction step using Call-By-Name (CBN) semantics.
  Reduces the outermost function application without evaluating arguments first.
*)
let rec reduce_cbn term =
  match term with
  | Parser.Variable _ -> None  (* Variables are irreducible. *)
  | Parser.Abstraction _ -> None  (* Abstractions are already values. *)
  | Parser.Application (Parser.Abstraction (x, body), t2) ->
      (* Substitute directly, without reducing t2. *)
      Some (substitute x t2 body)
  | Parser.Application (t1, t2) ->
      (* Try reducing t1. *)
      match reduce_cbn t1 with
      | Some t1' -> Some (Parser.Application (t1', t2))
      | None -> None  (* Call-by-name does not reduce t2 if t1 is irreducible. *)
