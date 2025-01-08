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
  we return the set of free variables in a lambda calculus term. 
  we saw in call that a free variable is one that is not bound by an abstraction.
*)
let rec fv term =
  match term with
  | Variable x -> StringSet.singleton x  (* a variable itself is free. *) (* like the case of - FV(x) = {x} *)
  | Abstraction (x, t) -> StringSet.remove x (fv t)  (* we remove bound variable from free variables. *) (* the case of - FV(λx. t) = FV(t) - {x} *)
  | Application (t1, t2) -> StringSet.union (fv t1) (fv t2)  (* we return the union of free variables from both terms of each side. *) (* the case of - FV(t1 t2) = FV(t1) ∪ FV(t2) *)

(* 
  substitutes a variable with a replacement term in the *given* lambda term.
  also we handle alpha-conversion to avoid variable capture as required.
	structre of the input is like - "(λvar.term) replacement"
*)
let rec substitute var replacement term =
  match term with
  | Variable x ->
      if x = var then replacement  (* replace x with the replacement term if it matches var *)
      else term  (* otherwise return the variable unchanged *)

  | Abstraction (x, t) ->
      if x = var then
        term  (* if the bound variable matches var do nothing as it is not free in this scope *)
      else if StringSet.mem x (fv replacement) then
        (* perform "alpha-conversion" to avoid variable capture. *)
        let new_var = fresh_var (StringSet.union (fv t) (fv replacement)) in
        let new_body = substitute x (Variable new_var) t in
        Abstraction (new_var, substitute var replacement new_body)
      else
        Abstraction (x, substitute var replacement t)

  | Application (t1, t2) ->
      Application (substitute var replacement t1, substitute var replacement t2)

(* 
  checks if a term is a value.
  according to the definition (at least in the instructions in the task) in CBV, only abstractions are considered values.
*)
let rec is_value term =
  match term with
  | Parser.Abstraction _ -> true  (* a value is only an abstraction. *)
  | _ -> false  (* all other terms are not values. *)


(* 
  implements a single reduction step using Call-By-Value (CBV) semantics.
  reduces only when arguments are fully evaluated.
*)
let rec reduce_cbv term =
  match term with
  | Parser.Variable _ -> None  (* variables are irreducible. *)
  | Parser.Abstraction _ -> None  (* abstractions are already values. *)
  | Parser.Application (Parser.Abstraction (x, body), t2) ->
      (* reduces (λx. body) t2 if t2 is a value. *)
      if is_value t2 then
        Some (substitute x t2 body)  (* substitute t2 into the body. *)
        (* we perform substitution only if t2 is a value. *)
      else (
        match reduce_cbv t2 with
        | Some t2' -> Some (Parser.Application (Parser.Abstraction (x, body), t2')) (* trying reducing t2 recursively if it's not yet a value. *)
        | None -> None (* if t2 is irreducible and not a value, stop. *)
      )
  | Parser.Application (t1, t2) ->  
      (* try reducing t1 first. *)
      (match reduce_cbv t1 with
      | Some t1' -> Some (Parser.Application (t1', t2)) (* reduce t1 and construct the new application term. *)
      | None -> (
          (* if t1 is a value, try reducing t2. *)
          match reduce_cbv t2 with
          | Some t2' -> Some (Parser.Application (t1, t2')) (* reduce t2 and construct the new application term. *)
          | None -> None)) (* if neither t1 nor t2 can be reduced and we stop. *)

(* 
  implements a single reduction step using Call-By-Name (CBN) semantics.
  reduces the outermost function application without evaluating arguments first.
*)
let rec reduce_cbn term =
  match term with
  | Parser.Variable _ -> None  (* variables are irreducible. *)
  | Parser.Abstraction _ -> None  (* abstractions are already values. *)
  | Parser.Application (Parser.Abstraction (x, body), t2) ->
      (* substitute directly, without reducing t2. *)
      Some (substitute x t2 body)
  | Parser.Application (t1, t2) ->
      (* try reducing t1. *)
      match reduce_cbn t1 with
      | Some t1' -> Some (Parser.Application (t1', t2))
      | None -> None  (* call-by-name does not reduce t2 if t1 is irreducible. *)
