(* 
                         CS 51 Final Project
                        MiniML -- Expressions
*)

(*......................................................................
  Abstract syntax of MiniML expressions 
 *)

type unop =
  | Negate
;;
    
type binop =
  | Plus
  | Minus
  | Times
  | Equals
  | LessThan
;;

type varid = string ;;
  
type expr =
  | Var of varid                         (* variables *)
  | Num of int                           (* integers *)
  | Bool of bool                         (* booleans *)
  | Unop of unop * expr                  (* unary operators *)
  | Binop of binop * expr * expr         (* binary operators *)
  | Conditional of expr * expr * expr    (* if then else *)
  | Fun of varid * expr                  (* function definitions *)
  | Let of varid * expr * expr           (* local naming *)
  | Letrec of varid * expr * expr        (* recursive local naming *)
  | Raise                                (* exceptions *)
  | Unassigned                           (* (temporarily) unassigned *)
  | App of expr * expr                   (* function applications *)
;;
  
(*......................................................................
  Manipulation of variable names (varids) and sets of them
 *)

(* varidset -- Sets of varids *)
module SS = Set.Make (struct
                       type t = varid
                       let compare = String.compare
                     end ) ;;

type varidset = SS.t ;;

(* same_vars varids1 varids2 -- Tests to see if two `varid` sets have
   the same elements (for testing purposes) *)
let same_vars : varidset -> varidset -> bool =
  SS.equal;;

(* vars_of_list varids -- Generates a set of variable names from a
   list of `varid`s (for testing purposes) *)
let vars_of_list : string list -> varidset =
  SS.of_list ;;
  
(* free_vars exp -- Returns the set of `varid`s corresponding to free
   variables in `exp` *)
let rec free_vars (exp : expr) : varidset =
  let empty = SS.empty in 
  match exp with
  | Var n -> SS.add n empty
  | Num _
  | Bool _ -> empty
  | Unop (_op, expr) -> free_vars expr
  | Binop (_op, expr1, expr2) -> SS.union (free_vars expr1) (free_vars expr2)
  | Conditional (expr1, expr2, expr3) -> SS.union (SS.union (free_vars expr1)
                                         (free_vars expr2)) (free_vars expr3)
  | Fun (n, expr) -> SS.remove n (free_vars expr)
  | Let (n, expr1, expr2) -> SS.remove n (SS.union (free_vars expr1) 
                             (free_vars expr2))
  | Letrec (n, expr1, expr2) -> SS.remove n (SS.union (free_vars expr1) 
                                (free_vars expr2))
  | Raise  
  | Unassigned -> empty
  | App (expr1, expr2) -> SS.union (free_vars expr1) (free_vars expr2)
;;
  
(* new_varname () -- Returns a freshly minted `varid` constructed with
   a running counter a la `gensym`. Assumes no other variable names
   use the prefix "var". (Otherwise, they might accidentally be the
   same as a generated variable name.) *)
let new_varname : unit -> varid =
  let counter = ref 0 in
  fun () -> let varname = "var" ^ string_of_int !counter in
            counter := !counter + 1;
            varname ;;

(*......................................................................
  Substitution 

  Substitution of expressions for free occurrences of variables is the
  cornerstone of the substitution model for functional programming
  semantics.
 *)

(* subst var_name repl exp -- Return the expression `exp` with `repl`
   substituted for free occurrences of `var_name`, avoiding variable
   capture *)
let rec subst (var_name : varid) (repl : expr) (exp : expr) : expr =
  (* function for checking free variables in repl that have same name as 'var' input *)
  let inrepl var =
    if SS.mem var (free_vars repl) then true
    else false in
  match exp with
  | Var n -> if n = var_name && SS.mem n (free_vars exp) then repl
             else exp
  | Num _
  | Bool _ -> exp
  | Unop (op, expr1) -> Unop(op, subst var_name repl expr1)
  | Binop (op, expr1, expr2) -> Binop(op, (subst var_name repl expr1),
                                (subst var_name repl expr2))
  | Conditional (expr1, expr2, expr3) -> Conditional ((subst var_name repl 
                                         expr1), (subst var_name repl expr2),
                                         (subst var_name repl expr3))
  | Fun (n, expr1) -> (* create new fresh variable *)
                      let z = new_varname () in
                      (* check if n is the same as var_name in which case  
                      should return the expression unchanged*)
                      if n = var_name then exp
                      else if inrepl n then 
                        Fun(z, (subst var_name repl (subst n (Var z) expr1)))
                      else Fun(n, subst var_name repl expr1)
  | Let (n, expr1, expr2) -> let z = new_varname () in 
                             if n = var_name then exp
                             else if inrepl n then 
                              Let(z, (subst var_name repl expr1), 
                              (subst var_name repl (subst n (Var z) expr2)))
                             else Let(n, subst var_name repl expr1, subst var_name repl expr2)
  | Letrec (n, expr1, expr2) -> let z = new_varname () in
                                if n = var_name then exp
                                else if inrepl n then 
                                  Letrec(z, (subst var_name repl (subst n (Var z) expr1)), (subst var_name repl (subst n (Var z) expr2)))
                                else Letrec(n, subst var_name repl expr1, subst var_name repl expr2)
  | Raise 
  | Unassigned -> exp
  | App (expr1, expr2) -> App((subst var_name repl expr1), 
                          (subst var_name repl expr2))                          
;;
     
(*......................................................................
  String representations of expressions
 *)
   
(* exp_to_concrete_string exp -- Returns a string representation of
   the concrete syntax of the expression `exp` *)
let rec exp_to_concrete_string (exp : expr) : string =
  match exp with 
  | Var n -> n
  | Num n -> string_of_int n
  | Bool n -> string_of_bool n
  | Unop (_op, expr1) -> "-" ^ exp_to_concrete_string expr1
  | Binop (op, expr1, expr2) -> (
                                      match op with
                                      | Plus -> exp_to_concrete_string expr1 ^ " + " ^ exp_to_concrete_string expr2
                                      | Minus -> exp_to_concrete_string expr1 ^ " - " ^ exp_to_concrete_string expr2
                                      | Times -> exp_to_concrete_string expr1 ^ " * " ^ exp_to_concrete_string expr2
                                      | Equals -> exp_to_concrete_string expr1 ^ " = " ^ exp_to_concrete_string expr2
                                      | LessThan -> exp_to_concrete_string expr1 ^ " < " ^ exp_to_concrete_string expr2 )
  | Conditional (expr1, expr2, expr3) -> 
                                      "if " ^ exp_to_concrete_string expr1 ^
                                      " then " ^ exp_to_concrete_string expr2 ^
                                      " else " ^ exp_to_concrete_string expr3
  | Fun (n, expr1) -> "fun " ^ n ^ " -> " ^ 
                           exp_to_concrete_string expr1 
  | Let (n, expr1, expr2) -> "let " ^ n ^ " = " ^
                                    exp_to_concrete_string expr1 ^ " in " ^
                                    exp_to_concrete_string expr2 
  | Letrec (n, expr1, expr2) -> "let rec " ^ n ^ " = " ^
                                       exp_to_concrete_string expr1 ^
                                       " in " ^ exp_to_concrete_string expr2
  | Raise -> "raise exception" 
  | Unassigned -> "unassigned"
  | App (expr1, expr2) -> exp_to_concrete_string expr1 ^ " " ^
                            exp_to_concrete_string expr2 
                          
;;
     
(* exp_to_abstract_string exp -- Return a string representation of the
   abstract syntax of the expression `exp` *)
let rec exp_to_abstract_string (exp : expr) : string =
  match exp with
  | Var n -> "Var(" ^ n ^ ")"
  | Num n -> "Num(" ^ string_of_int n ^ ")"
  | Bool n -> "Bool(" ^ string_of_bool n ^ ")" 
  | Unop (_op, expr) -> "Negate(" ^ exp_to_abstract_string expr ^ ")"
  | Binop (op, expr1, expr2) -> (
                                      match op with
                                      | Plus -> "Binop(Plus, " ^ exp_to_abstract_string expr1 ^ ", " ^
                                      exp_to_abstract_string expr2 ^ ")"
                                      | Minus -> "Binop(Minus, " ^ exp_to_abstract_string expr1 ^ ", " ^
                                      exp_to_abstract_string expr2 ^ ")"
                                      | Times -> "Binop(Times, " ^ exp_to_abstract_string expr1 ^ ", " ^
                                      exp_to_abstract_string expr2 ^ ")"
                                      | Equals -> "Binop(Equals, " ^ exp_to_abstract_string expr1 ^ 
                                                  ", " ^ exp_to_abstract_string expr2 ^ ")"
                                      | LessThan -> "Binop(LessThan, " ^ exp_to_abstract_string expr1 ^ ", " ^
                                      exp_to_abstract_string expr2 ^ ")" )
  | Conditional (expr1, expr2, expr3) -> "Conditional(" ^
                                            exp_to_abstract_string expr1 ^ ", "
                                            ^ exp_to_abstract_string expr2 ^ 
                                            "," ^ 
                                            exp_to_abstract_string expr3 ^ ")"
  | Fun (n, expr) -> "Fun(" ^ n ^ ", " ^ 
                           exp_to_abstract_string expr ^ ")"
  | Let (n, expr1, expr2) -> "Let(" ^ n ^ ", " ^
                                    exp_to_abstract_string expr1 ^ ", " ^
                                    exp_to_abstract_string expr2 ^ ")"
  | Letrec (n, expr1, expr2) -> 
                                      "Letrec(" ^ n ^ ", " ^ exp_to_abstract_string expr1 ^ ", " ^
                                      exp_to_abstract_string expr2 ^ ")"
  | Raise -> "Raise"
  | Unassigned -> "Unassigned"
  | App (expr1, expr2) -> "App(" ^ exp_to_abstract_string expr1 ^ ", " ^
                            exp_to_abstract_string expr2 ^ ")"       
;;