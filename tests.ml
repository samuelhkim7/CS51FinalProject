open Expr ;;
open Evaluation ;;
open Miniml ;;
open Test_util ;;

(** Tests for Expr **)

let test () =
  (* exp_to_abstract_string tested in repl *)

  (* free_vars tests *)
  unit_test (free_vars (Num 7) = vars_of_list [])
  "free_vars Num";
  unit_test (same_vars (free_vars (Fun ("x", Binop (Minus, Var "x", Var "y")))) 
  (vars_of_list ["y"]))
  "free_vars Fun";
  unit_test (same_vars (free_vars (Let ("x", Var "x", Var "y"))) 
  (vars_of_list ["y"]))
  "free_vars Let";
  unit_test (same_vars (free_vars (Let ("f", Fun ("x", Binop (Plus, Var "x", Var "y")), App (Var "f", Num 3)))) (vars_of_list ["y"]))
  "free_vars App";


  (* new_varname tests *)
  unit_test (new_varname () = "var0")
            "new_varname first call" ;
  unit_test (new_varname () = "var1")
            "new_varname second call" ;
  unit_test (new_varname () = "var2")
            "new_varname third call" ;
  
  (* subst tests *)
  unit_test (subst "x" (Num 7) (Var "x") = Num 7)
            "subst Num Var";
  unit_test (subst "x" (Num 7) (Binop (Plus, Var "x", Var "y")) = 
            (Binop (Plus, Num 7, Var "y")))
            "subst Binop";
  unit_test (subst "x" (Num 7) (Fun ("f", Binop (Times, Var "y", Var "x"))) = 
            (Fun ("f", Binop (Times, Var "y", Num 7))))
            "subst Fun";
  unit_test (subst "x" (Var "f") (Fun ("f", Binop (Plus, Var "x", Var "y"))) = 
            (Fun ("var4", Binop (Plus, Var "f", Var "y"))))
            "subst fresh variable";
  unit_test (subst "f" (Fun ("x", Binop (Plus, Var "x", Num 3))) 
            (App (Var "f", Num 3)) = 
            App (Fun ("x", Binop (Plus, Var "x", Num 3)), Num 3))
            "subst Num App";

  (* Env.lookup/extend tests *)
  let env1 = Env.extend (Env.empty ()) "x" (ref (Env.Val (Num 7))) in
  let env2 = Env.extend env1 "y" (ref (Env.Val (Fun ("x", Binop (Plus, Var "x", 
             Var "x"))))) in

  unit_test (Env.lookup env1 "x" = Env.Val (Num 7))
            "lookup/extend 1";
  unit_test (Env.lookup env2 "y" = Env.Val (Fun ("x", Binop (Plus, Var "x", Var 
                                   "x"))))
            "lookup/extend 2";

  (* Evaluation test cases *)
  let expr1 = Binop (Plus, Num 7, Binop (Times, Num 4, Num 3)) in
  let expr2 = Let("f", Fun ("x", Var "x"), App(Var "f", Num(7))) in
  let expr3 = App(Fun("x", Binop(Plus, Var"x", Var "x")), Num(7)) in
  let expr4 = Let("x", Num 1, Let("f", Fun("y", Binop(Plus, Var "x", Var "y")), Let("x", Num(2), App(Var "f", Num(3))))) in
  let expr5 = Let("x", Num(7), Let("f", Fun("y", Binop(Plus, Var "x", 
  Var "y")), Let("x", Num(2), App(Var "f", Num 42)))) in

  (* eval_s tests *)
  unit_test (eval_s expr1 (Env.empty ()) = Env.Val (Num 19))
            "eval_s Binop";
  unit_test (eval_s expr2 (Env.empty ()) = Env.Val (Num 7))
            "eval_s Let Fun App";
  unit_test (eval_s expr3 (Env.empty ()) = Env.Val (Num 14))
            "eval_s App Fun Binop";
  unit_test (eval_s expr4 (Env.empty ()) = Env.Val (Num 4))
            "eval_s dynamic/lexical";
  unit_test (eval_s expr5 (Env.empty ()) = Env.Val (Num 49))
            "eval_s dynamic/lexical 2";
  
  (* eval_d tests *)
  unit_test (eval_d expr1 (Env.empty ()) = Env.Val (Num 19))
            "eval_d Binop";
  unit_test (eval_d expr2 (Env.empty ()) = Env.Val (Num 7))
            "eval_d Let Fun App";
  unit_test (eval_d expr3 (Env.empty ()) = Env.Val (Num 14))
            "eval_d App Fun Binop";
  unit_test (eval_d expr4 (Env.empty ()) = Env.Val (Num 5))
            "eval_d dynamic/lexical";
  unit_test (eval_d expr5 (Env.empty ()) = Env.Val (Num 44))
            "eval_d dynamic/lexical 2";

  (* eval_l tests *)
  unit_test (eval_l expr1 (Env.empty ()) = Env.Val (Num 19))
            "eval_l Binop";
  unit_test (eval_l expr2 (Env.empty ()) = Env.Val (Num 7))
            "eval_l Let Fun App";
  unit_test (eval_l expr3 (Env.empty ()) = Env.Val (Num 14))
            "eval_l App Fun Binop";
  unit_test (eval_l expr4 (Env.empty ()) = Env.Val (Num 4))
            "eval_l dynamic/lexical";
  unit_test (eval_l expr5 (Env.empty ()) = Env.Val (Num 49))
            "eval_l dynamic/lexical 2";
;;

let _ = test () ;;