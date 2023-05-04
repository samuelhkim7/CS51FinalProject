(* 
            Unit Teting Framework Based on CS51 Utils
*)

let unit_test (condition : bool) (msg : string) : unit =  
  if condition then
    Printf.printf "%s passed\n" msg
  else
    Printf.printf "%s FAILED\n" msg ;;

let unit_test_within (tolerance : float)
    (value1 : float)
    (value2 : float)
    (msg : string)
  : unit =
  unit_test (abs_float (value1 -. value2) < tolerance) msg ;;