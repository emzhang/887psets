1 subgoals, subgoal 1 (ID 1209)
  
  m : map_
  r : reduce
  a : list nat
  lsls : list (list nat)
  IHlsls : interp_mr (m, r) (fold_left app lsls []) =
           interp_reduce r (map (interp_mr (m, r)) lsls)
  ============================
   interp_mr (m, r) (fold_left app lsls a) =
   interp_reduce r (interp_mr (m, r) a :: map (interp_mr (m, r)) lsls)

