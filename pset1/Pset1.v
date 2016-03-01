(** * 6.887 Formal Reasoning About Programs, Spring 2016 - Pset 1 *)

Require Import Frap Pset1Sig.                             

Lemma applyIndHyp : forall (x : nat) (m1: map_) (m2 : map_), (allPositive m1 -> x > 0 -> interp_map m1 x > 0) -> ( allPositive m2 -> x > 0 -> interp_map m2 x > 0) -> ( allPositive (Add m1 m2) -> x > 0 -> interp_map (Add m1 m2) x > 0).
  Proof.
    intros.
    simplify.
    destruct H1.
    specialize (H H1 H2).
    specialize (H0 H3 H2).
    linear_arithmetic.
  Qed.
Theorem allPositive_ok : forall (m : map_) (x : nat),
  allPositive m
  -> x > 0
  -> interp_map m x > 0.
Proof.
  
  (*works below*)
  induct m. intro.
  intro.
  intro.
  unfold interp_map.
  unfold allPositive in H. trivial.

  intro.
  intro.
  intro.
  unfold allPositive in H.
  unfold interp_map. trivial.

  intro.
  Check applyIndHyp.
  apply (applyIndHyp x m1 m2 (IHm1 x) (IHm2 x)).

  intros.
  simplify.
  specialize (IHm2 x).
  specialize (IHm1 (interp_map m2 x)).
  destruct H.
  exact (IHm1 H (IHm2 H1 H0)).
Qed.
(*from perry*)
(*
Lemma fl_lsls_plus_ls: forall (lsls : list(list nat)) (ls1 ls2 : nat), fold_left plus lsls (ls1 ++ ls2) = fold_left plus lsls ls1 ++ ls2.
Proof.

Admitted.*)

Lemma fl_list_plus_nat: forall (ls : list nat) (a0 a : nat), fold_left plus ls (a0 + a) = fold_left plus ls a0 + a.
Proof.
  induct ls.
  simplify.
  ring.
  simplify.
  repeat rewrite IHls.
  SearchAbout fold_left.
  ring.
Qed.

Lemma fl_list_max_nat: forall (ls : list nat) (a0 a : nat), fold_left max ls (max a0 a) = max (fold_left max ls a0) a.
Proof.
  induct ls.
  simplify.
  ring.

  simplify.
  repeat rewrite IHls.
  SearchAbout max.
  
  rewrite <- Max.max_assoc .
  symmetry.
  rewrite <- Max.max_assoc.
  f_equal.
  apply Max.max_comm.
Qed.

Lemma fl_swap_plus : forall (ls1 ls2 : list nat) (a:nat), fold_left plus (ls1 ++ ls2) a = fold_left plus (ls2 ++ ls1) a.
Proof.
  induct ls1.
  simplify.
  rewrite app_nil_r.
  equality.
  
  simplify.
  SearchAbout fold_left app.
  rewrite IHls1.
  repeat rewrite fold_left_app.
  simplify.
  f_equal.
  apply fl_list_plus_nat.
Qed.

Lemma fl_swap_max :  forall (ls1 ls2 : list nat) (a:nat), fold_left max (ls1 ++ ls2) a = fold_left max (ls2 ++ ls1) a.
Proof.
  induct ls1.
  simplify.
  rewrite app_nil_r.
  equality.

  simplify.
  rewrite IHls1.
  repeat rewrite fold_left_app.
  repeat simplify.
  f_equal.
  apply fl_list_max_nat.
Qed.
    
Theorem reduce_swap : forall e ls1 ls2, interp_reduce e (ls1 ++ ls2) = interp_reduce e (ls2 ++ ls1).
Proof.  
  (*try cases, destruct, cases on +, max*)
  induct e.
  simplify.
  apply fl_swap_plus.
  repeat simplify.
  apply fl_swap_max.
Qed.


Theorem interp_swap : forall e ls1 ls2, interp_mr e (ls1 ++ ls2) = interp_mr e (ls2 ++ ls1).
Proof.
  induct e.
  simplify.
  unfold interp_mr.
  simplify.
  SearchAbout map.
  rewrite -> map_app.
  symmetry.
  rewrite -> map_app.
  simplify.
  rewrite reduce_swap.
  equality.  
Qed.

Lemma red_add_dist : forall(ls1 ls2 : list nat), fold_left plus (ls1 ++ ls2) 0 = fold_left plus ls1 0 + fold_left plus ls2 0. 
Proof.
  induct ls1.
  induct ls2.
  simplify.
  equality.

  simplify.
  equality.

  simplify.
  SearchRewrite (_ + 0).
  rewrite <- (plus_0_r (a)).
  rewrite <- plus_comm.
  SearchRewrite (_ + _). 
  rewrite fl_list_plus_nat.
  symmetry.
  rewrite fl_list_plus_nat.
  symmetry.
  specialize (IHls1 ls2).
  
  rewrite IHls1.
  linear_arithmetic.  
Qed.

Lemma red_max_dist : forall (ls1 ls2 : list nat), fold_left max (ls1 ++ ls2) 0 = max (fold_left max ls1 0) (fold_left max ls2 0).
Proof.
  induct ls1.
  induct ls2.
  simplify.
  equality.

  simplify.
  equality.

  simplify.
  SearchAbout max.
  
  rewrite fl_list_max_nat.
  symmetry.
  rewrite fl_list_max_nat.
  symmetry.

  specialize (IHls1 ls2).
  rewrite IHls1.
  SearchAbout max.

  
  rewrite <- Max.max_assoc.
  symmetry.
  rewrite <- Max.max_assoc.
  symmetry.
  f_equal.
  rewrite <- Max.max_comm .
  equality.
Qed.
Theorem mapReduce_partition_two : forall m r ls1 ls2, interp_mr (m, r) (ls1 ++ ls2) = interp_reduce r [interp_mr (m, r) ls1; interp_mr (m, r) ls2].
Proof.
  induct r.
  simplify.
  unfold interp_mr.
  simplify.

  
  SearchAbout map.
  rewrite map_app.
  rewrite red_add_dist.
  linear_arithmetic.

  unfold interp_mr.
  simplify.

  rewrite map_app.
  rewrite Max.max_0_l.
  rewrite red_max_dist.
  equality.
Qed.

Arguments app {_} _ _ .
Lemma app_conc : forall a (ls : list a) (b : a), b::ls = [b]++ls.
Proof.
  simplify.
  equality.
Qed.

Lemma lsls_partition : forall (lsls : list(list nat)) (a : list nat), fold_left app lsls a = fold_left app lsls [] ++ a.
Proof.
  
(*
  induct lsls.
  simplify.
  equality.

  simplify.
  SearchAbout app.
  cases a.
  simplify.
  rewrite IHlsls.
  SearchRewrite (_ ++ []).  
  rewrite app_nil_r.
  equality.

  *)
Admitted.


Theorem mapReduce_partition : forall m r lsls, interp_mr (m, r) (fold_left app lsls []) = interp_reduce r (List.map (interp_mr (m, r)) lsls).
Proof.
  induct lsls.
  simplify.
  unfold interp_mr.
  simplify.
  equality.
  
  simplify.

  rewrite lsls_partition.
  rewrite mapReduce_partition_two.
  rewrite IHlsls.
  rewrite app_conc.
  rewrite reduce_swap.

  cases r.
  simplify.
  rewrite <- (plus_0_r (interp_mr (m, Sum) a)).
  rewrite <- plus_comm.
  SearchRewrite (_ + _). 
  rewrite fl_list_plus_nat.

  symmetry.
  rewrite <- (plus_0_r (interp_mr (m, Sum) a)).
  rewrite <- (plus_comm (0) ( interp_mr (m, Sum) a)).
  SearchRewrite (_ + 0). 
  rewrite fl_list_plus_nat.
  simplify.
  linear_arithmetic.

  simplify.
  (*rewrite fl_list_max_nat.*)
  symmetry.
  rewrite fl_list_max_nat.
  simplify.
  rewrite Max.max_0_l.
  rewrite Max.max_comm.
  equality.
  
Qed.

(* For full credit, the code you turn in can't use [Admitted] or [admit] anymore! *)
