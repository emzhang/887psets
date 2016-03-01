(** * 6.887 Formal Reasoning About Programs, Spring 2016 - Pset 1 *)

Require Import Frap Pset1Sig.

(* Authors: Peng Wang (wangpeng@csail.mit.edu), Adam Chlipala (adamc@csail.mit.edu) *)


(** * MapReduce *)

Lemma add_positive : forall n m,
  n > 0
  -> m > 0
  -> n + m > 0.
Proof.
  linear_arithmetic.
Qed.

Theorem allPositive_ok : forall m x,
  allPositive m
  -> x > 0
  -> interp_map m x > 0.
Proof.
  induct m; simplify; propositional.

  apply add_positive.
  apply IHm1.
  trivial.
  trivial.
  apply IHm2.
  trivial.
  trivial.

  apply IHm1.
  trivial.
  apply IHm2.
  trivial.
  trivial.
Qed.

Lemma fold_left_swap' : forall A (f : A -> A -> A),
  (forall x y : A, f x y = f y x)
  (* Operator is commutative. *)
  -> (forall x y z : A, f (f x y) z = f x (f y z))
  (* Operator is associative. *)
  -> forall ls a b,
      fold_left f ls (f a b) = f (fold_left f ls a) b.
Proof.
  induct ls; simplify; try equality.
Qed.

Lemma fold_left_swap : forall A (f : A -> A -> A),
  (forall x y : A, f x y = f y x)
  (* Operator is commutative. *)
  -> (forall x y z : A, f (f x y) z = f x (f y z))
  (* Operator is associative. *)
  -> forall ls1 ls2 init,
      fold_left f (ls1 ++ ls2) init = fold_left f (ls2 ++ ls1) init.
Proof.
  induct ls1; simplify.
  {
    rewrite app_nil_r.
    equality.
  }
  {
    rewrite IHls1.
    rewrite fold_left_app.
    rewrite fold_left_app.
    simplify.
    f_equal.
    apply fold_left_swap'; trivial.
  }
Qed.

Lemma reduce_swap : forall e ls1 ls2,
  interp_reduce e (ls1 ++ ls2) = interp_reduce e (ls2 ++ ls1).
Proof.
  unfold interp_reduce; simplify.
  cases e; apply fold_left_swap; simplify; linear_arithmetic.
Qed.

Lemma interp_swap : forall e ls1 ls2, interp_mr e (ls1 ++ ls2) = interp_mr e (ls2 ++ ls1).
Proof.
  induct e; simplify.
  unfold interp_mr; simplify.
  rewrite map_app.
  rewrite map_app.
  apply reduce_swap.
Qed.

Lemma fold_left_par' : forall A (f : A -> A -> A) (rzero : A),
    (forall x y z : A, f (f x y) z = f x (f y z))
    (* Operator is associative. *)
    -> (forall x, f x rzero = x)
    (* [rzero] is a right zero for operator. *)
    -> forall ls init, fold_left f ls init = f init (fold_left f ls rzero).
Proof.
  induct ls; simplify; equality.
Qed.

Lemma fold_left_par : forall A (f : A -> A -> A) (rzero : A),
    (forall x y z : A, f (f x y) z = f x (f y z))
    (* Operator is associative. *)
    -> (forall x, f x rzero = x)
    (* [rzero] is a right zero for operator. *)
    -> forall ls1 ls2 init,
        fold_left f (ls1 ++ ls2) init = f (fold_left f ls1 init) (fold_left f ls2 rzero).
Proof.
  induct ls1; simplify; try equality.
  apply fold_left_par'.
  trivial.
  trivial.
Qed.

Lemma mapReduce_partition_two : forall m r ls1 ls2,
    interp_mr (m, r) (ls1 ++ ls2) = interp_reduce r [interp_mr (m, r) ls1; interp_mr (m, r) ls2].
Proof.
  unfold interp_mr; simplify.
  cases r; simplify; rewrite map_app; apply fold_left_par; linear_arithmetic.
Qed.

Arguments app {_} _ _ .

Lemma mapReduce_partition' : forall m r lsls init,
    interp_mr (m, r) (fold_left app lsls init)
    = interp_reduce r (interp_mr (m, r) init :: map (interp_mr (m, r)) lsls).
Proof.
  induct lsls; simplify.
  {
    unfold interp_reduce; simplify.
    cases r; linear_arithmetic.
  }
  {
    rewrite IHlsls.
    rewrite mapReduce_partition_two.
    cases r; simplify; linear_arithmetic.
  }
Qed.

Lemma mapReduce_partition : forall m r lsls,
    interp_mr (m, r) (fold_left app lsls []) = interp_reduce r (map (interp_mr (m, r)) lsls).
Proof.
  induct lsls; simplify; try equality.
  apply mapReduce_partition'.
Qed.


(** * Constant propagation *)

Theorem constPropArith_ok : forall v1 v2 e,
  (forall x n, v1 $? x = Some n -> v2 $? x = Some n)
  -> interp (constPropArith e v1) v2 = interp e v2.
Proof.
  induct e; simplify; propositional.

  cases (v1 $? x); simplify; try equality.
  rewrite (H x n); simplify; equality.

  cases (constPropArith e1 v1); simplify; try equality.
  cases (constPropArith e2 v1); simplify; equality.

  cases (constPropArith e1 v1); simplify; try equality.
  cases (constPropArith e2 v1); simplify; equality.

  cases (constPropArith e1 v1); simplify; try equality.
  cases (constPropArith e2 v1); simplify; equality.
Qed.

Theorem effectOf_ok : forall c v1 v2,
  (forall x n, v1 $? x = Some n -> v2 $? x = Some n)
  -> (forall x n, effectOf c v1 $? x = Some n
                  -> exec c v2 $? x = Some n).
Proof.
  induct c; simplify; try equality.

  apply H.
  trivial.

  cases (constPropArith e v1).
  rewrite <- (constPropArith_ok v1).
  cases (x ==v x0); simplify; try equality.
  rewrite Heq.
  simplify.
  trivial.
  apply H.
  trivial.
  trivial.

  cases (x ==v x0); simplify; try equality.
  apply H.
  trivial.

  cases (x ==v x0); simplify; try equality.
  apply H.
  trivial.

  cases (x ==v x0); simplify; try equality.
  apply H.
  trivial.

  cases (x ==v x0); simplify; try equality.
  apply H.
  trivial.

  apply (IHc2 (effectOf c1 v1)).
  apply IHc1.
  trivial.
  trivial.
Qed.

Theorem constProp_ok : forall c v1 v2,
  (forall x n, v1 $? x = Some n -> v2 $? x = Some n)
  -> exec (constProp c v1) v2 = exec c v2.
Proof.
  induct c; simplify; propositional.

  rewrite constPropArith_ok.
  trivial.
  trivial.

  rewrite IHc1.
  rewrite IHc2.
  trivial.
  trivial.
  apply effectOf_ok.
  trivial.
  trivial.

  rewrite constPropArith_ok.
  apply selfCompose_extensional.
  simplify.
  apply IHc.
  simplify.
  equality.
  trivial.
Qed.  

Theorem constProp_ok0 : forall c v,
  exec (constProp c $0) v = exec c v.
Proof.
  simplify.
  apply constProp_ok.
  simplify.
  equality.
Qed.
