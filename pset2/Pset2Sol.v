(** * 6.887 Formal Reasoning About Programs, Spring 2016 - Pset 2 *)

Require Import Frap Pset2Sig.

Set Implicit Arguments.


(* Authors: Adam Chlipala (adamc@csail.mit.edu), Peng Wang (wangpeng@csail.mit.edu) *)

Definition flag_for (pr : increment_program) : bool :=
  match pr with
    | SetFlag => false
    | SetTurn => true
    | ReadFlag => true
    | ReadTurn => true
    | Read => true
    | Write _ => true
    | UnsetFlag => true
    | Done => false
  end.

Definition contribution_from (pr : increment_program) : nat :=
  match pr with
  | UnsetFlag => 1
  | Done => 1
  | _ => 0
  end.

Definition in_critical_section (pr : increment_program) : Prop :=
  match pr with
  | Read => True
  | Write _ => True
  | UnsetFlag => True
  | _ => False
  end.

Definition instruction_ok (self other : increment_program) :=
  match self with
    | Write n => n = contribution_from other
    | _ => True
  end.

Inductive increment2_invariant : threaded_state inc_state (increment_program * increment_program) -> Prop :=
| Inc2Inv : forall tu pr1 pr2,
  instruction_ok pr1 pr2
  -> instruction_ok pr2 pr1
  -> (in_critical_section pr1
      -> (pr2 = SetFlag \/ pr2 = Done)
         \/ (tu = false /\ (pr2 = ReadFlag \/ pr2 = ReadTurn))
         \/ pr2 = SetTurn)
  -> (in_critical_section pr2
      -> (pr1 = SetFlag \/ pr1 = Done)
         \/ (tu = true /\ (pr1 = ReadFlag \/ pr1 = ReadTurn))
         \/ pr1 = SetTurn)
  -> increment2_invariant {| Shared :=
                               {| Flag1 := flag_for pr1; Flag2 := flag_for pr2; Turn := tu;
                                  Global := contribution_from pr1 + contribution_from pr2 |};
                             Private := (pr1, pr2) |}.

Lemma Inc2Inv' : forall sh tu pr1 pr2,
  sh = {| Flag1 := flag_for pr1; Flag2 := flag_for pr2; Turn := tu;
          Global := contribution_from pr1 + contribution_from pr2 |}
  -> instruction_ok pr1 pr2
  -> instruction_ok pr2 pr1
  -> (in_critical_section pr1
      -> (pr2 = SetFlag \/ pr2 = Done)
         \/ (tu = false /\ (pr2 = ReadFlag \/ pr2 = ReadTurn))
         \/ pr2 = SetTurn)
  -> (in_critical_section pr2
      -> (pr1 = SetFlag \/ pr1 = Done)
         \/ (tu = true /\ (pr1 = ReadFlag \/ pr1 = ReadTurn))
         \/ pr1 = SetTurn)
  -> increment2_invariant {| Shared := sh; Private := (pr1, pr2) |}.
Proof.
  simplify.
  rewrite H.
  apply Inc2Inv; assumption.
Qed.

Theorem increment2_ok :
  invariantFor increment2_sys increment2_correct.
Proof.
  apply invariant_weaken with (invariant1 := increment2_invariant).

  apply invariant_induction; simplify.

  invert H.
  invert H0.
  invert H1.
  eapply Inc2Inv'.
  equality.
  simplify.
  trivial.
  simplify.
  trivial.
  simplify.
  propositional.
  simplify.
  propositional.

  invert H.
  invert H0.

  invert H8; simplify.

  eapply Inc2Inv'.
  simplify.
  equality.
  simplify.
  trivial.
  cases pr2; simplify; trivial.
  simplify.
  propositional.
  propositional.

  eapply Inc2Inv'.
  simplify.
  equality.
  simplify.
  trivial.
  cases pr2; simplify; trivial.
  simplify.
  propositional.
  propositional.

  eapply Inc2Inv'.
  simplify.
  equality.
  simplify.
  trivial.
  cases pr2; simplify; trivial.
  simplify.
  propositional.
  equality.

  eapply Inc2Inv'.
  simplify.
  equality.
  simplify.
  trivial.
  cases pr2; simplify; trivial.
  simplify.
  cases pr2; simplify; equality.
  cases pr2; simplify; equality.

  eapply Inc2Inv'.
  simplify.
  equality.
  simplify.
  trivial.
  cases pr2; simplify; trivial.
  simplify.
  cases pr2; simplify; equality.
  cases pr2; simplify; equality.

  eapply Inc2Inv'.
  simplify.
  equality.
  simplify.
  trivial.
  cases pr2; simplify; trivial.
  simplify.
  cases pr2; simplify; equality.
  cases pr2; simplify; equality.

  eapply Inc2Inv'.
  simplify.
  equality.
  simplify.
  trivial.
  cases pr2; simplify; trivial.
  simplify.
  cases pr2; simplify; equality.
  cases pr2; simplify; equality.

  eapply Inc2Inv'.
  simplify.
  rewrite H1.
  equality.
  simplify.
  trivial.
  cases pr2; simplify; trivial.
  equality.
  simplify.
  cases pr2; simplify; equality.
  cases pr2; simplify; equality.

  eapply Inc2Inv'.
  simplify.
  equality.
  simplify.
  trivial.
  cases pr2; simplify; trivial.
  cases pr2; simplify; equality.
  cases pr2; simplify; equality.

  invert H8; simplify.

  eapply Inc2Inv'.
  simplify.
  equality.
  cases pr1; simplify; trivial.
  simplify.
  trivial.
  simplify.
  propositional.
  propositional.

  eapply Inc2Inv'.
  simplify.
  equality.
  cases pr1; simplify; trivial.
  simplify.
  trivial.
  simplify.
  propositional.
  cases pr1; simplify; propositional.

  eapply Inc2Inv'.
  simplify.
  equality.
  cases pr1; simplify; trivial.
  simplify.
  trivial.
  simplify.
  cases pr1; simplify; equality.
  equality.

  eapply Inc2Inv'.
  simplify.
  equality.
  cases pr1; simplify; trivial.
  simplify.
  trivial.
  simplify.
  cases pr1; simplify; equality.
  cases pr1; simplify; equality.

  eapply Inc2Inv'.
  simplify.
  equality.
  cases pr1; simplify; trivial.
  simplify.
  trivial.
  simplify.
  cases pr1; simplify; equality.
  cases pr1; simplify; equality.

  eapply Inc2Inv'.
  simplify.
  equality.
  cases pr1; simplify; trivial.
  simplify.
  trivial.
  simplify.
  cases pr1; simplify; equality.
  cases pr1; simplify; equality.

  eapply Inc2Inv'.
  simplify.
  equality.
  cases pr1; simplify; trivial.
  simplify.
  trivial.
  simplify.
  cases pr1; simplify; equality.
  cases pr1; simplify; equality.
  cases pr1; simplify; equality.

  eapply Inc2Inv'.
  simplify.
  f_equal.
  linear_arithmetic.
  cases pr1; simplify; trivial.
  equality.
  simplify.
  trivial.
  simplify.
  cases pr1; simplify; equality.
  cases pr1; simplify; equality.

  eapply Inc2Inv'.
  simplify.
  equality.
  cases pr1; simplify; trivial.
  simplify.
  trivial.
  cases pr1; simplify; equality.
  cases pr1; simplify; equality.
  
  invert 1.
  unfold increment2_correct; simplify.
  invert H.
  simplify.
  equality.
Qed.
