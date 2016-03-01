`(** * 6.887 Formal Reasoning About Programs, Spring 2016 - Pset 2 *)

Require Import Frap Pset2Sig.

Definition contribution_from (pr : increment_program) : nat :=
  match pr with
  | UnsetFlag => 1
  | Done => 1
  | _ => 0
  end.

Definition flag_set (pr : increment_program) : bool :=
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


Definition is_valid_turn (pr1 pr2: increment_program) (turn: bool) :=
   match pr1 with
     | SetFlag => match pr2 with
                    | _ => match turn with
                          | true => False
                          | false => True
                           end
                    end
     | SetTurn => match pr2 with
                    | _ => match turn with
                          | true => False
                          | false => True
                           end
                  end
     | ReadFlag => match pr2 with
                    |SetFlag => match turn with
                                  |true => True
                                  |false => False
                                 end
                    |SetTurn => match turn with
                                 |true => True
                                  |false => False
                                 end
                    |ReadFlag => match turn with
                                  |_ => True
                                 end
                    |ReadTurn => match turn with
                                  |_ => True
                                 end
                    |Read => match turn with
                                  |true => True
                                  |false => False
                                 end
                    |Write n => match turn with
                                  |true => True
                                  |false => False
                                 end
                    |UnsetFlag => match turn with
                                  |true => True
                                  |false => False
                                 end
                    |Done => match turn with
                                  |true => True
                                  |false => False
                                 end
                    end
  | ReadTurn => match pr2 with
                    |SetFlag => match turn with
                                  |true => True
                                  |false => False
                                 end
                    |SetTurn => match turn with
                                 |true => True
                                  |false => False
                                 end
                    |ReadFlag => match turn with
                                  |_ => True
                                 end
                    |ReadTurn => match turn with
                                  |_ => True
                                 end
                    |Read => match turn with
                                  |true => True
                                  |false => False
                                 end
                    |Write n => match turn with
                                  |true => True
                                  |false => False
                                 end
                    |UnsetFlag => match turn with
                                  |true => True
                                  |false => False
                                 end
                    |Done => match turn with
                                  |true => True
                                  |false => False
                                 end
                    end
  | Read => match pr2 with
                    |SetFlag => match turn with
                                  |true => True
                                  |false => False
                                 end
                    |SetTurn => match turn with
                                  |true => True
                                  |false => False
                                 end
                    |ReadFlag => match turn with
                                  |true => False
                                  |false => True
                                 end
                    |ReadTurn => match turn with
                                  |true => False
                                  |false => True
                                 end
                    |Read => False
                    |Write n => False
                    |UnsetFlag => False
                    |Done => match turn with
                                  |true => True
                                  |false => False
                                 end
                    end
  | Write _ => match pr2 with
                    |SetFlag => match turn with
                                  |true => True
                                  |false => False
                                 end
                    |SetTurn => match turn with
                                  |true => True
                                  |false => False
                                 end
                    |ReadFlag => match turn with
                                  |true => False
                                  |false => True
                                 end
                    |ReadTurn => match turn with
                                  |true => False
                                  |false => True
                                 end
                    |Read => False
                    |Write n => False
                    |UnsetFlag => False
                    |Done => match turn with
                                  |true => True
                                  |false => False
                                 end
                    end
  | UnsetFlag => match pr2 with
                    |SetFlag => match turn with
                                  |true => True
                                  |false => False
                                 end
                    |SetTurn => match turn with
                                  |true => True
                                  |false => False
                                 end
                    |ReadFlag => match turn with
                                  |true => False
                                  |false => True
                                 end
                    |ReadTurn => match turn with
                                  |true => False
                                  |false => True
                                 end
                    |Read => False
                    |Write n => False
                    |UnsetFlag => False
                    |Done => match turn with
                                  |true => True
                                  |false => False
                                 end
                    end
  | Done => match pr2 with
                    |SetFlag => match turn with
                                  |true => True
                                  |false => False
                                 end
                    |SetTurn => match turn with
                                  |true => True
                                  |false => False
                                 end
                    |ReadFlag => match turn with
                                  |true => False
                                  |false => True
                                 end
                    |ReadTurn => match turn with
                                 |true => False
                                  |false => True
                                 end
                    |Read => match turn with
                                  |true => False
                                  |false => True
                                 end
                    |Write n => match turn with
                                  |true => False
                                  |false => True
                                 end
                    |UnsetFlag => match turn with
                                  |true => False
                                  |false => True
                                 end
                    |Done => True
                    end
   end.

Definition in_cs (pr : increment_program) : bool :=
  match pr with
  | SetFlag => false
  | SetTurn => false 
  | ReadFlag => false
  | ReadTurn => false
  | Read => true
  | Write n => true
  | UnsetFlag => true
  | Done => false
  end.           
Definition shared_from_private (pr1 pr2 : increment_program) (turn : bool):=
  {| Flag1 := flag_set pr1;
     Flag2 := flag_set pr2;
     Turn := turn;
     Global := contribution_from pr1 + contribution_from pr2 |}.

(*both not in CS*)
Definition instruction_ok (self other : increment_program) :=
  match self with
  | SetFlag => True
  | SetTurn => True
  | ReadFlag => True
  | ReadTurn => True
  | Read => in_cs other = false 
  | Write n => in_cs other = false /\ n = contribution_from other
  | UnsetFlag => in_cs other = false 
  | Done => True
  end.

Inductive increment2_invariant :
  threaded_state inc_state (increment_program * increment_program) -> Prop :=
| Inc2Inv : forall pr1 pr2 turn,
  instruction_ok pr1 pr2
  -> instruction_ok pr2 pr1
  -> is_valid_turn pr1 pr2 turn
  -> increment2_invariant {| Shared := {|Flag1 := flag_set pr1;
                                         Flag2 := flag_set pr2;
                                         Turn := turn;
                                         Global := contribution_from pr1 + contribution_from pr2|}; Private := (pr1, pr2) |}.


Definition shared_from_private1 (pr1 pr2 : increment_program) (turn : bool) :=
  {|Flag1 := flag_set pr1;
    Flag2 := flag_set pr2;
    Turn := turn;
    Global := contribution_from pr1 + contribution_from pr2 |}.

Lemma Inc2Inv' : forall sh pr1 pr2 turn,
   sh = shared_from_private1 pr1 pr2 turn 
   -> instruction_ok pr1 pr2
   -> instruction_ok pr2 pr1
   -> is_valid_turn pr1 pr2 turn
   -> increment2_invariant {| Shared := sh; Private := (pr1, pr2) |}.
Proof.
  intros.
  rewrite H.
  apply Inc2Inv; assumption.
Qed.

Theorem increment2_invariant_ok : invariantFor increment2_sys increment2_invariant.
Proof.
  apply invariant_induction; simplify.
  invert H.
  invert H0.
  invert H1.

  eapply Inc2Inv'.

  unfold shared_from_private1.
  simplify.
  equality.

  simplify.
  propositional.

  simplify.
  propositional.

  simplify.
  propositional.

  invert H.
  invert H0.
  invert H7; simplify.

  cases pr2; simplify.
  
  eapply Inc2Inv'; unfold shared_from_private1; simplify.
  equality.
  equality.
  equality.

  apply H3.

  eapply Inc2Inv'; unfold shared_from_private1; simplify.
  equality.
  equality.
  equality.
  equality.

  eapply Inc2Inv'; unfold shared_from_private1; simplify.
  equality.
  equality.
  equality.
  equality.

  eapply Inc2Inv'; unfold shared_from_private1; simplify.
  equality.
  equality.
  equality.
  equality.

  eapply Inc2Inv'; unfold shared_from_private1; simplify.
  equality.
  equality.
  equality.
  equality.

  eapply Inc2Inv'; unfold shared_from_private1; simplify.
  equality.
  equality.
  equality.
  equality.


  eapply Inc2Inv'; unfold shared_from_private1; simplify.
  equality.
  equality.
  equality.
  equality.


  eapply Inc2Inv'; unfold shared_from_private1; simplify.
  equality.
  equality.
  equality.
  equality.

  eapply Inc2Inv'; unfold shared_from_private1; simplify.
  equality.
  equality.
  equality.
  
  cases pr2; equality.

  eapply Inc2Inv'; unfold shared_from_private1; simplify.
  equality.
  equality.
  equality.

  apply H3.
  simplify.
  eapply Inc2Inv'; unfold shared_from_private1; simplify.
  equality.
  unfold in_cs.
  cases pr2; equality.

  unfold instruction_ok.
  cases pr2; trivial.

  unfold in_cs.
  simplify.
  equality.

  cases pr2.
  apply H3.
  apply H3.
  simplify.
  equality.

  simplify.
  simplify.
  equality.

  simplify.
  equality.

  simplify.
  equality.
  
  simplify.
  equality.
  apply H3.

  eapply Inc2Inv'; unfold shared_from_private1; simplify.
  equality.
  equality.
  equality.

  cases pr2; trivial.
  
  eapply Inc2Inv'; unfold shared_from_private1; simplify.
  equality.
  unfold in_cs.
  cases pr2; trivial.
  equality.
  equality.
  simplify.
  equality.

  unfold instruction_ok.
  cases pr2; trivial.

  unfold in_cs.
  equality.

  unfold in_cs.
  unfold contribution_from.
  equality.

  unfold in_cs.
  equality.

  cases pr2; trivial.

  eapply Inc2Inv'; unfold shared_from_private1; simplify.
  equality.
  equality.
  equality.

  cases pr2; trivial.

  eapply Inc2Inv'; unfold shared_from_private1; simplify.
  unfold contribution_from.
  cases pr2.
  simplify.

  invert H1.
  equality.

  invert H1.
  unfold contribution_from.
  equality.

  invert H1.
  unfold contribution_from.
  equality.

  invert H1.
  unfold contribution_from.
  equality.

  invert H1.
  unfold contribution_from.
  equality.
  
  equality.
  equality.

  invert H1.
  unfold contribution_from.
  equality.

  eapply H1.
  unfold instruction_ok.
  cases pr2; trivial.
  invert H1.
  invert H.
  apply H3.

  eapply Inc2Inv'; unfold shared_from_private1; simplify.
  unfold contribution_from.
  equality.
  equality.

  unfold instruction_ok.
  cases pr2; trivial.
  invert H1.
  cases pr2; repeat apply H3.
  equality.
  equality.
  equality.
  equality.
 
  (* *)
  (**** THIS is where I was stuck, I originally had eapply, and then invert, 
   but that lead to the weir turn = true, turn = false cases
   switching the order helped me avoid that.****)
  invert H7.
  eapply Inc2Inv'; unfold shared_from_private1; simplify.
 
  simplify.
  equality.

  unfold instruction_ok.
  simplify.
  cases pr1.
  equality.
  equality.
  equality.
  equality.
  equality.
  trivial.
  equality.
  equality.
  equality.
  
  unfold is_valid_turn.
  
  cases pr1.
  simplify.
  simplify.
  apply H3.
  simplify.
  apply H3.
  simplify.
  apply H3.
  simplify.
  apply H3.
  simplify.
  apply H3.
  simplify.
  apply H3.
  simplify.
  apply H3.
  simplify.
  apply H3.

  eapply Inc2Inv'; unfold shared_from_private1; simplify.

  simplify.
  equality.

  unfold instruction_ok.

  cases pr1; simplify; equality.
  equality.
  unfold is_valid_turn.
  cases pr1; equality.

  eapply Inc2Inv'; unfold shared_from_private1; simplify.

  simplify.
  equality.

  unfold instruction_ok.
  cases pr1; simplify; equality.
  equality.

  unfold is_valid_turn.
  cases pr1; simplify; equality.

  eapply Inc2Inv'; unfold shared_from_private1; simplify.

  simplify.
  equality.

  unfold instruction_ok.
  cases pr1; simplify; equality.

  unfold in_cs.
  cases pr1; simplify; equality.

  unfold is_valid_turn.
  cases pr1; simplify; equality.

  eapply Inc2Inv'; unfold shared_from_private1; simplify.
  simplify.
  equality.

  unfold instruction_ok.
  cases pr1; simplify; equality.

  equality.

  unfold is_valid_turn.
  cases pr1; simplify; equality.

  eapply Inc2Inv'; unfold shared_from_private1; simplify.
  equality.

  unfold instruction_ok.
  cases pr1; simplify; equality.

  unfold in_cs.
  cases pr1; simplify; equality.

  unfold is_valid_turn.
  cases pr1; simplify; equality.

  eapply Inc2Inv'; unfold shared_from_private1; simplify.
  equality.

  unfold instruction_ok.
  cases pr1;simplify; equality.

  unfold contribution_from.

  cases pr1; simplify; equality.

  unfold is_valid_turn.
  cases pr1; simplify; equality.

  eapply Inc2Inv'; unfold shared_from_private1; simplify.
  unfold contribution_from.
  cases pr1; simplify.
  invert H2.
  equality.
  invert H2.
  equality.
  invert H2.
  equality.
  invert H2.
  equality.
  invert H2.
  equality.
  invert H2.
  equality.
  invert H2.
  equality.
  invert H2.
  equality.

  unfold instruction_ok.
  cases pr1; simplify; equality.

  unfold in_cs.
  cases pr1; simplify; equality.

  unfold is_valid_turn.
  cases pr1; simplify; equality.

  eapply Inc2Inv'; unfold shared_from_private1; simplify.
  equality.
  unfold instruction_ok.
  cases pr1; simplify; equality.

  equality.

  unfold is_valid_turn.
  cases pr1; simplify; equality.

Qed.
  
  


Theorem increment2_ok :
  invariantFor increment2_sys increment2_correct.
Proof.
 
  apply invariant_weaken with (invariant1 := increment2_invariant).
  apply increment2_invariant_ok.
  simplify.

  invert H.
  unfold increment2_correct; simplify.
  invert H.
  simplify.
  equality.
Qed.
(*fcn that takes in pr1 pr2 turn and return prop *)