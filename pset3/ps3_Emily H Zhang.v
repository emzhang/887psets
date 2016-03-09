(** * 6.887 Formal Reasoning About Programs, Spring 2016 - Pset 3 *)

Require Import Frap Pset3Sig.

Set Implicit Arguments.

Lemma l1: forall  (l : list rule) (x : var) (b : bool), forall (pm pm': fmap var bool), applyRules pm pm' l $? x = Some b -> pm' $? x = None -> exists r: rule, ((r.(Conclusion).(AssumedPredicate)), (r.(Conclusion).(AssumedToBe))) = (x, b) /\ In r l /\ assumptionsHold pm (Assumptions r) = true.
Proof.
  induct l.
  unfold applyRules.
  assert (forall (b : bool), None = Some b -> False).
  intros. equality.
  simplify.
  specialize (H b).
  contradiction H.
  rewrite <- H0.
  rewrite -> H1.
  equality.
  simplify.
  
  cases (AssumedPredicate (Conclusion a) ==v x).
  cases b.
  intros.
  
  
 
  (*unfold In.
  SearchAbout (_ :: _).
  exact(in_eq (A:=rule) a l).*)

  assert ((applyRule pm pm' a) $? x = None).
  admit.

  cases (AssumedToBe (Conclusion a)).
  exists a.
  propositional.
  invert e.
  invert Heq.
  equality.

  admit. (* prove assumptions hold *)

  (* TODO figure out syntax *)
  specialize (IHl x true pm (applyRule pm pm' a) H H1).
  assert (forall r, In r l -> a = r \/ In r l).
  intros.
  right. assumption.
  destruct IHl.
  specialize (H2 x0).
  exists x0.
  propositional.

  cases (AssumedToBe (Conclusion a)).
  exists a.
  propositional.
  invert e.
  rewrite -> Heq.
  assert ( False).
  admit.
  contradiction H1.

  (* again assumptions hold*)
  admit.

  exists a.
  propositional. 
  invert e.
  invert Heq.
  equality.

  (* again assmptions*)
  admit.

  specialize (IHl x b pm (applyRule pm pm' a)).
  specialize (IHl H).

  assert (applyRule pm pm' a $? x = None).
  unfold applyRule.
  (*can't figure out how to do cases on assumptionsHold pm asn :( :( *)
  cases a.
  cases (assumptionsHold pm Assumptions).
  SearchAbout (fmap).
  rewrite (lookup_add_ne (pm') (k:=AssumedPredicate Conclusion) (k':=x) (AssumedToBe Conclusion)).
  assumption.
  admit.

  apply H0.
  specialize (IHl H1).
  destruct IHl.
  exists x0.
  propositional.

Qed.

Theorem predicate_abstraction_simulates : forall pc state action
  (pc0 : pc) (st0 : state)
  (actionOf : pc -> action -> pc -> Prop)
  (doAction : action -> state -> state -> Prop)
  (pa : predicate_abstraction state action),
  predicate_abstraction_sound doAction pa
  -> simulates (paR pa)
               (actionSys pc0 st0 actionOf doAction)
               (predicate_abstract pc0 actionOf pa).
Proof.
  simplify.
  econstructor.
  intros.
  simplify.
  propositional.
  exists (pc0, $0).
  propositional.
  invert H1; simplify.
  eapply PaR.
  simplify.
  invert H0.

  simplify.
  invert H1.
  propositional.
  Check $0.
  destruct st2.
  exists (pc2, match (Rules pa) $? act with
            | None => $0
            | Some rs => applyRules f $0 rs
                end).
  propositional.
  eapply PaR.
  simplify.
  unfold predicate_abstraction_sound in H.
  unfold ruleAccurate in H.
  unfold assertionAccurate in H.
  cases (Rules pa $? act).
  cases (Predicates pa $? x).
  
  
  (* prove this as lemma1 *)
  
  assert (applyRules f $0 l $? x = Some b -> exists r : rule, ((r.(Conclusion).(AssumedPredicate)), (r.(Conclusion).(AssumedToBe))) = (x, b) /\ In r l).
  simplify.
  
  admit.
  
  specialize (H4 H1).
  invert H4.
  specialize (H act l x0).
  specialize (H Heq).
  destruct H5.
  specialize (H H5).
  specialize (H st3 st4).
  (*prove this as lemma 2*)
  assert (assumptionsAccurate (Predicates pa) (Assumptions x0) st3).
  admit.
  specialize (H H6).
  specialize (H H3).
  invert H4.
  rewrite Heq0 in H.
  apply H.
  
  SearchAbout $0.
  (*prove as lemma1*)
  assert (applyRules f $0 l $? x = Some b -> exists r : rule, ((r.(Conclusion).(AssumedPredicate)), (r.(Conclusion).(AssumedToBe))) = (x, b) /\ In r l).
  
  admit.
  specialize (H4 H1).
  invert H4.
  specialize (H act l x0).
  specialize (H Heq).
  destruct H5.
  specialize (H H5).
  specialize (H st3 st4).

  (*being proving false*)
  (*prove as lemma2*)
  assert (assumptionsAccurate (Predicates pa) (Assumptions x0) st3). 
  admit.
  
  specialize (H H6).
  specialize (H H3).
  invert H4.
  rewrite Heq0 in H.
  apply H.


  rewrite (lookup_empty (A:=var) bool x) in H1.
  assert (forall (b : bool), None = Some b -> False).
  intros. equality.
  specialize (H4 b).
  contradiction H4.
  (* end proving false *)

  econstructor.
  invert H0.
  apply H2.
Qed.


(* Optional part: using predicate abstraction for another example *)

Import Program2 ZArith.


(* This is not the right abstraction. :-) *)
Definition sys_pa : predicate_abstraction state action := {|
  Predicates := $0;
  Rules := $0 $+ (LockOK, [])
              $+ (AssignA, [])
              $+ (IfFalse, [])
              $+ (IfTrue, [])
              $+ (UnlockOK, [])
              $+ (IncA, [])
              $+ (WhileFalse, [])
              $+ (WhileTrue, [])
|}.

Opaque Zplus. (* Important to keep Coq from trying too hard to help and
               * unfolding the definition of addition for integers! *)

Theorem sys_ok : forall np npo,
  invariantFor (sys np npo) (fun st => fst st = Done -> (snd st).(HasLock) = false).
Proof.
Admitted.
