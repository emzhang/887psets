(** * 6.887 Formal Reasoning About Programs, Spring 2016 - Pset 3 *)

Require Import Frap Pset3Sig.

Set Implicit Arguments.


(* Authors: Adam Chlipala (adamc@csail.mit.edu), Peng Wang (wangpeng@csail.mit.edu) *)


Lemma assumptionsHold_sound : forall state prs (st : state) pm,
    (forall x b, pm $? x = Some b
               -> match prs $? x with
                  | Some pr => pr st <-> b = true
                  | None => False
                  end)
  -> forall asms, assumptionsHold pm asms = true
  -> assumptionsAccurate prs asms st.
Proof.
  induct asms; simplify; propositional.

  cases (assertionHolds pm a); simplify; try equality.
  unfold assertionHolds, assertionAccurate in *.
  cases a; simplify.
  cases (pm $? AssumedPredicate); try equality.
  cases b.
  cases AssumedToBe; try equality.
  apply H in Heq0.
  cases (prs $? AssumedPredicate); propositional.
  cases AssumedToBe; try equality.
  apply H in Heq0.
  cases (prs $? AssumedPredicate); propositional.
  apply H.
  assumption.

  cases (assertionHolds pm a); simplify; equality.
Qed.

Lemma applyRule_sound : forall state (doIt : state -> state -> Prop)
                               prs x b st st' r pm pm',
  (forall x b, pm $? x = Some b
               -> match prs $? x with
                  | Some pr => pr st <-> b = true
                  | None => False
                  end)
  -> (forall x b, pm' $? x = Some b
                  -> match prs $? x with
                     | Some pr => pr st' <-> b = true
                     | None => False
                     end)
  -> applyRule pm pm' r $? x = Some b
  -> ruleAccurate prs doIt r
  -> doIt st st'
  -> match prs $? x with
     | Some pr => pr st' <-> b = true
     | None => False
     end.
Proof.
  unfold applyRule; simplify.
  cases r.
  cases (assumptionsHold pm Assumptions).
  cases (AssumedToBe Conclusion).

  cases (x ==v AssumedPredicate Conclusion); simplify.
  invert H1.
  unfold ruleAccurate in H2; simplify.
  apply H2 in H3.
  unfold assertionAccurate in H3.
  rewrite Heq0 in H3.
  cases (prs $? AssumedPredicate Conclusion); propositional.
  eapply assumptionsHold_sound.
  eassumption.
  assumption.
  apply H0; assumption.
  
  cases (x ==v AssumedPredicate Conclusion); simplify.
  invert H1.
  unfold ruleAccurate in H2; simplify.
  apply H2 in H3.
  unfold assertionAccurate in H3.
  rewrite Heq0 in H3.
  cases (prs $? AssumedPredicate Conclusion); propositional.
  eapply assumptionsHold_sound.
  eassumption.
  assumption.
  apply H0; assumption.

  apply H0; assumption.
Qed.

Lemma applyRules_sound' : forall state (doIt : state -> state -> Prop)
  (prs : fmap var (state -> Prop)) x b st st' pm,
  (forall x b, pm $? x = Some b
       -> match prs $? x with
          | Some pr => pr st <-> b = true
          | None => False
          end)
  -> doIt st st'
  -> forall rs pm', (forall r, In r rs -> ruleAccurate prs doIt r)
  -> applyRules pm pm' rs $? x = Some b
  -> (forall x b, pm' $? x = Some b
                  -> match prs $? x with
                     | None => False
                     | Some pr => pr st' <-> b = true
                     end)
  -> match prs $? x with
     | None => False
     | Some pr => pr st' <-> b = true
     end.
Proof.
  induct rs; simplify.

  apply H3.
  assumption.

  eapply IHrs; simplify.
  apply H1.
  propositional.
  eassumption.
  eapply applyRule_sound.
  apply H.
  eassumption.
  eassumption.
  apply H1; propositional.
  assumption.
Qed.

Theorem applyRules_sound : forall state (doIt : state -> state -> Prop)
  (prs : fmap var (state -> Prop)) x b st st' rs pm,
  (forall r, In r rs -> ruleAccurate prs doIt r)
  -> (forall x b, pm $? x = Some b
       -> match prs $? x with
          | Some pr => pr st <-> b = true
          | None => False
          end)
  -> applyRules pm $0 rs $? x = Some b
  -> doIt st st'
  -> match prs $? x with
     | None => False
     | Some pr => pr st' <-> b = true
     end.
Proof.
  simplify.
  eapply applyRules_sound'.
  eassumption.
  eassumption.
  eassumption.
  eassumption.
  simplify.
  equality.
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
  constructor; simplify.

  propositional; subst.
  exists (pc0, $0); propositional.
  constructor; simplify.
  equality.

  invert H1.
  invert H0.
  exists (pc2, match pa.(Rules) $? act with
               | None => $0
               | Some rs => applyRules pm $0 rs
               end); propositional.
  constructor; simplify.
  unfold predicate_abstraction_sound in H.
  cases (Rules pa $? act); simplify; try equality.
  eapply applyRules_sound.
  simplify.
  eapply H.
  eassumption.
  eassumption.
  eassumption.
  assumption.
  assumption.

  constructor; assumption.
Qed.


(* Optional part: using predicate abstraction for another example *)

Import Program2 ZArith.


Definition tr := {|AssumedPredicate := "np = npo";
                   AssumedToBe := true|}.
Definition fa := {|AssumedPredicate := "np = npo";
                   AssumedToBe := false|}.

Definition establish := [{|Assumptions := []; Conclusion := tr |}].
Definition preserve := [{|Assumptions := [tr]; Conclusion := tr |};
                         {|Assumptions := [fa]; Conclusion := fa |}].
Definition falsify := [{|Assumptions := [tr]; Conclusion := fa |}].

Definition locked := {|AssumedPredicate := "locked";
                       AssumedToBe := true|}.
Definition unlocked := {|AssumedPredicate := "locked";
                         AssumedToBe := false|}.
Definition take_lock := [{|Assumptions := []; Conclusion := locked |}].
Definition release_lock := [{|Assumptions := []; Conclusion := unlocked |}].
Definition preserve_lock := [{|Assumptions := [locked]; Conclusion := locked |};
                              {|Assumptions := [unlocked]; Conclusion := unlocked |}].
Definition while_false := [{|Assumptions := [fa]; Conclusion := locked |};
                            {|Assumptions := [tr; locked]; Conclusion := locked |}].

Definition sys_pa : predicate_abstraction state action := {|
  Predicates := $0 $+ ("np = npo", fun st => st.(NP) = st.(NPO))
                   $+ ("locked", fun st => st.(HasLock) = true);
  Rules := $0 $+ (LockOK, preserve ++ take_lock)
              $+ (AssignA, establish ++ preserve_lock)
              $+ (IfFalse, preserve ++ preserve_lock)
              $+ (IfTrue, preserve ++ preserve_lock)
              $+ (UnlockOK, preserve ++ release_lock)
              $+ (IncA, falsify ++ preserve_lock)
              $+ (WhileFalse, while_false)
              $+ (WhileTrue, preserve ++ preserve_lock)
|}.

Opaque Zplus.

Theorem sys_ok : forall np npo,
  invariantFor (sys np npo) (fun st => fst st = Unlock2 -> (snd st).(HasLock) = true).
Proof.
  simplify.
  eapply invariant_weaken.
  eapply invariant_simulates.
  eapply predicate_abstraction_simulates with (pa := sys_pa).

  unfold predicate_abstraction_sound; simplify.
  cases act; simplify; invert H; unfold ruleAccurate, assertionAccurate in *; simplify; propositional; subst;
    simplify; unfold assertionAccurate in *; simplify; propositional;
    invert H1; simplify; propositional; equality || (try linear_arithmetic).

  model_check_infer.

  simplify.
  invert H.
  simplify.
  propositional; subst; invert H1; simplify; try equality.
  specialize (H3 "locked" true); simplify.
  cases (HasLock st); propositional; equality.
Qed.
