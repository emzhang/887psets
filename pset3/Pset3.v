(** * 6.887 Formal Reasoning About Programs, Spring 2016 - Pset 3 *)

Require Import Frap Pset3Sig.

Set Implicit Arguments.
   
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
  cases (Predicates pa $? x).
  cases (Rules pa $? act).

  (* ??? am stuck :( :( *)
  
  assert (applyRules f $0 l $? x = Some b -> exists r : rule,  match r with
  | {| Assumptions := asns; Conclusion := conc |} => (conc.(AssumedPredicate), conc.(AssumedToBe))
    
                                                               end = (x, b)).
  unfold applyRules in H1.
  unfold applyRule in H1.
  intros.
  simplify.
  simpl in H1.
  cases ( (fix applyRules (st st' : fmap var bool) (rs : list rule) {struct rs} :
          fmap var bool :=
          match rs with
          | [] => st'
          | r :: rs' =>
              applyRules st
                match r with
                | {| Assumptions := asns; Conclusion := conc |} =>
                    if assumptionsHold st asns
                    then st' $+ (AssumedPredicate conc, AssumedToBe conc)
                    else st'
                end rs'
          end) f $0 l $? x).
          if assumptionsHold st asns
    then st' $+ (conc.(AssumedPredicate), conc.(AssumedToBe))
    else st'
          
  invert H0; simplify.
  eapply PaR.
  simplify.
 
  
Admitted.


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
