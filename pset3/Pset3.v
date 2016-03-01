(** * 6.887 Formal Reasoning About Programs, Spring 2016 - Pset 3 *)

Require Import Frap Pset3Sig.

Set Implicit Arguments.
(*
Lemma first_thing : forall pc state action
  (*(st1 st2 : state)*)
  (actionOf : pc -> action -> pc -> Prop)
  (doAction : action -> state -> state -> Prop)
  (pa : predicate_abstraction state action)
  (sys1 : trsys (pc * state))
  (sys2 : trsys (pc * fmap var bool))
  (R : pc * state -> pc * fmap var bool -> Prop),
  (forall st1, sys1.(Initial) st1
               -> exists st2, R st1 st2
                              /\ sys2.(Initial) st2).
Proof.
  simplify.
  first_order.
  simplify.
Admitted.

Lemma second_thing : forall pc state action
  (sys1 : trsys (pc * state))
  (sys2 : trsys (pc * fmap var bool))
  (R : pc * state -> pc * fmap var bool -> Prop) ,
  (forall st1 st2, R st1 st2
                      -> forall st1', sys1.(Step) st1 st1'
                                      -> exists st2', R st1' st2'
                                                      /\ sys2.(Step) st2 st2').
Proof.
*)
   
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
  exists (paR.(Initial)).
  destruct st1.

    
    simplify.
  exists (Initial (predicate_abstract pc0 actionOf pa)).
                    
  induct paR.
  simplify.
  propositional.
  invert H1.
  
  exact (Simulates (first_thing _ _ _ _ _ _ _ _) (second_thing _ _ _ _ _ _ __ _ _ _)).
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
  invariantFor (sys np npo) (fun st => fst st = Unlock2 -> (snd st).(HasLock) = true).
Proof.
Admitted.
