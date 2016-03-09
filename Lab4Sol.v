(** * 6.887 Formal Reasoning About Programs - Lab 4
    * Operational Semantics *)

Require Import Frap.

(* Authors: Peng Wang (wangpeng@csail.mit.edu), Adam Chlipala (adamc@csail.mit.edu) *)


(** * Challenge 1: Nondeterminism *)

Module Challenge1.
  
  Inductive arith : Set :=
  | Const (n : nat)
  | Var (x : var)
  | Plus (e1 e2 : arith)
  | Minus (e1 e2 : arith)
  | Times (e1 e2 : arith).

  Inductive cmd :=
  | Skip
  | Assign (x : var) (e : arith)
  | Sequence (c1 c2 : cmd)
  | If (e : arith) (then_ else_ : cmd)
  | While (e : arith) (body : cmd)
  | Choice (c1 c2 : cmd).

  Definition valuation := fmap var nat.
  Fixpoint interp (e : arith) (v : valuation) : nat :=
    match e with
    | Const n => n
    | Var x =>
      match v $? x with
      | None => 0
      | Some n => n
      end
    | Plus e1 e2 => interp e1 v + interp e2 v
    | Minus e1 e2 => interp e1 v - interp e2 v
    | Times e1 e2 => interp e1 v * interp e2 v
    end.

  (** Big-step semantics *)

  Inductive eval : valuation -> cmd -> valuation -> Prop :=
  | EvalSkip : forall v,
      eval v Skip v
  | EvalAssign : forall v x e,
      eval v (Assign x e) (v $+ (x, interp e v))
  | EvalSeq : forall v c1 v1 c2 v2,
      eval v c1 v1
      -> eval v1 c2 v2
      -> eval v (Sequence c1 c2) v2
  | EvalIfTrue : forall v e then_ else_ v',
      interp e v <> 0
      -> eval v then_ v'
      -> eval v (If e then_ else_) v'
  | EvalIfFalse : forall v e then_ else_ v',
      interp e v = 0
      -> eval v else_ v'
      -> eval v (If e then_ else_) v'
  | EvalWhileTrue : forall v e body v' v'',
      interp e v <> 0
      -> eval v body v'
      -> eval v' (While e body) v''
      -> eval v (While e body) v''
  | EvalWhileFalse : forall v e body,
      interp e v = 0
      -> eval v (While e body) v
  | EvalChoice1 : forall v c1 c2 v',
      eval v c1 v'
      -> eval v (Choice c1 c2) v'
  | EvalChoice2 : forall v c1 c2 v',
      eval v c2 v'
      -> eval v (Choice c1 c2) v'.

  (** Small-step semantics *)

  Inductive step : valuation * cmd -> valuation * cmd -> Prop :=
  | StepAssign : forall v x e,
      step (v, Assign x e) (v $+ (x, interp e v), Skip)
  | StepSeq1 : forall v c1 c2 v' c1',
      step (v, c1) (v', c1')
      -> step (v, Sequence c1 c2) (v', Sequence c1' c2)
  | StepSeq2 : forall v c2,
      step (v, Sequence Skip c2) (v, c2)
  | StepIfTrue : forall v e then_ else_,
      interp e v <> 0
      -> step (v, If e then_ else_) (v, then_)
  | StepIfFalse : forall v e then_ else_,
      interp e v = 0
      -> step (v, If e then_ else_) (v, else_)
  | StepWhileTrue : forall v e body,
      interp e v <> 0
      -> step (v, While e body) (v, Sequence body (While e body))
  | StepWhileFalse : forall v e body,
      interp e v = 0
      -> step (v, While e body) (v, Skip)
  | StepChoice1 : forall v c1 c2,
      step (v, Choice c1 c2) (v, c1)
  | StepChoice2 : forall v c1 c2,
      step (v, Choice c1 c2) (v, c2).

  Hint Constructors trc step eval.

  Lemma step_star_Seq : forall v c1 c2 v' c1',
      step^* (v, c1) (v', c1')
      -> step^* (v, Sequence c1 c2) (v', Sequence c1' c2).
  Proof.
    induct 1; eauto.
    cases y; eauto.
  Qed.

  Hint Resolve step_star_Seq.

  Theorem big_small : forall v c v', eval v c v'
                                     -> step^* (v, c) (v', Skip).
  Proof.
    induct 1; eauto 6 using trc_trans.
  Qed.

  Lemma small_big'' : forall v c v' c', step (v, c) (v', c')
                                        -> forall v'', eval v' c' v''
                                                       -> eval v c v''.
  Proof.
    induct 1; simplify;
      repeat match goal with
             | [ H : eval _ _ _ |- _ ] => invert1 H
             end; eauto.
  Qed.

  Hint Resolve small_big''.

  Lemma small_big' : forall v c v' c', step^* (v, c) (v', c')
                                         -> forall v'', eval v' c' v''
                                                  -> eval v c v''.
  Proof.
    induct 1; eauto.
    cases y; eauto.
  Qed.

  Hint Resolve small_big'.

  Theorem small_big : forall v c v', step^* (v, c) (v', Skip)
                                     -> eval v c v'.
  Proof.
    eauto.
  Qed.

  (** Contextual small-step semantics *)

  Inductive context :=
  | Hole
  | CSeq (C : context) (c : cmd).

  Inductive plug : context -> cmd -> cmd -> Prop :=
  | PlugHole : forall c, plug Hole c c
  | PlugSeq : forall c C c' c2,
      plug C c c'
      -> plug (CSeq C c2) c (Sequence c' c2).

  Inductive step0 : valuation * cmd -> valuation * cmd -> Prop :=
  | Step0Assign : forall v x e,
      step0 (v, Assign x e) (v $+ (x, interp e v), Skip)
  | Step0Seq : forall v c2,
      step0 (v, Sequence Skip c2) (v, c2)
  | Step0IfTrue : forall v e then_ else_,
      interp e v <> 0
      -> step0 (v, If e then_ else_) (v, then_)
  | Step0IfFalse : forall v e then_ else_,
      interp e v = 0
      -> step0 (v, If e then_ else_) (v, else_)
  | Step0WhileTrue : forall v e body,
      interp e v <> 0
      -> step0 (v, While e body) (v, Sequence body (While e body))
  | Step0WhileFalse : forall v e body,
      interp e v = 0
      -> step0 (v, While e body) (v, Skip)
  | Step0Choice1 : forall v c1 c2,
      step0 (v, Choice c1 c2) (v, c1)
  | Step0Choice2 : forall v c1 c2,
      step0 (v, Choice c1 c2) (v, c2).

  Inductive cstep : valuation * cmd -> valuation * cmd -> Prop :=
  | CStep : forall C v c v' c' c1 c2,
      plug C c c1
      -> step0 (v, c) (v', c')
      -> plug C c' c2
      -> cstep (v, c1) (v', c2).

  Hint Constructors plug step0 cstep.

  Theorem step_cstep : forall v c v' c',
      step (v, c) (v', c')
      -> cstep (v, c) (v', c').
  Proof.
    induct 1; repeat match goal with
                     | [ H : cstep _ _ |- _ ] => invert H
                     end; eauto.
  Qed.

  Lemma step0_step : forall v c v' c',
      step0 (v, c) (v', c')
      -> step (v, c) (v', c').
  Proof.
    induct 1; eauto.
  Qed.

  Hint Resolve step0_step.

  Lemma cstep_step' : forall C c0 c,
      plug C c0 c
      -> forall v' c'0 v c', step0 (v, c0) (v', c'0)
                       -> plug C c'0 c'
                       -> step (v, c) (v', c').
  Proof.
    induct 1; simplify; repeat match goal with
                               | [ H : plug _ _ _ |- _ ] => invert1 H
                               end; eauto.
  Qed.

  Hint Resolve cstep_step'.

  Theorem cstep_step : forall v c v' c',
      cstep (v, c) (v', c')
      -> step (v, c) (v', c').
  Proof.
    induct 1; eauto.
  Qed.

End Challenge1.


(** * Challenge 2: Functions and Control Stack *)

Module Challenge2.
  
  Inductive arith : Set :=
  | Const (n : nat)
  | Var (x : var)
  | Plus (e1 e2 : arith)
  | Minus (e1 e2 : arith)
  | Times (e1 e2 : arith).

  Definition valuation := fmap var nat.
  
  Inductive cmd :=
  | Skip
  | Assign (x : var) (e : arith)
  | Sequence (c1 c2 : cmd)
  | If (e : arith) (then_ else_ : cmd)
  | While (e : arith) (body : cmd)
  | Call (lhs f : var) (arg : arith)
  | InCall (v : valuation) (lhs ret : var) (c : cmd)
  | Return (e : arith).

  Fixpoint interp (e : arith) (v : valuation) : nat :=
    match e with
    | Const n => n
    | Var x =>
      match v $? x with
      | None => 0
      | Some n => n
      end
    | Plus e1 e2 => interp e1 v + interp e2 v
    | Minus e1 e2 => interp e1 v - interp e2 v
    | Times e1 e2 => interp e1 v * interp e2 v
    end.

  (* function specification *)
  Record fun_spec := {
    Arg : var;
    Ret : var;
    Body : cmd
  }.

  (** An environment is a mapping from function names to function specs *)
  Definition environment := fmap var fun_spec.

  Section env.

    Variable env : environment.
    
    (** Big-step semantics *)
    Inductive eval : valuation -> cmd -> valuation -> Prop :=
    | EvalSkip : forall v,
        eval v Skip v
    | EvalAssign : forall v x e,
        eval v (Assign x e) (v $+ (x, interp e v))
    | EvalSeq : forall v c1 v1 c2 v2,
        eval v c1 v1
        -> eval v1 c2 v2
        -> eval v (Sequence c1 c2) v2
    | EvalIfTrue : forall v e then_ else_ v',
        interp e v <> 0
        -> eval v then_ v'
        -> eval v (If e then_ else_) v'
    | EvalIfFalse : forall v e then_ else_ v',
        interp e v = 0
        -> eval v else_ v'
        -> eval v (If e then_ else_) v'
    | EvalWhileTrue : forall v e body v' v'',
        interp e v <> 0
        -> eval v body v'
        -> eval v' (While e body) v''
        -> eval v (While e body) v''
    | EvalWhileFalse : forall v e body,
        interp e v = 0
        -> eval v (While e body) v
    | EvalCall : forall v lhs f arg spec v',
        env $? f = Some spec 
        -> eval ($0 $+ (spec.(Arg), interp arg v)) spec.(Body) v'
        -> eval v (Call lhs f arg) (v $+ (lhs, interp (Var spec.(Ret)) v'))
    | EvalInCall : forall v0 lhs ret v c v',
        eval v c v'
        -> eval v (InCall v0 lhs ret c) (v0 $+ (lhs, interp (Var ret) v')).

    (** Small-step semantics *)

    Inductive step : valuation * cmd -> valuation * cmd -> Prop :=
    | StepAssign : forall v x e,
        step (v, Assign x e) (v $+ (x, interp e v), Skip)
    | StepSeq1 : forall v c1 c2 v' c1',
        step (v, c1) (v', c1')
        -> step (v, Sequence c1 c2) (v', Sequence c1' c2)
    | StepSeq2 : forall v c2,
        step (v, Sequence Skip c2) (v, c2)
    | StepIfTrue : forall v e then_ else_,
        interp e v <> 0
        -> step (v, If e then_ else_) (v, then_)
    | StepIfFalse : forall v e then_ else_,
        interp e v = 0
        -> step (v, If e then_ else_) (v, else_)
    | StepWhileTrue : forall v e body,
        interp e v <> 0
        -> step (v, While e body) (v, Sequence body (While e body))
    | StepWhileFalse : forall v e body,
        interp e v = 0
        -> step (v, While e body) (v, Skip)
    | StepStartCall : forall v lhs f arg spec,
        env $? f = Some spec
        -> step (v, Call lhs f arg) ($0 $+ (spec.(Arg), interp arg v), InCall v lhs spec.(Ret) spec.(Body))
    | StepInCall : forall v c v' c' v0 lhs ret,
        step (v, c) (v', c')
        -> step (v, InCall v0 lhs ret c) (v', InCall v0 lhs ret c')
    | StepEndCall : forall v0 lhs ret v,
        step (v, InCall v0 lhs ret Skip) (v0, Assign lhs (Const (interp (Var ret) v))).

    Hint Constructors trc step eval.

    Lemma step_star_Seq : forall v c1 c2 v' c1',
        step^* (v, c1) (v', c1')
        -> step^* (v, Sequence c1 c2) (v', Sequence c1' c2).
    Proof.
      induct 1; eauto.
      cases y; eauto.
    Qed.

    Hint Resolve step_star_Seq.

    Lemma step_star_InCall : forall v c v' c' v0 lhs ret,
        step^* (v, c) (v', c')
        -> step^* (v, InCall v0 lhs ret c) (v', InCall v0 lhs ret c').
    Proof.
      induct 1; eauto.
      cases y; eauto.
    Qed.

    Hint Resolve step_star_InCall.
    
    Theorem big_small : forall v c v',
        eval v c v'
        -> step^* (v, c) (v', Skip).
    Proof.
      induct 1; simplify; eauto 4 using trc_trans.
      {
        econstructor.
        eauto.
        eapply trc_trans.
        apply step_star_Seq.
        eassumption.
        eauto.
      }
      {
        econstructor; eauto.
        eapply trc_trans.
        {
          apply step_star_InCall.
          eassumption.
        }
        eauto.
      }
      {
        eapply trc_trans.
        {
          apply step_star_InCall.
          eassumption.
        }
        eauto.
      }
    Qed.

    Lemma small_big'' : forall v c v' c',
        step (v, c) (v', c')
        -> forall v'', eval v' c' v''
                       -> eval v c v''.
    Proof.
      induct 1; simplify;
        repeat match goal with
               | [ H : eval _ _ _ |- _ ] => invert1 H
               end; eauto.
      {
        econstructor; eauto.
      }
    Qed.

    Hint Resolve small_big''.

    Lemma small_big' : forall v c v' c',
        step^* (v, c) (v', c')
        -> forall v'', eval v' c' v''
                       -> eval v c v''.
    Proof.
      induct 1; eauto.
      cases y; eauto.
    Qed.

    Hint Resolve small_big'.

    Theorem small_big : forall v c v',
        step^* (v, c) (v', Skip)
        -> eval v c v'.
    Proof.
      eauto.
    Qed.

    (** Small-step semantics with control stack *)

    Inductive step0 : valuation * cmd -> valuation * cmd -> Prop :=
    | Step0Assign : forall v x e,
        step0 (v, Assign x e) (v $+ (x, interp e v), Skip)
    | Step0IfTrue : forall v e then_ else_,
        interp e v <> 0
        -> step0 (v, If e then_ else_) (v, then_)
    | Step0IfFalse : forall v e then_ else_,
        interp e v = 0
        -> step0 (v, If e then_ else_) (v, else_)
    | Step0WhileTrue : forall v e body,
        interp e v <> 0
        -> step0 (v, While e body) (v, Sequence body (While e body))
    | Step0WhileFalse : forall v e body,
        interp e v = 0
        -> step0 (v, While e body) (v, Skip).

    Record frame := {
      Val : valuation;
      Cont : cmd;
      LHS : var;
      RetVar : var
    }.

    Definition stack := list frame.

    Inductive stepcs : stack * valuation * cmd * cmd -> stack * valuation * cmd * cmd -> Prop :=
    | StepcsStep0 : forall v c v' c' s k,
        step0 (v, c) (v', c') ->
        stepcs (s, v, c, k) (s, v', c', k)
    | StepcsSeq : forall s v c1 c2 k,
        stepcs (s, v, Sequence c1 c2, k) (s, v, c1, Sequence c2 k)
    | StepcsCont : forall s v k1 k2,
        stepcs (s, v, Skip, Sequence k1 k2) (s, v, k1, k2)
    | StepcsReturn : forall fr s v,
        stepcs (fr :: s, v, Skip, Skip) (s, fr.(Val) $+ (fr.(LHS), interp (Var fr.(RetVar)) v), Skip, fr.(Cont))
    | StepcsCall : forall s v lhs f arg k spec,
        env $? f = Some spec
        -> stepcs (s, v, Call lhs f arg, k) ({| Val := v; Cont := k; LHS := lhs; RetVar := spec.(Ret)|} :: s, $0 $+ (spec.(Arg), interp arg v), spec.(Body), Skip)
    | StepcsInCall : forall s v0 lhs ret v c k,
        stepcs (s, v, InCall v0 lhs ret c, k) ({| Val := v0; Cont := k; LHS := lhs; RetVar := ret|} :: s, v, c, Skip).
    
    Hint Constructors step0 stepcs.

    Hint Extern 0 (_ <> _) => equality.

    Lemma eval_stepcs' : forall v c v',
        eval v c v'
        -> forall s k, stepcs^* (s, v, c, k) (s, v', Skip, k).
    Proof.
      induct 1; simplify; eauto 4 using trc_trans.
      {
        econstructor; eauto.
        econstructor; eauto.
        eapply trc_trans; eauto.
      }
      {
        econstructor; eauto.
        eapply trc_trans; eauto.
      }
    Qed.
    
    Theorem eval_stepcs : forall v c v',
        eval v c v'
        -> stepcs^* ([], v, c, Skip) ([], v', Skip, Skip).
    Proof.
      simplify.
      eapply eval_stepcs'.
      eauto.
    Qed.

    Definition unravel_frame c fr := Sequence (InCall fr.(Val) fr.(LHS) fr.(RetVar) c) fr.(Cont).
    Arguments unravel_frame _ _ / .
      
    Definition unravel s c := fold_left unravel_frame s c.
    Arguments unravel / .

    Lemma eval_unravel : forall s v c v' c',
        (forall v'', eval v' c' v'' -> eval v c v'') ->
        forall v'',
          eval v' (unravel s c') v'' ->
          eval v (unravel s c) v''.
    Proof.
      induct s; simplify.
      { eauto. }
      eapply IHs; try eassumption.
      simplify.
      repeat match goal with
             | [ H : eval _ _ _ |- _ ] => invert1 H
             end; eauto.
      econstructor; try eassumption.
      eauto.
    Qed.
    
    Lemma step0_eval : forall v c v' c',
        step0 (v, c) (v', c')
        -> forall v'', eval v' c' v''
                       -> eval v c v''.
    Proof.
      induct 1; simplify;
        repeat match goal with
               | [ H : eval _ _ _ |- _ ] => invert1 H
               end; eauto.
    Qed.

    Hint Resolve step0_eval.

    Lemma stepcs_eval'' : forall s v c k s' v' c' k',
        stepcs (s, v, c, k) (s', v', c', k')
        -> forall v'', eval v' (unravel s' (Sequence c' k')) v''
                       -> eval v (unravel s (Sequence c k)) v''.
    Proof.
      induct 1; simplify; eapply eval_unravel; try eassumption; simplify;
        repeat match goal with
               | [ H : eval _ _ _ |- _ ] => invert1 H
               end; eauto 6.
      {
        econstructor; try eassumption.
        econstructor; eauto.
      }
      {
        econstructor; try eassumption.
        econstructor; eauto.
      }
    Qed.

    Hint Resolve stepcs_eval''.

    Lemma stepcs_eval' : forall s v c k s' v' c' k',
        stepcs^* (s, v, c, k) (s', v', c', k')
        -> forall v'', eval v' (unravel s' (Sequence c' k')) v''
                       -> eval v (unravel s (Sequence c k)) v''.
    Proof.
      induct 1; eauto.
      repeat match goal with
             | [ H : (_ * _)%type |- _ ] => cases H
             end; eauto.
    Qed.

    Hint Resolve stepcs_eval'.

    Theorem stepcs_eval : forall v c v',
        stepcs^* ([], v, c, Skip) ([], v', Skip, Skip)
        -> eval v c v'.
    Proof.
      simplify.
      eapply stepcs_eval' in H; simplify;
        repeat match goal with
               | [ H : eval _ _ _ |- _ ] => invert1 H
               end; eauto.
    Qed.


  End env.

  (* Here's how to handle the [Return] command. *)
  Module StrangeAlternateUniverse.
    Section Return.
      Variable env : environment.

      Inductive stepcs : stack * valuation * cmd * cmd -> stack * valuation * cmd * cmd -> Prop :=
      | StepcsStep0 : forall v c v' c' s k,
          step0 (v, c) (v', c') ->
          stepcs (s, v, c, k) (s, v', c', k)
      | StepcsSeq : forall s v c1 c2 k,
          stepcs (s, v, Sequence c1 c2, k) (s, v, c1, Sequence c2 k)
      | StepcsCont : forall s v k1 k2,
          stepcs (s, v, Skip, Sequence k1 k2) (s, v, k1, k2)
      | StepcsReturn : forall fr s v,
          stepcs (fr :: s, v, Skip, Skip) (s, fr.(Val) $+ (fr.(LHS), interp (Var fr.(RetVar)) v), Skip, fr.(Cont))

      (****)
      | StepcsExplicitReturn : forall fr s v e k,
          stepcs (fr :: s, v, Return e, k) (s, fr.(Val) $+ (fr.(LHS), interp e v), Skip, fr.(Cont))
      (****)

      | StepcsCall : forall s v lhs f arg k spec,
          env $? f = Some spec
          -> stepcs (s, v, Call lhs f arg, k) ({| Val := v; Cont := k; LHS := lhs; RetVar := spec.(Ret)|} :: s, $0 $+ (spec.(Arg), interp arg v), spec.(Body), Skip)
      | StepcsInCall : forall s v0 lhs ret v c k,
          stepcs (s, v, InCall v0 lhs ret c, k) ({| Val := v0; Cont := k; LHS := lhs; RetVar := ret|} :: s, v, c, Skip).
    End Return.
  End StrangeAlternateUniverse.

End Challenge2.
