(** * 6.887 Formal Reasoning About Programs, Spring 2016 - Pset 4 *)

Require Import Frap Pset4Sig.

(* Authors: Peng Wang (wangpeng@csail.mit.edu), Adam Chlipala (adamc@csail.mit.edu) *)


Section env.

  Variable env : environment.
  Hint Constructors trc step eval.

  Lemma step_star_Seq : forall v c1 c2 v' c1',
        (step env)^* (v, c1) (v', c1')
        -> (step env)^* (v, Sequence c1 c2) (v', Sequence c1' c2).
    Proof.
      induct 1; eauto.
      cases y; eauto.
    Qed.

  Hint Resolve step_star_Seq.

  Lemma step_star_InCall : forall v c v' c' v0 lhs ret,
        (step env)^* (v, c) (v', c')
        -> (step env)^* (v, InCall v0 lhs ret c) (v', InCall v0 lhs ret c').
  Proof.
      induct 1; eauto.
      cases y; eauto.
  Qed.

  Hint Resolve step_star_InCall.

  Lemma step_star_Try : forall v c v' c' x handler,
                          (step env) ^* (v, c) (v', c')
                          (*-> (step env) ^* (v, Try c x handler) (v', c') \/
                             (step env) ^* (v, Try c x handler) (v $+ (x, exn), handler).*)
                          (*-> (step env) ^* (v, Try Skip x handler) (v, Skip) \/ *)
                          -> (step env)^* (v, Try c x handler) (v', Try c' x handler).
  Proof.
    induct 1; eauto.
    cases y; eauto.
  Qed.

  Hint Resolve step_star_Try.
(*
  Lemma step_star_TryDone : forall v x handler,
                              (step env) ^* (v, Try Skip x handler) (v, Skip).
  Proof.
    econstructor; eauto.
  Qed.

  Hint Resolve step_star_TryDone.

  Lemma step_star_TryThrow : forall v (n : nat) x handler,
                               (step env)^* (v, Try (Throw (Const n)) x handler) (v $+ (x, n), handler).
  Proof.
    econstructor; eauto.
  Qed.


  Hint Resolve step_star_TryThrow.*)
                              
  Theorem big_small : forall v c v',
      eval env v c (Normal, v')
      -> (step env)^* (v, c) (v', Skip).
  Proof.
    
    induct 1; simplify; eauto 5 using trc_trans.
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
        apply step_star_Try.
        eauto.
      }  
      {
        econstructor.
        apply StepTry.
        
        
        
        
        
        
        
      (*
      {
        apply step_star_Try.
        eauto.
      }
      {
        econstructor;eauto.
        apply step_star_TryThrow.
      }
      {
        econstructor; eauto.
        *)
      
  (*
      assert (eval env v (Try c x handler) (Normal, v')).
      exact (EvalTryExn env v c exn v'0  x handler (Normal, v') H H0).
      cases c.
      invert H.
      invert H1.
      invert H.
      invert H.
      
      admit. (* sequence c1 c2 *)
      admit.
      admit.
      admit.
      admit.
      admit.
      
      
      Econstructor; eauto.
      cases c.
      econstructor; eauto.
      econstructor; eauto.
      SearchAbout trc.
      trc_trans      
      econstructor; eauto.
      cases c.
      *)
        
    
    
  Admitted.



  Theorem big_small_exn : forall v c n v',
      eval env v c (Exception n, v')
      -> (step env)^* (v, c) (v', Throw (Const n)).
  Proof.
  Admitted.

  Lemma small_big'' : forall v c v' c',
        (step env) (v, c) (v', c')
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
        (step env)^* (v, c) (v', c')
        -> forall v'', eval v' c' v''
                       -> eval v c v''.
    Proof.
      induct 1; eauto.
      cases y; eauto.
    Qed.

    Hint Resolve small_big'.

  Theorem small_big : forall v c v',
      (step env)^* (v, c) (v', Skip)
      -> eval env v c (Normal, v').
  Proof.
  Admitted.

  Theorem small_big_exn : forall v c v' n,
      (step env)^* (v, c) (v', Throw (Const n))
      -> eval env v c (Exception n, v').
  Proof.
  Admitted.

  (** Small-step semantics with control stack *)

  Theorem eval_stepcs : forall v c v',
      eval env v c (Normal, v')
      -> (stepcs env)^* ([], v, c, Skip) ([], v', Skip, Skip).
  Proof.
  Admitted.

  Theorem eval_stepcs_exn : forall v c (n : nat) v',
      eval env v c (Exception n, v')
      -> (stepcs env)^* ([], v, c, Skip) ([], v', Throw (Const n), Skip).
  Proof.
  Admitted.

  Theorem stepcs_eval : forall v c v',
      (stepcs env)^* ([], v, c, Skip) ([], v', Skip, Skip)
      -> eval env v c (Normal, v').
  Proof.
  Admitted.

  Theorem stepcs_eval_exn : forall v c v' (n : nat),
      (stepcs env)^* ([], v, c, Skip) ([], v', Throw (Const n), Skip)
      -> eval env v c (Exception n, v').
  Proof.
  Admitted.

End env.
