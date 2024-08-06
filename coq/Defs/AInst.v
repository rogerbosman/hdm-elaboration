Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.

Require Import Defs.ERels.
Require Import Defs.List.
Require Import Defs.Sub.

(*** Notation, tactics etc*)
Notation  "ψ ⊢a a ⤳ θ" := (AInst ψ a θ) (at level 50) : type_scope.

Theorem AInst_split : forall ψ a1 a2 θ,
    ψ ⊢a a2 ++ a1 ⤳ θ
  -> exists θ1 θ2,
          θ = θ2 ++ θ1
        /\ ψ ⊢a a1 ⤳ θ1
        /\ ψ ⊢a a2 ⤳ θ2.
Proof.
  introv AINST. gen θ. ind_a a2; intros. exists. crush.
  inverts AINST. forwards [?θ [?θ [EQ [?AINST ?AINST]]]]: IHa2. eassumption.
  subst. exists θ ((τ, α) :: θ0). splits; crush.
Qed.

Ltac AInst_split H :=
  apply AInst_split in H; destruct H as [?θ [?θ [?EQ [?INSTA ?INSTA]]]];
    match type of EQ with
      | (?θ1 = _) => subst θ1
    end.

Theorem AInst_merge : forall ψ a1 a2 θ1 θ2,
    ψ ⊢a a1 ⤳ θ1
  -> ψ ⊢a a2 ⤳ θ2
  -> ψ ⊢a (a2 ++ a1) ⤳ (θ2 ++ θ1).
Admitted.

(* Ltac inv_AInst := idtac. *)
Ltac inv_AInst :=
(*   repeat *)
(*     let da1 := fresh "da" in *)
(*     let da2 := fresh "da" in *)
(*     let dsub1 := fresh "dsub" in *)
(*     let dsub2 := fresh "dsub" in *)
(*     let EQ__da := fresh "EQ__da" in *)
(*     let EQ__dsub := fresh "EQ__dsub" in *)
(*     let INSTA1 := fresh "INSTA" in *)
(*     let INSTA2 := fresh "INSTA" in *)
    match goal with
(*     (*AInst*) *)
    | [ H : AInst _ nil      _ |- _ ] => inverts H
    | [ H : AInst _ []       _ |- _ ] => inverts H
    | [ H : AInst _ [_]      _ |- _ ] => inverts H
    | [ H : AInst _ (_ :: _)  _ |- _ ] => inverts H
    | [ H : AInst _ (_ ++ _) _ |- _ ] => AInst_split H
(*     | [ H : AInst _ _ ([_] ++ _) _ _ |- _ ] => inverts H *)
(*     | [ H : AInst _ _ (Env_Empty _) _ _ |- _ ] => inverts H *)
(*     | [ H : AInst _ _ • _ _ |- _ ] => inverts H *)
(*     | [ H : AInst _ _ (Env_Skol _ _) _ _ |- _ ] => inverts H *)
(*     | [ H : AInst _ _ (Env_A _ _) _ _ |- _ ] => inverts H *)
(*     | [ H : AInst _ _ (Env_Var _ _ _) _ _ |- _ ] => inverts H *)
(*     | [ H : AInst _ _ (Env_Obj _ _) _ _ |- _ ] => inverts H *)
(*     | [ H : AInst _ _ <_>a _ _ |- _ ] => inverts H *)
(*     | [ H : AInst _ _ (_ ++ _) _ _ |- _ ] => apply ainst_split in H; destruct H as [da1 [da2 [dsub1 [dsub2 [EQ__da [EQ__dsub [INSTA1 INSTA2]]]]]]]; subst *)
  end.


(*** Props *)
Lemma AInst_Sub_wf : forall a ψ θ,
    ψ ⊢a a ⤳ θ
  -> ψ ⊢θ θ.
Proof.
  introv AINST. induction AINST. crush.
  simpl+. eapply Sub_wf_cons; eassumption.
Qed.
#[export] Hint Resolve AInst_Sub_wf : core.

Corollary AInst_Sub_to_A : forall a ψ θ,
    ψ ⊢a a ⤳ θ
  -> a = Sub_to_A θ.
Proof.
  introv AINST. induction AINST; crush.
Qed.

(* Lemma AInst_props : forall a ψ θ, *)
(*     ψ ⊢a a ⤳ θ *)
(*   -> ψ ⊢θ θ *)
(*   /\ a = Sub_to_A θ. *)
(* Proof. *)
(*   induction a; introv INST; inv_AInst. crush. *)
(*   forwards [IH__wf IH__aeq]: IHa. eassumption. subst. *)
(*   splits. *)
(*   - introv IN. simpl+ in IN. destr_union. *)
(*     eauto. eauto. *)
(*   - eauto. *)
(* Qed. *)

(* Corollary AInst_props__swf : forall a ψ θ, *)
(*     ψ ⊢a a ⤳ θ *)
(*   -> ψ ⊢θ θ. *)
(* Proof. apply AInst_props. Qed. *)
(* #[export] Hint Resolve AInst_props__swf : core. *)



(*** ERels *)
Lemma  AInst_E_sk_sub : forall a ψ1 ψ2 θ,
    ψ1 ⊢a a ⤳ θ
  -> ψ1 ⊆ψα ψ2
  -> ψ2 ⊢a a ⤳ θ.
Proof.
  intro a. ind_a a; introv AINST SUB; inv_AInst.
  - auto.
  - eauto using WfT_E_A_sk_sub.
Qed.
#[export] Instance AInst_E_sk_sub_proper : Proper (E_A_sk_sub ==> eq ==> eq ==> impl) AInst.
Proof. autounfold. intros. subst. eauto using AInst_E_sk_sub. Qed.
