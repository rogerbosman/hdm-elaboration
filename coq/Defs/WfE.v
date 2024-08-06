Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.
Require Import Defs.HdmLems.

Require Import Defs.ERels.
Require Import Defs.FrA.
Require Import Defs.WfSTt.

Notation "wf( ψ )" := (WfE ψ) (at level 50, format "wf( ψ )") : type_scope.


Ltac inv_WfE :=
    repeat match goal with
    | [ H : wf(•                ) |- _ ] => inverts H
    | [ H : wf(_ ::a _           ) |- _ ] => inverts H
    | [ H : wf(_ ::x _ :- _      ) |- _ ] => inverts H
    | [ H : wf(_ ::o ⦇_ ▸ ⟨_⟩ _⦈ ) |- _ ] => inverts H
    end.

Fact WfE_destr_cons_var1 : forall ψ x σ,
    wf(ψ ::x x :- σ)
  -> wf(ψ).
Proof. intros. inverts H. crush. Qed.
Fact WfE_destr_cons_var2 : forall ψ x σ,
    wf(ψ ::x x :- σ)
  -> ψ ⊢wfσ σ.
Proof. intros. inverts H. crush. Qed.
Fact WfE_destr_cons_var3 : forall ψ x σ,
    wf(ψ ::x x :- σ)
  -> x ∉ E_names ψ.
Proof. intros. inverts H. crush. Qed.
#[export] Hint Resolve WfE_destr_cons_var1 WfE_destr_cons_var2 WfE_destr_cons_var3 : core.

Fact WfE_destr_cons_obj1 : forall ψ t a σ,
    wf(ψ ::o ⦇t ▸ ⟨a⟩ σ⦈)
  -> wf(ψ ::a a).
Proof. intros. inverts H. crush. Qed.
Fact WfE_destr_cons_obj2 : forall ψ t a σ,
    wf(ψ ::o ⦇t ▸ ⟨a⟩ σ⦈)
  -> (ψ ::a a) ⊢wft t.
Proof. intros. inverts H. crush. Qed.
Fact WfE_destr_cons_obj3 : forall ψ t a σ,
    wf(ψ ::o ⦇t ▸ ⟨a⟩ σ⦈)
  -> (ψ ::a a) ⊢wfσ σ.
Proof. intros. inverts H. crush. Qed.
#[export] Hint Resolve WfE_destr_cons_obj1 WfE_destr_cons_obj2 WfE_destr_cons_obj3 : core.

Fact WfE_destr_cons_a1 : forall ψ a,
    wf(ψ ::a a)
  -> wf(ψ).
Proof. intros. inverts H. crush. Qed.
Fact WfE_destr_cons_a2 : forall ψ a,
    wf(ψ ::a a)
  -> a ### E_skvars ψ.
Proof. intros. inverts H. crush. Qed.
#[export] Hint Resolve WfE_destr_cons_a1 WfE_destr_cons_a2 : core.

Lemma TmTy_wft_var : forall ψ σ,
    wf(ψ)
  -> σ ∈σ E_schemes ψ
  -> ψ ⊢wfσ σ.
Proof.
  introv WF IN. induction WF; simpl+ in IN. crush.
  - eapply WfS_E_A_sk_sub. eauto. fsetdec+.
  - applys WfS_E_A_sk_sub ψ. 2:fsetdec+.
    destr_union; eauto.
  - eapply WfS_E_A_sk_sub. eauto. fsetdec+.
Qed.

Fact WfE__A' : forall(ψ:E) (a:A),
    wf(ψ)
  -> a ### (E_skvars ψ)
  -> wf(E_append_A_in_A ψ a).
Proof.
  intros. destruct ψ; simpl+. 3,4:crush. constructor; auto.
  inverts H. econstructor. auto. eapply FrA_app. eassumption. eassumption.
  simpl+. fsetdec.
Qed.
#[export] Hint Resolve WfE__A' : core.


Lemma WfE_cons_Unit : forall ψ,
    wf(ψ)
  -> wf(ψ ::o ⦇t__Unit ▸ ⟨[]⟩ S__T T__Unit⦈).
Proof. intros. econstructor; crush. Qed.
#[export] Hint Resolve WfE_cons_Unit : core.

Lemma WfE_cons_obj_shift : forall ψ a t σ,
    wf(ψ ::a a ::o ⦇t ▸ ⟨[]⟩ σ⦈)
  <-> wf(ψ ::o ⦇t ▸ ⟨a⟩ σ⦈).
Proof. split; intros; inverts H; econstructor; eauto; wfdec. Qed.
