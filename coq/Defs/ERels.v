Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.

Require Import Defs.Sub.
Require Import Defs.WfSTt.

Ltac erel_fsetdec := unfolds; simpl+; fsetdec.
Ltac erel_crush := unfolds; simpl+; crush.

(*** E_x_sub *)
Notation E_x_sub := M_E_names.R__sub.
#[export] Hint Unfold E_x_sub : defs rels.
Notation  "ψ1 ⊆ψx ψ2"  := (E_x_sub ψ1 ψ2) (at level 70).

(*** E_sk_sub *)
Notation E_sk_sub := M_E_skvars.R__sub.
#[export] Hint Unfold E_sk_sub : defs rels.

(*** E_x_Sc_sub *)
Notation E_x_Sc_sub := M_E_bindings.R__sub.
#[export] Hint Unfold E_x_Sc_sub : defs rels.
Notation  "ψ1 ⊆ψxσ ψ2"  := (E_x_Sc_sub ψ1 ψ2) (at level 70).

(*** E_A_sk_sub *)
Notation E_A_sk_sub := M_E_A_skvars.R__sub.
Notation  "ψ1 ⊆ψα ψ2"  := (E_A_sk_sub ψ1 ψ2) (at level 70).
#[export] Hint Unfold E_A_sk_sub : defs rels.

Lemma WfT_E_A_sk_sub : forall ψ1 ψ2 τ,
    ψ1 ⊢wfτ τ
  -> ψ1 ⊆ψα ψ2
  -> ψ2 ⊢wfτ τ.
Proof. intros. unfolds. unfolds in H. split. jauto. crush. Qed.
#[export] Hint Resolve WfT_E_A_sk_sub : core.
#[export] Instance WfT_E_sk_sub_proper : Proper (E_A_sk_sub ==> eq ==> impl) WfT.
Proof. autounfold. intros. subst. eauto. Qed.

Lemma WfS_E_A_sk_sub : forall ψ1 ψ2 σ,
    ψ1 ⊢wfσ σ
  -> ψ1 ⊆ψα ψ2
  -> ψ2 ⊢wfσ σ.
Proof. intros. unfolds. unfolds in H. split. jauto. destruct H. rewrite H1. crush. Qed.
#[export] Hint Resolve WfS_E_A_sk_sub : core.
#[export] Instance WfS_E_sk_sub_proper : Proper (E_A_sk_sub ==> eq ==> impl) WfS.
Proof. autounfold. intros. subst. eauto. Qed.

Lemma Wft_E_A_sk_sub : forall ψ1 ψ2 t,
    ψ1 ⊢wft t
  -> ψ1 ⊆ψα ψ2
  -> ψ1 ⊆ψx ψ2
  -> ψ2 ⊢wft t.
Proof. intros. unfolds. unfolds in H. splits. jauto. crush. crush. Qed.

Lemma SubSumpTm_E_A_sk_sub : forall ψ1 ψ2 t1 σ t2 τ,
    SubSumpTm ψ1 t1 σ t2 τ
  -> ψ1 ⊆ψα ψ2
  -> SubSumpTm ψ2 t1 σ t2 τ.
Proof. introv SS SUB. induction SS. crush. eauto. Qed.
#[export] Hint Resolve SubSumpTm_E_A_sk_sub : core.
#[export] Instance SubSump_E_sk_sub_proper : Proper (E_A_sk_sub ==> eq ==> eq ==> eq ==> eq ==> impl) SubSumpTm.
Proof. autounfold. intros. subst. eauto. Qed.


Fact Sub_wf_E_sk_sub : forall ψ1 ψ2 θ,
    ψ1 ⊢θ θ
  -> ψ1 ⊆ψα ψ2
  -> ψ2 ⊢θ θ.
Proof. introv WF SUB IN. rewrite <- SUB. crush. Qed.

(*** E_O_sk_sub *)
Notation E_O_sk_sub := M_E_A_O_skvars.R__sub.
Notation  "ψ1 ⊆ψα# ψ2"  := (E_O_sk_sub ψ1 ψ2) (at level 70).
#[export] Hint Unfold E_O_sk_sub : defs rels.

Axiom E_skvas_E_A_O_skvars : forall ψ,
  E_A_skvars ψ ⊆ E_A_O_skvars ψ.
#[export] Hint Resolve E_skvas_E_A_O_skvars : core.


(*** E_x_eq_list *)
Definition E_x_list := E_fold [] const (fun acc x σ => (x, σ) :: acc) const3.

Definition E_x_list_eq : relation E := fun ψ1 ψ2 => E_x_list ψ1 = E_x_list ψ2.
Notation  "ψ1 =ψx ψ2"  := (E_x_list_eq ψ1 ψ2) (at level 70).
#[export] Hint Unfold E_x_list_eq : defs rels.

Lemma E_x_list_eq_app : forall ψ1 ψ1' ψ2 ψ2',
    ψ1 =ψx ψ1'
  -> ψ2 =ψx ψ2'
  -> ψ1 +++ ψ2 =ψx ψ1' +++ ψ2'.
Proof.
  intros. gen ψ1 ψ1' ψ2'. induction ψ2; intros.
  - simpl+ in *. induction ψ2'. 1,2,4:crush.
    unfolds in H0. simpl+ in H0. crush.
  - simpl+. eauto.
  - induction ψ2'; simpl+ in *; unfolds in H0; simpl+ in H0.
    crush. crush. inverts H0. unfolds. simpl+. fequals. apply IHψ2. eassumption. eassumption. crush.
  - simpl+. eauto.
Qed.

#[export] Instance E_x_list_eq_app_proper : Proper (E_x_list_eq ==> E_x_list_eq ==> E_x_list_eq) E__app. autounfold. intros. apply E_x_list_eq_app; crush. Qed.

Lemma E_lookup_E_x_list_eq : forall ψ1 ψ2 x,
    ψ1 =ψx ψ2
  -> E_lookup ψ1 x = E_lookup ψ2 x.
Proof.
  intro ψ1. induction ψ1; intros.
  - induction ψ2; simpl+. 1,2,4:crush.
    unfolds in H. simpl in H. crush.
  - eauto.
  - induction ψ2.
    + unfolds in H. simpl in H. crush.
    + eauto.
    + unfolds in H. simpl+ in H. inverts H.
      simpl+. if_dec; crush.
    + eauto.
  - eauto.
Qed.
#[export] Hint Resolve E_lookup_E_x_list_eq : core.
#[export] Instance E_x_list_eq_proper : Proper (E_x_list_eq ==> eq ==> eq) E_lookup. autounfold. crush. Qed.

(*** E_sk_x_Sc_sub *)
Definition E_sk_x_Sc_sub (ψ1 ψ2:E) := (ψ1 ⊆ψα ψ2 /\ ψ1 ⊆ψxσ ψ2).
#[export] Hint Unfold E_sk_x_Sc_sub : core.
Notation  "ψ1 ⊆ψαxσ ψ2"  := (E_sk_x_Sc_sub ψ1 ψ2) (at level 70).

#[export] Instance E_sk_x_sub_proper : Proper (E_sk_x_Sc_sub ==> eq ==> E_sk_x_Sc_sub) E__app. autounfold. crush. Qed.

Lemma E_sk_x_sub_var_OLDSTYLE :  forall σ x ψ1 ψ2 ψ3 (τ:T) (t:Tm),
    (σ, x) ∈σx E_bindings ψ1
  -> SubSumpTm (ψ1 +++ ψ3) (t__Var_f x) σ t τ
  -> ψ1 ⊆ψαxσ  ψ2
  -> exists σ',
      (σ', x) ∈σx E_bindings ψ2
    /\ SubSumpTm (ψ2 +++ ψ3) (t__Var_f x) σ' t τ.
Proof.
  introv IN SS [SUB EQ]. exists σ. split.
  - simpl+. rewrite+ <- EQ. crush.
  - eapply SubSumpTm_E_A_sk_sub. eassumption. crush.
Qed.

Lemma E_sk_x_sub_SS : forall ψ1 ψ2 ψ3 x σ t τ,
    SubSumpTm (ψ1 +++ ψ3) (t__Var_f x) σ t τ
  -> ψ1 ⊆ψαxσ  ψ2
  -> SubSumpTm (ψ2 +++ ψ3) (t__Var_f x) σ t τ.
Proof.
  introv SS [SUB__a SUB__x].
  assert (ψ1 +++ ψ3 ⊆ψα ψ2 +++ ψ3). crush.
  rewrite <- H. eassumption.
Qed.

Lemma E_sk_x_sub_WfT : forall ψ1 ψ2 ψ3 τ,
    (ψ1 +++ ψ3) ⊢wfτ τ
  -> ψ1 ⊆ψαxσ  ψ2
  -> (ψ2 +++ ψ3) ⊢wfτ τ.
Proof. introv WFT [SUB _]. rewrite <- SUB. crush. Qed.

(*** E_sk_sub_x_list_eq *)
Definition E_sk_sub_x_list_eq (ψ1 ψ2:E) := (ψ1 ⊆ψα ψ2 /\ ψ1 =ψx ψ2).
#[export] Hint Unfold E_sk_sub_x_list_eq : core.

#[export] Instance E_sk_sub_x_eq_app_proper : Proper (E_sk_sub_x_list_eq ==> eq ==> E_sk_sub_x_list_eq) E__app. autounfold. split. crush. crush. apply E_x_list_eq_app_proper; crush. Qed.

Lemma E_sk_sub_x_list_eq_vars : forall σ x ψ1 ψ2 ψ3 (τ:T) (t:Tm),
      E_lookup ψ3 x = None
    -> E_lookup ψ1 x = Some σ
    -> SubSumpTm (ψ1 +++ ψ3) (t__Var_f x) σ t τ
  -> E_sk_sub_x_list_eq ψ1  ψ2
    -> exists σ',
        E_lookup ψ2 x = Some σ'
      /\ SubSumpTm (ψ2 +++ ψ3) (t__Var_f x) σ' t τ.
Proof.
  introv IN SS [SUB EQ]. exists σ. split.
  - rewrite <- EQ. crush.
  - eapply SubSumpTm_E_A_sk_sub. eassumption. crush.
Qed.

Lemma E_sk_sub_x_list_eq_SS : forall ψ1 ψ2 ψ3 x σ t τ,
    SubSumpTm (ψ1 +++ ψ3) (t__Var_f x) σ t τ
  -> E_sk_sub_x_list_eq ψ1  ψ2
  -> SubSumpTm (ψ2 +++ ψ3) (t__Var_f x) σ t τ.
Proof.
  introv SS [SUB__a SUB__x].
  assert (ψ1 +++ ψ3 ⊆ψα ψ2 +++ ψ3). crush.
  rewrite <- H. eassumption.
Qed.

Lemma E_sk_sub_x_list_eq_WfT : forall ψ1 ψ2 ψ3 τ,
    (ψ1 +++ ψ3) ⊢wfτ τ
  -> E_sk_sub_x_list_eq ψ1  ψ2
  -> (ψ2 +++ ψ3) ⊢wfτ τ.
Proof. introv WFT [SUB _]. rewrite <- SUB. crush. Qed.


Ltac wfdec :=
  match goal with
    | |- _ ⊢wfσ _ => eapply WfS_E_A_sk_sub; [eassumption|reldec]
    | |- _ ⊢wfτ _ => eapply WfT_E_A_sk_sub; [eassumption|reldec]
    | |- _ ⊢wft _ => eapply Wft_E_A_sk_sub; [eassumption|reldec|reldec]
  end.
Ltac wfdec' :=
  match goal with
    | |- _ ⊢wfσ _ => eapply WfS_E_A_sk_sub; [eauto|reldec]
    | |- _ ⊢wfτ _ => eapply WfT_E_A_sk_sub; [eauto|reldec]
    | |- _ ⊢wft _ => eapply Wft_E_A_sk_sub; [eauto|reldec|reldec]
  end.
