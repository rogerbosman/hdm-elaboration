Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.

Require Import Defs.List.
Require Import Defs.OpenClose.
Require Import Defs.Subst.rename_skvar_A.
Require Import Defs.Subst.Notation.

From Equations Require Import Equations.

Fixpoint foralls (σ:Sc) : nat :=
  match σ with
  | (S__T _) => 0
  | (S__Forall σ) => S (foralls σ)
  end.

Definition foralls_lt (σ1 σ2:Sc) := lt (foralls σ1) (foralls σ2).

#[local] Hint Constructors Acc : core.

Lemma well_founded'_foralls_lt_wf' : forall len, forall σ, foralls σ <= len -> Acc foralls_lt σ.
  unfold foralls_lt; induction len; crush.
Defined.
Theorem well_founded_foralls_lt : well_founded foralls_lt.
  red; intro; eapply well_founded'_foralls_lt_wf'; eauto.
Defined.

Fact foralls_open_Sc_wrt_T_rec : forall σ τ n,
  foralls (open_Sc_wrt_T_rec n τ σ) = foralls σ.
Proof. intro σ. induction σ; crush. Qed.
#[export] Hint Rewrite foralls_open_Sc_wrt_T_rec : core.
Fact foralls_open_Sc_wrt_T : forall σ τ,
  foralls (open_Sc_wrt_T σ τ) = foralls σ.
Proof. intros. unfold open_Sc_wrt_T. simpl+. crush. Qed.
#[export] Hint Rewrite foralls_open_Sc_wrt_T : core.

Equations Derive NoConfusion Subterm for T.

Definition well_founded_subterm : well_founded T_subterm. eapply well_founded_T_subterm. Qed.


Inductive foralls_or_subterm : Sc -> Sc -> Prop :=
  | decr_foralls : forall (σ1 σ2:Sc),
      lt (foralls σ1) (foralls σ2)
    -> foralls_or_subterm σ1 σ2
  | decr_subterm : forall (τ1 τ2:T),
      T_subterm τ1 τ2
    -> foralls_or_subterm (S__T τ1) (S__T τ2).
#[export] Hint Constructors foralls_or_subterm : core.

Lemma T_subterm_foralls_or_subterm : forall τ,
    Acc T_subterm τ
  -> Acc foralls_or_subterm (S__T τ).
Proof.
  intros. induction H. econstructor. intros τ' ?H.
  inverts H1.
  - destruct τ'; simpl+ in H2; crush.
  - eauto.
Qed.

Lemma foralls_foralls_or_subterm : forall σ,
    Acc foralls_lt σ
  -> Acc foralls_or_subterm σ.
Proof.
  intros. induction H. econstructor. intros σ' ?H.
  inverts H1.
  - eauto.
  - eapply T_subterm_foralls_or_subterm. eapply well_founded_subterm.
Qed.

Lemma well_founded_foralls_or_subterm : well_founded foralls_or_subterm.
Proof. unfold well_founded. intro σ. apply foralls_foralls_or_subterm. apply well_founded_foralls_lt. Qed.

#[export] Instance WellFounded_foralls_or_subterm : WellFounded foralls_or_subterm := { wellfounded := well_founded_foralls_or_subterm }.

Lemma calc_foralls : forall σ,
    exists n, n = foralls σ.
Proof. induction σ; eexists; crush. Qed.

Ltac forall_ind σ :=
  let n := fresh "n" in
  forwards [n H]: calc_foralls σ; gen σ; induction n;
    [ intros σ__τ H__foralls; destruct σ__τ; [clear H__foralls | inverts H__foralls]
    | intros σ__Forall H__foralls; destruct σ__Forall; simpl+ in H__foralls; inverts H__foralls].

Fact foralls_close_Sc_wrt_T_rec : forall σ α n,
  foralls (close_Sc_wrt_T_rec n α σ) = foralls σ.
Proof. intro σ. induction σ; crush. Qed.
#[export] Hint Rewrite foralls_close_Sc_wrt_T_rec : core.
Fact foralls_close_Sc_wrt_T : forall σ α,
  foralls (close_Sc_wrt_T α σ) = foralls σ.
Proof. intros. unfold close_Sc_wrt_T. simpl+. crush. Qed.
#[export] Hint Rewrite foralls_close_Sc_wrt_T : core.

Lemma foralls_close_Sc_wrt_A : forall (a:A) (σ:Sc),
    foralls (∀ a ⬪ σ) = plus (length a) (foralls σ).
Proof. intro a. ind_a a. crush. intros. simpl+. fequals. Qed.

Lemma foralls_rename_skvar : forall α__in α__out a σ,
    foralls (∀ {α__in ↤ α__out}a ⬪ σ) = foralls (∀ a ⬪ σ).
Proof. intros. do 2 rewrite foralls_close_Sc_wrt_A. fequals. simpl+. crush. Qed.
#[export] Hint Rewrite foralls_rename_skvar : core.

Lemma Sub_app_Sc_foralls : forall σ θ,
  foralls ⟦θ ▹ σ⟧ = foralls σ.
Proof. intros. induction σ. crush. simpl+. crush. Qed.
