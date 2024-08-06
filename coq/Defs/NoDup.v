Set Warnings "-notation-overridden".
Require Import Preamble.

Require Import Defs.List.

#[export] Hint Constructors NoDup : core.

Fact NoDup_singleton : forall (X:Type) (x:X),
    NoDup [x].
Proof. intros. constructor; auto. Qed.
#[export] Hint Resolve NoDup_singleton : core.

Fact NoDup_destr1 : forall α (a:A),
    NoDup (α :: a)
  -> NoDup a.
Proof. intros. inverts H. crush. Qed.
#[export] Hint Resolve NoDup_destr1 : core.

Fact NoDup_app : forall a1 a2 α,
    NoDup (a1 ++ a2)
  -> α ∈ varl a1
  -> α ∈ varl a2
  -> False.
Proof.
  intro a1. induction a1 as [|α a1]. crush. intros.
  simpl+ in H0. inverts H. destr_union.
  - apply H4. apply in_or_app. right. eauto.
  - eauto.
Qed.
Corollary NoDup_app'1 : forall a1 a2 α,
    NoDup (a1 ++ a2)
  -> α ∈ varl a1
  -> α ∉ varl a2.
Proof. unfold not. apply NoDup_app. Qed.
Corollary NoDup_app'2 : forall a1 a2 α,
    NoDup (a1 ++ a2)
  -> α ∈ varl a2
  -> α ∉ varl a1.
Proof. unfold not. intros. eapply NoDup_app; eassumption. Qed.

Lemma NoDup_snoc : forall α (a:A),
    NoDup (a ++ [α])
  -> ~ In α a
  /\ NoDup a.
Proof.
  introv ND. forwards ND': NoDup_rev. eassumption.
  rewrite rev_app_distr in ND'. simpl+ in ND'. inverts ND'.
  rewrite <- in_rev in H1. apply NoDup_rev in H2. rewrite rev_involutive in H2.
  crush.
Qed.
