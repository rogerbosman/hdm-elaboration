Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.

Require Import Defs.List.

Require Import Defs.Subst.Notation.
Require Import Defs.Subst.rename_var.


(*** Def *)
(* Definition rename_skvar_A (α__in α__out : skvar) : A -> A := fold_right (fun (α:skvar) (a:A) => (rename_var α__in α__out α) :: a) []. *)
Definition rename_skvar_A (α__in α__out : skvar) : A -> A := map (rename_var α__in α__out).

#[export] Instance renamable_skvar_A : renamable_skvar A skvar := { rename_skvar := rename_skvar_A }.
(* #[export] Instance substable_A : substable A skvar skvar := { subst := rename_skvar_A }. *)

#[export] Hint Unfold rename_skvar renamable_skvar_A rename_skvar_A : rename_skvar_A.
Ltac unfold_rename_skvar := autounfold with rename_skvar_A.

(*** Simplification *)
Lemma rename_skvar_A_app : forall α__in α__out a1 a2,
    {α__in ↤ α__out} (a1 ++ a2) = {α__in ↤ α__out} a1 ++ {α__in ↤ α__out} a2.
Proof. intros. induction a1; simpl+. crush. fequals. Qed.
#[export] Hint Rewrite rename_skvar_A_app : core.

Lemma rename_skvar_A_notin : forall a α β,
    α ∉ varl a
  -> {β ↤ α}a = a.
Proof.
  intros. ind_a a. crush.
  simpl+. unfold_subst_var. if_dec; simpl+ in H. fsetdec. fequals. apply IHa. fsetdec.
Qed.

(*** In, Nodup *)
Lemma In_subst_var : forall α__in α__out α a,
    In α ({α__in ↤ α__out}a)
  -> α__in ∉ varl a
  -> (In α__out a /\ α = α__in)
  \/ In α a.
Proof.
  intros. ind_a a. crush.
  simpl+ in H. destruct H.
  - unfold rename_var in H. if_dec.
    + left. simpl+. crush.
    + subst. simpl+. auto.
  - simpl+ in H0. forwards: IHa. simpl+. eassumption. fsetdec. destruct H1. destruct H1.
    + crush.
    + simpl+ in *. eauto.
Qed.

Lemma NoDup_rename_skvar_A : forall α__in α__out a,
    NoDup a
  -> α__in ∉ varl a
  -> NoDup ({α__in ↤ α__out}a).
Proof.
  intros. ind_a a. crush. simpl+. inverts H. simpl+ in H0.
  specializes IHa. eassumption. fsetdec.
  constructor. 2:eauto. intro IN. apply In_subst_var in IN. destruct IN.
  - destruct H. unfold rename_var in H1. if_dec. eauto. crush.
  - unfold rename_var in H. if_dec. apply in_a_in_varl in H. crush. crush.
  - fsetdec.
Qed.

(*** Other lemmas *)
Lemma varl_rename_skvar_A_upper : forall a α β,
    varl ({β ↤ α}a) ⊆ varl a ∪ {{β}}.
Proof.
  intros. ind_a a. crush. simpl+. rewrite IHa. rewrite subst_var_upper. clfsetdec.
Qed.

Lemma varl_rename_skvar_A_lower : forall a α β,
    AtomSetImpl.remove α (varl a) ⊆ varl ({β ↤ α}a).
Proof.
  intros. ind_a a. crush. simpl+. rewrite <- IHa.
  unfold_subst_var. if_dec; clfsetdec.
Qed.

Lemma varl_rename_skvar_A_in : forall a α β,
    α ∈ varl a
  -> varl ({β ↤ α}a) ≡ (AtomSetImpl.remove α (varl a)) ∪ {{β}}.
Proof.
  intros. ind_a a. fsetdec. simpl+ in *. destr_union.
  - simpl+. decide_in α (varl a).
    + rewrite IHa. 2:fsetdec. clfsetdec.
    + rewrite rename_skvar_A_notin. 2:fsetdec. fsetdec.
  - rewrite IHa. 2:assumption. unfold_subst_var. clear IHa. if_dec; fsetdec.
Qed.

Lemma rename_skvar_A_length : forall a α__in α__out,
    length ({α__in ↤ α__out}a) = length a.
Proof. intros. unfold_rename_skvar. simpl+. reflexivity. Qed.
#[export] Hint Rewrite rename_skvar_A_length : core.
