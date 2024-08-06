Set Warnings "-notation-overridden".
Require Import Preamble.

Require Import Defs.Subst.Notation.

(*** Def *)
Definition rename_var (x__in x__out x : var) : var := (if eq_var x x__out then x__in else x).
#[export] Hint Unfold rename_var : core.
#[export] Instance substable_var : substable atom atom atom := { subst := rename_var }.

(*** Unfold_subst_var *)
#[export] Hint Unfold subst : subst_var_unfold.
#[export] Hint Unfold substable_var : subst_var_unfold.
#[export] Hint Unfold rename_var : subst_var_unfold.

Tactic Notation "unfold_subst_var" :=
  autounfold with subst_var_unfold.
Tactic Notation "unfold_subst_var" "in" hyp(H) :=
  autounfold with subst_var_unfold in H.
Tactic Notation "unfold_subst_var" "in" "*" :=
  autounfold with subst_var_unfold in *.

(*** Simplification *)
Fact subst_var_refl : forall x y,
    {y ≔ x}x = y.
Proof. intros. unfold_subst_var. if_taut. Qed.
#[export] Hint Rewrite subst_var_refl : core.

(*** Other lemmas *)
Lemma subst_var_upper : forall α1 α2 α3,
    {{({α1 ≔ α2} α3)}} ⊆ {{α1}} ∪ {{α3}}.
Proof. intros. unfold_subst_var; if_dec; clfsetdec. Qed.
