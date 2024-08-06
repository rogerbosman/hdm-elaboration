Set Warnings "-notation-overridden".
Require Import Preamble.
Require Import Defs.HdmLems.

Require Import Defs.Subst.Notation.
Require Import Defs.Subst.rename_var.
Require Import Defs.Subst.HdmSubst.

Require Import Defs.Freevars.

(*** Def *)
Definition rename_name_E (x__in x__out : var) : E -> E :=
  E_fold E__Nil E__A (fun ψ x σ => E__Var ψ ({ x__in ≔ x__out } x) σ) (fun ψ t a σ => E__O ψ ({ t__Var_f x__in ≔__x x__out }t) a σ).

#[export] Instance renamable_name_E : renamable_name E var := { rename_name := rename_name_E }.

(*** E_fold *)
(** E_skvars *)
Lemma E_skvars_subst_name : forall x__in x__out ψ,
    E_skvars ({x__in ↤__x x__out}ψ) ≡ E_skvars ψ.
Proof. intros. induction ψ; simpl+; fsetdec+. Qed.
#[export] Hint Rewrite E_skvars_subst_name : core.
Lemma E_A_skvars_subst_name : forall x__in x__out ψ,
    E_A_skvars ({x__in ↤__x x__out}ψ) ≡ E_A_skvars ψ.
Proof. intros. induction ψ; fsetdec+. Qed.
#[export] Hint Rewrite E_A_skvars_subst_name : core.
Lemma E_A_O_skvars_subst_name : forall x__in x__out ψ,
    E_A_O_skvars ({x__in ↤__x x__out}ψ) ≡ E_A_O_skvars ψ.
Proof. intros. induction ψ; fsetdec+. Qed.
#[export] Hint Rewrite E_A_O_skvars_subst_name : core.

(*** Other lemmas *)
Lemma subst_name_E_notin : forall ψ x__in x__out,
    x__out ∉ (E_names ψ ∪ E_t_names ψ)
  -> {x__in ↤__x x__out}ψ = ψ.
Proof.
  intros. induction ψ; simpl+ in *. 1,2:crush.
  - rewrite IHψ. 2:fsetdec+. simpl+ in H. fequals. unfold_subst_var. if_dec. 2:crush.
    false. apply H. fsetdec.
  - rewrite IHψ. 2:fsetdec+. fequals.
    apply subst_tvar_Tm_notin. fsetdec.
Qed.

Lemma rename_name_E_fresh_eq : forall ψ x__in x__out,
    x__out ∉ E_O_names ψ
  -> {x__in ↤__x x__out}ψ = ψ.
Proof.
  introv NIE. induction ψ. crush.
  - simpl+. fequals. apply IHψ. fsetdec+.
  - simpl+. fequals. apply IHψ. fsetdec+.
    unfold_subst_var. if_dec. 2:crush.
    false. apply NIE. fsetdec+.
  - simpl+. fequals. apply IHψ. fsetdec+.
    apply subst_tvar_Tm_fresh_eq. simpl+ in NIE. fsetdec.
Qed.
