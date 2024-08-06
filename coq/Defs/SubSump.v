Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.
Require Import Defs.HdmLems.

Require Import Defs.FrA.
Require Import Defs.List.
Require Import Defs.OpenClose.
Require Import Defs.Subst.
(* Require Import Defs.TmTy. *)
Require Import Defs.WfSTt.

(*** SubSumpTm *)
Lemma SubSumpTm_rename_skvar_E : forall α β ψ t__in σ t__out τ,
    SubSumpTm ψ t__in σ t__out τ
  -> SubSumpTm ({β ↤ α} ψ) ({T__Var_f β ≔ α}t__in) ({T__Var_f β ≔ α}σ) ({T__Var_f β ≔ α}t__out) ({T__Var_f β ≔ α}τ).
Proof.
  introv SS. induction SS.
  - applys SST__M.
  - simpl+. applys SST__L. 2:applys_eq IHSS.
    + eauto using WfT_rename_skvar_E.
    + rewrite subst_skvar_Sc_open_Sc_wrt_T. 2:crush. reflexivity.
Qed.

Lemma SubSumpTm_subst_name : forall x__in x__out t1 ψ σ t2 τ,
    SubSumpTm ψ t1 σ t2 τ
  -> SubSumpTm ({x__in ↤__x x__out}ψ) ({t__Var_f x__in ≔__x x__out} t1) σ ({t__Var_f x__in ≔__x x__out}t2) τ.
Proof.
  introv SS. dependent induction SS.
  - crush.
  - econstructor. eauto using WfT_subst_name. eassumption.
Qed.

Lemma SubSumpTm'_rename_skvar : forall α β ψ t__in σ1 t__out σ2,
    SubSumpTm' ψ t__in σ1 t__out σ2
  -> SubSumpTm' ({β ↤ α} ψ) ({T__Var_f β ≔ α}t__in) ({T__Var_f β ≔ α}σ1) ({T__Var_f β ≔ α}t__out) ({T__Var_f β ≔ α}σ2).
Proof.
  introv SS. induction SS.
  - applys SST'__M. auto using SubSumpTm_rename_skvar_E.
  - simpl+. applys SST'__R (L ∪ {{α}}). intros α' NIL__α'.
    assert (α' <> α). fsetdec.
    specializes H α'. specializes H. fsetdec.
    applys_eq H.
    + simpl+. unfold rename_var. if_taut. reflexivity.
    + rewrite subst_skvar_Tm_open_Tm_wrt_T. 2:crush. simpl+. if_taut.
    + rewrite subst_skvar_Sc_open_Sc_wrt_T. 2:crush. simpl+. if_taut.
Qed.

(*** SubSumpTmA *)
Lemma SubSumpTmA_FrA : forall ψ t1 σ t2 a τ,
    SubSumpTmA ψ t1 σ t2 a τ
  -> a ### E_skvars ψ.
Proof. introv SS. induction SS. crush. simpl+ in IHSS. eapply FrA_app'. eassumption. FrA_L_sub. Qed.
