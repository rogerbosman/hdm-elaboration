Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.
Require Import Defs.HdmLems.

Require Import Defs.Freevars.

Require Import Defs.Subst.Notation.
Require Import Defs.Subst.rename_skvar_A.
Require Import Defs.Subst.HdmSubst.


(*** Def *)

Definition rename_skvar_E (α__in α__out : skvar) : E -> E :=
  E_fold E__Nil
    (fun ψ a => ψ ::a {α__in ↤ α__out} a)
    (fun ψ x σ => ψ ::x x :- {T__Var_f α__in ≔ α__out} σ)
    (fun ψ t a σ => ψ ::o ⦇{T__Var_f α__in ≔ α__out} t ▸ ⟨{α__in ↤ α__out} a⟩ {T__Var_f α__in ≔ α__out} σ⦈).

#[export] Instance renamable_skvar_E : renamable_skvar E skvar := { rename_skvar := rename_skvar_E }.

(*** E_fold *)
(** E_skvars *)
Lemma E_skvars_rename_skvar_E_upper : forall α β ψ,
    E_skvars ({β ↤ α}ψ) ⊆ E_skvars ψ ∪ {{β}}.
Proof.
  intros. induction ψ; simpl+ in *.
  - fsetdec.
  - rewrite varl_rename_skvar_A_upper. rewrite IHψ. clfsetdec.
  - rewrite fsk_Sc_subst_skvar_Sc_upper. simpl+. rewrite IHψ. clfsetdec.
  - rewrite varl_rename_skvar_A_upper. rewrite fsk_Sc_subst_skvar_Sc_upper. rewrite fsk_Tm_subst_skvar_Tm_upper. simpl+. rewrite IHψ. clfsetdec.
Qed.

(** E_A_O_skvars *)
Lemma E_A_O_skvars_rename_skvar_E_upper : forall α β ψ,
    E_A_O_skvars ({β ↤ α}ψ) ⊆ E_A_O_skvars ψ ∪ {{β}}.
Proof.
  intros. induction ψ; simpl+ in *. 1,3:fsetdec. all:rewrite varl_rename_skvar_A_upper; fsetdec.
Qed.

(*** Simplification *)
Lemma E_names_rename_skvar_E : forall ψ α β,
    E_names ({β ↤ α}ψ) = E_names ψ.
Proof. intros. induction ψ; simpl+; crush. Qed.
#[export] Hint Rewrite E_names_rename_skvar_E : core.

Lemma E_t_names_rename_skvar_E : forall ψ α β,
    E_t_names ({β ↤ α}ψ) ≡ E_t_names ψ.
Proof.
  intros. induction ψ; simpl+. 1,2,3:crush.
  rewrite IHψ. rewrite ftv_Tm_subst_skvar_Tm_eq. crush.
Qed.
#[export] Hint Rewrite E_t_names_rename_skvar_E : core.


(*** Other lemmas *)
Lemma rename_skvar_E_A_skvars_notin : forall α β ψ,
    α ∉ E_A_skvars ψ
  -> E_A_skvars ({β ↤ α}ψ) ≡ E_A_skvars ψ.
Proof.
  intros. induction ψ. 1,3,4: crush.
  simpl+ in *. rewrite IHψ. 2:crush.
  rewrite rename_skvar_A_notin. crush. fsetdec.
Qed.

Lemma E_A_skvars_rename_skvar_E_in : forall α β ψ,
    α ∈ E_A_skvars ψ
  -> E_A_skvars ({β ↤ α}ψ) ≡ (AtomSetImpl.remove α (E_A_skvars ψ)) ∪ {{β}}.
Proof.
  intros. induction ψ; simpl+ in *. fsetdec.
  - destr_union.
    + rewrite varl_rename_skvar_A_in. 2:eassumption.
      decide_in α (E_A_skvars ψ).
      * specializes IHψ IN. rewrite IHψ. clfsetdec.
      * rewrite rename_skvar_E_A_skvars_notin. 2:fsetdec. clear - NIL. fsetdec.
    + rewrite IHψ. 2:assumption. decide_in α (varl a).
      * rewrite varl_rename_skvar_A_in. 2:fsetdec. clfsetdec.
      * rewrite rename_skvar_A_notin. 2:fsetdec. fsetdec.
  - rewrite IHψ. clfsetdec. eassumption.
  - rewrite IHψ. clfsetdec. eassumption.
Qed.

Lemma E_A_skvars_rename_skvar_E_lower : forall α β ψ,
    AtomSetImpl.remove α (E_A_skvars ψ) ⊆ E_A_skvars ({β ↤ α}ψ).
Proof.
  intros. induction ψ. crush. all: simpl+; rewrite <- IHψ.
  - rewrite <- varl_rename_skvar_A_lower. fsetdec.
  - fsetdec.
  - fsetdec.
Qed.

Lemma rename_skvar_E_notin : forall α β ψ,
    α ∉ E_skvars ψ
  -> ({β ↤ α}ψ) = ψ.
Proof.
  intros. induction ψ; simpl+ in *. crush.
  - rewrite rename_skvar_A_notin. 2:fsetdec.
    rewrite IHψ. 2:fsetdec.
    crush.
  - rewrite subst_skvar_Sc_notin. 2:fsetdec.
    crush.
  - rewrite subst_skvar_Tm_notin. 2:fsetdec.
    rewrite rename_skvar_A_notin. 2:fsetdec.
    rewrite subst_skvar_Sc_notin. 2:fsetdec.
    crush.
Qed.

Lemma rename_skvar_E_A_O_skvars_notin : forall α β ψ,
    α ∉ E_A_O_skvars ψ
  -> E_A_O_skvars ({β ↤ α}ψ) = E_A_O_skvars ψ.
Proof.
  intros. induction ψ; simpl+ in *. 1,3:crush.
  - rewrite rename_skvar_A_notin. 2:fsetdec.
    rewrite IHψ. 2:fsetdec.
    crush.
  - rewrite rename_skvar_A_notin. 2:fsetdec.
    rewrite IHψ. 2:fsetdec.
    crush.
Qed.

Lemma rename_skvar_E_app : forall α β (ψ1 ψ2:E),
    {β ↤ α}(ψ1 +++ ψ2) = ({β ↤ α}ψ1) +++ ({β ↤ α}ψ2).
Proof. intros. induction ψ2; simpl+; crush. Qed.
#[export] Hint Rewrite rename_skvar_E_app : sub_dist.
