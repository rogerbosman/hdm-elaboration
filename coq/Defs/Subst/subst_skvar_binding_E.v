Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.

Require Import Defs.List.

Require Import Defs.Subst.Notation.
Require Import Defs.Subst.HdmSubst.

(*** Defs *)
(** Remove *)
Definition remove_sk_A (α : atom) : A -> A :=
  fold_right (fun (β:atom) (a:A) => (if eq_var α β then a else β :: a)) [].

Definition remove_sk_E (α:skvar) : E -> E :=
  E_fold E__Nil (fun ψ a => E__A ψ (remove_sk_A α a)) E__Var E__O.

(** Subst *)
Definition subst_skvar_binding_E (τ:T) (α : skvar) : E -> E :=
  E_fold E__Nil
    (fun ψ a => ψ ::a remove_sk_A α a)
    (fun ψ x σ => ψ ::x x :- {τ ≔ α} σ)
    (fun ψ t a σ => ψ ::o ⦇{τ ≔ α} t ▸ ⟨remove_sk_A α a⟩ {τ ≔ α} σ⦈).

(** Define notation directly since its the only deleting (subst-and-delete) substitution? *)
Notation  "{ τ ⇏ α } x"   := (subst_skvar_binding_E τ α x) (at level 50, format "{ τ  ⇏  α } x") : type_scope.
(* #[export] Instance substable_skvar_binding_Sc  : substable E T skvar := { subst := subst_skvar_binding_E }. *)

(*** Remove lems *)
Lemma remove_sk_A_app : forall α a1 a2,
    remove_sk_A α (a1 ++ a2) = remove_sk_A α a1 ++ remove_sk_A α a2.
Proof. intros. induction a1. crush. simpl+. if_taut. crush. Qed.
#[export] Hint Rewrite remove_sk_A_app : core.

(* Axiom remove_sk_E_append_A_in_A : forall α ψ a, *)
(*     remove_sk_E α (E_append_A_in_A ψ a) = E_append_A_in_A (remove_sk_E α ψ) (remove_sk_A α a). *)
(* #[export] Hint Rewrite remove_sk_E_append_A_in_A : core. *)

Lemma remove_sk_A_notin : forall α a,
    α ∉ varl a
  -> remove_sk_A α a = a.
Proof. intros. ind_a a. crush. simpl+. if_dec. 2:crush. simpl+ in H. fsetdec. Qed.

(*** Subst lems *)
Lemma E_lookup_subst_skvar_binding_E: forall (α : skvar) (τ : T) (ψ : E) (tx : tvar) (σ : Sc),
    E_lookup ψ tx = Some σ
  -> E_lookup ({τ ⇏ α} ψ) tx = Some ({τ ≔ α}σ).
Proof.
  introv IN. induction ψ.
  - crush.
  - simpl in IN. eauto.
  - simpl in IN. simpl. if_dec.
    + inverts IN. crush.
    + eauto.
  - simpl in IN. eauto.
Qed.

(* Axiom E_A_skvars_subst_skvar_binding_E_upper : forall τ α ψ, *)
(*     E_A_skvars ({τ ⇏ α} ψ) ⊆ E_A_skvars ψ. *)

Lemma E_A_skvars_subst_skvar_binding_E_lower : forall τ α ψ,
    E_A_skvars ({τ ⇏ α} ψ) ≡ AtomSetImpl.remove α (E_A_skvars ψ).
Proof.
  intros. induction ψ. 2:ind_a a. all:simpl+. 1,2,4,5:fsetdec.
  if_dec. simpl+ in *. fsetdec. simpl+ in *. clear IHψ. fsetdec.
Qed.

Lemma E_A_skvars_remove_sk_E : forall α ψ,
    E_A_skvars (remove_sk_E α ψ) ≡ AtomSetImpl.remove α (E_A_skvars ψ).
Proof.
  intros. induction ψ. 2:ind_a a. all:simpl+. 1,2,4,5:fsetdec.
  if_dec. simpl+ in *. fsetdec. simpl+ in *. clear IHψ. fsetdec.
Qed.
#[export] Hint Rewrite E_A_skvars_remove_sk_E : core.

Lemma E_lookup_remove_sk_E : forall ψ x α,
    E_lookup (remove_sk_E α ψ) x = E_lookup ψ x.
Proof. introv. induction ψ; simpl+; crush. Qed.
#[export] Hint Rewrite E_lookup_remove_sk_E : core.

Lemma remove_sk_E_notin : forall α ψ,
    α ∉ E_A_skvars ψ
  -> remove_sk_E α ψ = ψ.
Proof.
  introv NIE. induction ψ; simpl+ in *. 1,3,4:crush.
  rewrite IHψ. 2:fsetdec. rewrite remove_sk_A_notin. crush. fsetdec.
Qed.

Lemma subst_skvar_binding_E_app : forall (ψ1 ψ2:E) τ α,
    {τ ⇏ α} (ψ1 +++ ψ2) = {τ ⇏ α} ψ1 +++ {τ ⇏ α} ψ2.
Proof. introv. induction ψ2; simpl+; crush. Qed.
#[export] Hint Rewrite subst_skvar_binding_E_app : sub_dist.

Lemma subst_skvar_binding_E_notin : forall ψ α τ,
    α ∉ E_skvars ψ
  -> {τ ⇏ α} ψ = ψ.
Proof.
  intros. induction ψ; simpl+ in *.
  - crush.
  - rewrite remove_sk_A_notin. 2:fsetdec. crush.
  - rewrite subst_skvar_Sc_notin. 2:fsetdec. crush.
  - rewrite subst_skvar_Sc_notin. 2:fsetdec.
    rewrite subst_skvar_Tm_notin. 2:fsetdec.
    rewrite remove_sk_A_notin. 2:fsetdec.
    crush.
Qed.
