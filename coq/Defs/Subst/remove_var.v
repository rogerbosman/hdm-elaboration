Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.

(*** Def *)
(** remove *)
Definition remove_var_E (x:var) : E -> E :=
  E_fold E__Nil E__A (fun ψ y σ => if eq_var x y then ψ else ψ ::x y :- σ) E__O.

(** subst *)
(* Definition subst_var_E (x:var) : E -> E := *)
(*   E_fold E__Nil E__A (fun ψ y σ => if eq_var x y then ψ else ψ ::x y :- σ) E__O. *)

(*** Lems remove *)
Lemma remove_var_E_E_lookup : forall y ψ x σ,
    E_lookup ψ x = Some σ
  -> x = y \/ E_lookup (remove_var_E y ψ) x = Some σ.
Proof.
  introv LU. induction ψ. 1,2,4:crush.
  simpl+ in *. if_dec. crush. crush. simpl+ in *. if_taut. crush.
  simpl+. if_taut. crush.
Qed.

Lemma E_A_skvars_remove_var_E : forall x ψ,
    E_A_skvars (remove_var_E x ψ) ≡ E_A_skvars ψ.
Proof. intros. induction ψ; simpl+. 1,2,4:fsetdec. if_dec; simpl+; assumption. Qed.
#[export] Hint Rewrite E_A_skvars_remove_var_E : core.

Lemma remove_var_E_notin : forall ψ x,
    x ∉ E_names ψ
  -> remove_var_E x ψ = ψ.
Proof. intros. induction ψ; simpl+. 1,2,4: crush. if_dec. simpl+ in H. fsetdec. crush. Qed.

Lemma remove_var_E_app : forall ψ1 ψ2 x,
    remove_var_E x (ψ1 +++ ψ2) = remove_var_E x ψ1 +++ remove_var_E x ψ2.
Proof. intros. induction ψ2; simpl+. 1,2,4:crush. if_dec; crush. Qed.
#[export] Hint Rewrite remove_var_E_app : core.
