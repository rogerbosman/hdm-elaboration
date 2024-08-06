Set Warnings "-notation-overridden".
Require Import Preamble.

Fact E_app_empty_l : forall ψ,
    • +++ ψ = ψ.
Proof. induction ψ; crush. Qed.
#[export] Hint Rewrite E_app_empty_l : core appnil.

Fact E_app_empty_r : forall ψ,
    ψ +++ • = ψ.
Proof. reflexivity. Qed.
#[export] Hint Rewrite E_app_empty_r : core appnil.

Fact E_app_assoc : forall ψ1 ψ2 ψ3,
    ψ1 +++ (ψ2 +++ ψ3) = ψ1 +++ ψ2 +++ ψ3.
Proof. induction ψ3; crush. Qed.
#[export] Hint Rewrite E_app_assoc : core.

Fact E_A_skvars_E_skvars : forall ψ,
    E_A_skvars ψ ⊆ E_skvars ψ.
Proof. intro ψ. induction ψ; simpl+; fsetdec. Qed.

Corollary E_A_skvars_E_skvars1 : forall α ψ,
    α ∈ E_A_skvars ψ
  -> α ∈ E_skvars ψ.
Proof. intros. rewrite <- E_A_skvars_E_skvars. crush. Qed.
Corollary E_A_skvars_E_skvars2 : forall α ψ,
    α ∉ E_skvars ψ
  -> α ∉ E_A_skvars ψ.
Proof. intros. rewrite E_A_skvars_E_skvars. crush. Qed.
#[export] Hint Resolve E_A_skvars_E_skvars1 E_A_skvars_E_skvars2 : core.

Fact E_names_E_O_names : forall ψ,
    E_names ψ ⊆ E_O_names ψ.
Proof. intros. induction ψ; simpl+ in *; fsetdec. Qed.
