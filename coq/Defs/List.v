Set Warnings "-notation-overridden".
Require Import Preamble.

#[export] Hint Rewrite app_nil_r : core appnil.
#[export] Hint Rewrite app_nil_l : appnil.
#[export] Hint Rewrite app_length map_length : core.

Ltac ind_a a := induction a as [|?α a].
Ltac ind_a_rev a := induction a as [|?α a] using rev_ind.

Fact list_norm : forall (X:Type) (x:X) (xs:list X),
    x :: xs = [x] ++ xs.
Proof. reflexivity. Qed.
#[export] Hint Rewrite list_norm : norm.

(*** In *)
Fact in_a_in_varl_iff : forall α a,
    In α a
  <-> α ∈ varl a.
Proof. ind_a a; intros. crush. simpl+. split; intro H. destruct H. subst. crush. crush. destr_union; crush. Qed.

Fact in_a_in_varl : forall α a,
    In α a
  -> α ∈ varl a.
Proof. apply in_a_in_varl_iff. Qed.
Corollary in_varl_in_a : forall α a,
    α ∈ varl a
  -> In α a.
Proof. apply in_a_in_varl_iff. Qed.
#[export] Hint Resolve in_a_in_varl : core.
#[export] Hint Resolve in_varl_in_a : core.

Corollary notin_a_notin_varl : forall α a,
    ~ In α a
  -> α ∉ varl a.
Proof. unfold not in *. intros. apply in_a_in_varl_iff in H0. crush. Qed.
Corollary notin_varl_notin_a : forall α a,
    α ∉ varl a
  -> ~ In α a.
Proof. unfold not in *. intros. apply in_a_in_varl_iff in H0. crush. Qed.

