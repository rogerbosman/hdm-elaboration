Set Warnings "-notation-overridden".

Require Import Preamble.
Require Import Defs.HdmLems.

Require Import Defs.FrA.
Require Import Defs.List.
Require Import Defs.Sub.
Require Import Defs.Subst.

(*** Rename *)

Ltac ind_Rn θ := induction θ as [|[?α ?β] ?θ].
Ltac ind_Rn_rev θ := induction θ as [|[?α ?β] ?θ] using rev_ind.

Definition Rename : Set := list (skvar * skvar).
Definition Rename_lift : Rename -> Sub := map (fun p => (T__Var_f (fst p), snd p)).

Definition Rename_lift_app : forall θ1 θ2,
    Rename_lift (θ1 ++ θ2) = Rename_lift θ1 ++ Rename_lift θ2.
Proof. intros. ind_Rn θ1; crush. Qed.
#[export] Hint Rewrite Rename_lift_app : sub_dist.

Definition Rename_app_var : skvar -> Rename -> skvar := fold_right (uncurry rename_var).

Definition Rename_app_Sub (θ:Rename) : A -> A := map (flip Rename_app_var θ).

Lemma Rename_app_Sub_nil : forall a,
    Rename_app_Sub [] a = a.
Proof. intros. ind_a a. simpl+. crush. simpl+. crush. Qed.

Lemma Rename_app_Sub_cons : forall a α__in α__out θ,
    Rename_app_Sub ((α__in, α__out) :: θ) a = {α__in ↤ α__out}(Rename_app_Sub θ a).
Proof. intros. ind_a a. simpl+. crush. simpl+. crush. Qed.

Lemma Rename_app_var_notin : forall θ α,
    α ∉ dom_Sub (Rename_lift θ)
  -> Rename_app_var α θ = α.
Proof.
  intro θ. ind_Sub θ. crush. intros. simpl+.
  rewrite IHθ. 2:simpl+ in H; fsetdec. unfold rename_var. if_dec. simpl+ in H. fsetdec. crush.
Qed.

Definition Rename_dom_list : Rename -> A := map snd.
Definition Rename_codom_list : Rename -> A := map fst.

Fact Rename_dom_list_app : forall θ1 θ2,
    Rename_dom_list (θ1 ++ θ2) = Rename_dom_list θ1 ++ Rename_dom_list θ2.
Proof. introv. unfolds. rewrite map_app. crush. Qed.
#[export] Hint Rewrite Rename_dom_list_app : core.

Fact Rename_codom_list_app : forall θ1 θ2,
    Rename_codom_list (θ1 ++ θ2) = Rename_codom_list θ1 ++ Rename_codom_list θ2.
Proof. introv. unfolds. rewrite map_app. crush. Qed.
#[export] Hint Rewrite Rename_codom_list_app : core.

Lemma dom_Sub_Rename_lift : forall θ,
    dom_Sub (Rename_lift θ) ≡ varl (Rename_dom_list θ).
Proof. intros. ind_Sub θ; simpl+; fsetdec. Qed.
Lemma codom_Sub_Rename_lift : forall θ,
    skvars_codom_Sub (Rename_lift θ) ≡ varl (Rename_codom_list θ).
Proof. intros. ind_Sub θ; simpl+; fsetdec. Qed.
#[export] Hint Rewrite dom_Sub_Rename_lift codom_Sub_Rename_lift : core.
