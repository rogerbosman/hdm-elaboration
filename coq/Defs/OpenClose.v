Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.
Require Import Defs.HdmLems.

Require Import Defs.E.
Require Import Defs.ERels.
Require Import Defs.FrA.
Require Import Defs.Lc.
Require Import Defs.List.
Require Import Defs.Rename.
Require Import Defs.Subst.
Require Import Defs.Sub.

(*** Notation *)
Notation "'Λ' a ⬪ t"  := (close_Tm_wrt_A t a) (at level 70, format "'Λ'  a  ⬪  t") : type_scope.
Notation "∀ a ⬪ t"  := (close_Sc_wrt_A t a) (at level 70, format "∀  a  ⬪  t") : type_scope.

(*** Simplification *)
Section open_Sc_wrt_T_simpl.
  Variable τ : T.

  Fact open_Sc_wrt_T_T : forall τ',
      open_Sc_wrt_T (S__T τ') τ = S__T (open_T_wrt_T τ' τ).
  reflexivity. Qed.
End open_Sc_wrt_T_simpl.
#[export] Hint Rewrite open_Sc_wrt_T_T : core.

Section open_T_wrt_T_simpl.
  Variable τ : T.

  Fact open_T_wrt_T_Var_f : forall α,
      open_T_wrt_T (T__Var_f α) τ = T__Var_f α.
  reflexivity. Qed.

  Fact open_T_wrt_T_Unit :
      open_T_wrt_T T__Unit τ = T__Unit.
  reflexivity. Qed.

  Fact open_T_wrt_T_Bool :
      open_T_wrt_T T__Bool τ = T__Bool.
  reflexivity. Qed.

  Fact open_T_wrt_T_Fun : forall τ1 τ2,
      open_T_wrt_T (T__Fun τ1 τ2) τ = T__Fun (open_T_wrt_T τ1 τ) (open_T_wrt_T τ2 τ).
  reflexivity. Qed.
End open_T_wrt_T_simpl.
#[export] Hint Rewrite open_T_wrt_T_Var_f open_T_wrt_T_Unit open_T_wrt_T_Bool open_T_wrt_T_Fun : core.

Section open_Tm_wrt_T_simpl.
  Variable τ : T.

  Fact open_Tm_wrt_T_Var_b : forall n,
      open_Tm_wrt_T (t__Var_b n) τ = t__Var_b n.
  reflexivity. Qed.

  Fact open_Tm_wrt_T_Var_f : forall α,
      open_Tm_wrt_T (t__Var_f α) τ = t__Var_f α.
  reflexivity. Qed.

  Fact open_Tm_wrt_T_Unit :
      open_Tm_wrt_T t__Unit τ = t__Unit.
  reflexivity. Qed.

  Fact open_Tm_wrt_T_True :
      open_Tm_wrt_T t__True τ = t__True.
  reflexivity. Qed.

  Fact open_Tm_wrt_T_False :
      open_Tm_wrt_T t__False τ = t__False.
  reflexivity. Qed.

  Fact open_Tm_wrt_T_App : forall t1 t2,
      open_Tm_wrt_T (t__App t1 t2) τ = t__App (open_Tm_wrt_T t1 τ) (open_Tm_wrt_T t2 τ).
  reflexivity. Qed.

  Fact open_Tm_wrt_T_TApp : forall t τ',
      open_Tm_wrt_T (t__TApp t τ') τ = t__TApp (open_Tm_wrt_T t τ) (open_T_wrt_T τ' τ).
  reflexivity. Qed.

  Fact open_Tm_wrt_T_Lam : forall τ' t,
      open_Tm_wrt_T (t__Lam τ' t) τ = t__Lam (open_T_wrt_T τ' τ) (open_Tm_wrt_T t τ).
  reflexivity. Qed.
End open_Tm_wrt_T_simpl.
#[export] Hint Rewrite open_Tm_wrt_T_Var_b open_Tm_wrt_T_Var_f open_Tm_wrt_T_Unit open_Tm_wrt_T_True open_Tm_wrt_T_False open_Tm_wrt_T_App open_Tm_wrt_T_TApp open_Tm_wrt_T_Lam : core.

Section open_Tm_wrt_Tm_simpl.
  Variable t : Tm.

  Fact open_Tm_wrt_Tm_Var_f : forall α,
      open_Tm_wrt_Tm (t__Var_f α) t = t__Var_f α.
  reflexivity. Qed.

  Fact open_Tm_wrt_Tm_Unit :
      open_Tm_wrt_Tm t__Unit t = t__Unit.
  reflexivity. Qed.

  Fact open_Tm_wrt_Tm_True :
      open_Tm_wrt_Tm t__True t = t__True.
  reflexivity. Qed.

  Fact open_Tm_wrt_Tm_False :
      open_Tm_wrt_Tm t__False t = t__False.
  reflexivity. Qed.

  Fact open_Tm_wrt_Tm_App : forall t1 t2,
      open_Tm_wrt_Tm (t__App t1 t2) t = t__App (open_Tm_wrt_Tm t1 t) (open_Tm_wrt_Tm t2 t).
  reflexivity. Qed.

  Fact open_Tm_wrt_Tm_TApp : forall t' τ,
      open_Tm_wrt_Tm (t__TApp t' τ) t = t__TApp (open_Tm_wrt_Tm t' t) τ.
  reflexivity. Qed.
End open_Tm_wrt_Tm_simpl.
#[export] Hint Rewrite open_Tm_wrt_Tm_Var_f open_Tm_wrt_Tm_Unit open_Tm_wrt_Tm_True open_Tm_wrt_Tm_False open_Tm_wrt_Tm_App open_Tm_wrt_Tm_TApp : core.

(*** Lemmas *)
Lemma subst_skvar_Sc_close_Sc_wrt_A : forall τ α σ a,
    lc(τ)
  -> α ∉ varl a
  -> fv__α(τ) ∐ varl a
  -> { τ ≔ α } close_Sc_wrt_A σ a = close_Sc_wrt_A ({ τ ≔ α } σ) a.
Proof.
  introv LC NIA DISJ. ind_a a. crush. simpl+ in *. fequals. rewrite <- IHa.
  rewrite subst_skvar_Sc_close_Sc_wrt_T. reflexivity.
  assumption. fsetdec. eapply in_disj2. eassumption. fsetdec. fsetdec. disj_sub.
Qed.

Lemma subst_skvar_Tm_close_Tm_wrt_A : forall τ α t a,
    lc(τ)
  -> α ∉ varl a
  -> fv__α(τ) ∐ varl a
  -> { τ ≔ α } close_Tm_wrt_A t a = close_Tm_wrt_A ({ τ ≔ α } t) a.
Proof.
  introv LC NIA DISJ. ind_a a. crush. simpl+ in *. fequals. rewrite <- IHa.
  rewrite subst_skvar_Tm_close_Tm_wrt_T. reflexivity.
  assumption. fsetdec. eapply in_disj2. eassumption. fsetdec. fsetdec. disj_sub.
Qed.

Lemma subst_tvar_Tm_close_Tm_wrt_A : forall a t1 x t2,
    lc(t1)
  -> varl a ∐ fv__α(t1)
  -> {t1 ≔__x x} (close_Tm_wrt_A t2 a) = close_Tm_wrt_A ({t1 ≔__x x} t2) a.
Proof.
  intros. ind_a a. crush. simpl+. rewrite <- IHa. fequals.
  apply subst_tvar_Tm_close_Tm_wrt_T. assumption. eapply in_disj1. eassumption. fsetdec+.
  disj_sub.
Qed.

Fact close_Sc_wrt_T_subst_skvar_Sc : forall α β σ,
    β ∉ fv__α(close_Sc_wrt_T α σ)
  -> close_Sc_wrt_T α σ = close_Sc_wrt_T β ({T__Var_f β ≔ α} σ).
Proof.
  introv NIT. rewrite subst_skvar_Sc_spec.
  rewrite close_Sc_wrt_T_open_Sc_wrt_T; auto.
Qed.

Fact close_Tm_wrt_T_subst_skvar_Tm : forall α β t,
    β ∉ fv__α(close_Tm_wrt_T α t)
  -> close_Tm_wrt_T α t = close_Tm_wrt_T β ({T__Var_f β ≔ α} t).
Proof.
  introv NIT. rewrite subst_skvar_Tm_spec.
  rewrite close_Tm_wrt_T_open_Tm_wrt_T; auto.
Qed.

(*** Close subst samevar *)
Lemma subst_tvar_Tm_close_Tm_wrt_Tm_samevar : forall y x t,
    y ∉ fv__x(close_Tm_wrt_Tm x t)
  -> close_Tm_wrt_Tm y ({ t__Var_f y ≔__x x } t) =
    close_Tm_wrt_Tm x t.
Proof.
  introv NI. rewrite subst_tvar_Tm_spec. rewrite close_Tm_wrt_Tm_open_Tm_wrt_Tm. reflexivity. eassumption.
Qed.

Lemma subst_tvar_T_close_Tm_wrt_T_samevar : forall β α (t:Tm),
    β ∉ fv__α(close_Tm_wrt_T α t)
  -> close_Tm_wrt_T β ({ T__Var_f β ≔ α } t) = close_Tm_wrt_T α t.
Proof.
  introv NI. rewrite subst_skvar_Tm_spec. rewrite close_Tm_wrt_T_open_Tm_wrt_T. reflexivity. eassumption.
Qed.

(*** Open subst samevar *)
Lemma subst_skvar_Sc_open_Sc_wrt_T_samevar : forall α__in α__out σ,
    α__out ∉ fv__α(σ)
  -> {T__Var_f α__in ≔ α__out}open_Sc_wrt_T σ (T__Var_f α__out) = open_Sc_wrt_T σ (T__Var_f α__in).
Proof. intros. rewrite subst_skvar_Sc_spec. rewrite close_Sc_wrt_T_open_Sc_wrt_T. crush. assumption. Qed.

(*** WrT A *)
Lemma close_Tm_wrt_A_app : forall a1 a2 t,
    Λ a1 ++ a2 ⬪ t = Λ a1⬪ Λ a2⬪ t.
Proof. introv. ind_a a1. crush. simpl+. crush. Qed.

Lemma close_Sc_wrt_A_app : forall a1 a2 σ,
    ∀ a1 ++ a2 ⬪ σ = ∀ a1⬪ ∀ a2⬪ σ.
Proof. introv. ind_a a1. crush. simpl+. crush. Qed.

Lemma fsk_Tm_close_Tm_wrt_A : forall a t,
    fv__α(Λ a ⬪ t) ≡ fv__α(t) ∖ varl a.
Proof. intros a t. ind_a a. crush. intros. simpl+. rewrite fsk_Tm_close_Tm_wrt_T. fsetdec. Qed.

Lemma fsk_Sc_close_Sc_wrt_A : forall a σ,
    fv__α(∀ a ⬪ σ) ≡ fv__α(σ) ∖ varl a.
Proof. intros a σ. ind_a a. crush. intros. simpl+. rewrite fsk_Sc_close_Sc_wrt_T. fsetdec. Qed.

Lemma subst_skvar_Tm_close_Tm_wrt_A' : forall a α__in α__out t,
    α__in ∉ fv__α(t)
  -> α__in ∉ varl a
  -> {T__Var_f α__in ≔ α__out}(Λ a ⬪ t) = (Λ {α__in ↤ α__out}a ⬪ {T__Var_f α__in ≔ α__out}t).
Proof.
  intro a. ind_a a. crush. introv NI1 NI2. simpl+ in *.
  rewrite <- IHa. 2,3:fsetdec.
  fequals. unfold rename_var. if_dec.
  - subst_notin'. 2:rewrite fsk_Tm_close_Tm_wrt_T; fsetdec.
    rewrite subst_tvar_T_close_Tm_wrt_T_samevar. reflexivity.
    rewrite fsk_Tm_close_Tm_wrt_T. rewrite fsk_Tm_close_Tm_wrt_A. fsetdec.
  - rewrite subst_skvar_Tm_close_Tm_wrt_T. reflexivity.
    crush. crush. simpl+. fsetdec.
Qed.

Lemma close_Tm_wrt_A_snoc : forall a α σ,
    ∀ a ++ [α] ⬪ σ = ∀ a ⬪ S__Forall (close_Sc_wrt_T α σ).
Proof. intro a. ind_a a. crush. intros. simpl+. crush. Qed.
#[export] Hint Rewrite close_Tm_wrt_A_snoc : core.

Lemma Sub_app_Tm_close_Tm_wrt_A : forall θ t a,
    lc(θ)
  -> skvars_codom_Sub θ ∐ varl a
  -> dom_Sub θ ∐ varl a
  -> ⟦θ ▹ close_Tm_wrt_A t a⟧ = close_Tm_wrt_A ⟦θ ▹ t⟧ a.
Proof.
  introv LC DISJ1 DISJ2. ind_Sub θ. crush.
  dist. simpl+ in *. rewrite IHθ. 2:eauto. 2:clear - DISJ1; disj_sub. 2:clear - DISJ2; disj_sub.
  apply subst_skvar_Tm_close_Tm_wrt_A. eauto. in_disj. clear - DISJ1. disj_sub.
Qed.

Fact ftv_close_Tm_wrt_A : forall a t,
    fv__x(Λ a⬪ t) ≡ fv__x(t).
Proof.
  intros. ind_a a. crush. simpl+.
  rewrite ftv_Tm_close_Tm_wrt_T. crush.
Qed.
#[export] Hint Rewrite ftv_close_Tm_wrt_A : core.

(*** Rename *)
Lemma Rename_gen_T : forall θ τ,
    Rename_codom_list θ ### (varl (Rename_dom_list θ) ∪ fv__α(τ))
  -> (∀ (Rename_dom_list θ)⬪ τ) = (∀ (Rename_codom_list θ)⬪ ⟦(Rename_lift θ) ▹ τ⟧).
Proof.
  intro θ. ind_Rn θ; simpl+. crush.
  introv FR. fequals. rewrite IHθ. 2:eapply FrA_cons1 in FR; FrA_L_sub. dist.
  forwards: FrA_props1 FR.
  rewrite <- subst_skvar_Sc_close_Sc_wrt_A. 2:crush.
  rewrite subst_skvar_Sc_spec. rewrite close_Sc_wrt_T_open_Sc_wrt_T. crush.
  rewrite fsk_Sc_close_Sc_wrt_T. rewrite fsk_Sc_close_Sc_wrt_A.
  rewrite Sub_app_Sc_fsk. simpl+.
  assert (α ∉ fv__α(τ)). destruct FR.
    eapply in_disj1. eapply atoms_facts.disjoint_Subset. eapply H1. reflexivity. reldec. reldec.
  assert (α ∉ varl (Rename_codom_list θ)). destruct FR. inverts H. eauto.
  fsetdec.
  destruct FR. eapply in_disj2. eapply atoms_facts.disjoint_Subset. eassumption. reldec. reflexivity. reldec.
  inverts H. simpl+. eauto.
Qed.

Lemma Rename_gen_Tm : forall θ t,
    Rename_codom_list θ ### (varl (Rename_dom_list θ) ∪ fv__α(t))
  -> (Λ (Rename_dom_list θ)⬪ t) = (Λ (Rename_codom_list θ)⬪ ⟦(Rename_lift θ) ▹ t⟧).
Proof.
  intro θ. ind_Rn θ; simpl+. crush.
  introv FR. fequals. rewrite IHθ. 2:eapply FrA_cons1 in FR; FrA_L_sub. dist.
  forwards: FrA_props1 FR.
  rewrite <- subst_skvar_Tm_close_Tm_wrt_A. 2:crush.
  rewrite subst_skvar_Tm_spec. rewrite close_Tm_wrt_T_open_Tm_wrt_T. crush.
  rewrite fsk_Tm_close_Tm_wrt_T. rewrite fsk_Tm_close_Tm_wrt_A.
  rewrite Sub_app_Tm_fsk. simpl+.
  assert (α ∉ fv__α(t0)). destruct FR.
    eapply in_disj1. eapply atoms_facts.disjoint_Subset. eapply H1. reflexivity. reldec. reldec.
  assert (α ∉ varl (Rename_codom_list θ)). destruct FR. inverts H. eauto.
  fsetdec.
  destruct FR. eapply in_disj2. eapply atoms_facts.disjoint_Subset. eassumption. reldec. reflexivity. reldec.
  inverts H. simpl+. eauto.
Qed.
