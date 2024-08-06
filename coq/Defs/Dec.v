Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.
Require Import Defs.HdmLems.

Require Import Defs.ELookup.
Require Import Defs.ERels.
Require Import Defs.List.
Require Import Defs.FrA.
Require Import Defs.NoDup.
Require Import Defs.OpenClose.
Require Import Defs.Sub.
Require Import Defs.Subst.
Require Import Defs.SubSump.

(*** Notation *)
Require Export Defs.Dec.Notation.

(*** Facts *)
Fact Dec_lc (ψ:E) (e:Ex) (τ:T) (t:Tm) :
    ψ ⊢d e ▸ τ ⤳ t
  -> lc(e).
Proof. introv DEC. induction DEC; crush. Qed.
#[export] Hint Resolve Dec_lc : core.

(*** Dec_subst_name *)
Lemma Dec_subst_name : forall x__in x__out (e:Ex) (ψ:E) (τ:T) (t:Tm),
    ψ ⊢d e ▸ τ ⤳ t
  -> x__in ∉ E_names ψ
  -> {x__in ↤__x x__out} ψ ⊢d {e__Var_f x__in ≔__x x__out} e ▸ τ ⤳ {t__Var_f x__in ≔__x x__out} t.
Proof.
  introv DEC NIE. induction DEC.
  - simpl+. applys_eq Dec__Var.
    + eauto using E_lookup_subst_name.
    + applys_eq SubSumpTm_subst_name; try eassumption. simpl+. crush.
  - crush.
  - simpl+. applys Dec__Abs (L ∪ {{x__in}} ∪ {{x__out}}).
    + eauto using WfT_subst_name.
    + intros x NIL__x. specializes H x. specializes H. fsetdec. simpl+. fsetdec. simpl+ in H.
      applys_eq H.
      * fequals. unfold_subst_var. if_dec. fsetdec. fsetdec.
      * rewrite subst_var_Ex_open_Ex_wrt_Ex. simpl+. fequals. fequals. if_dec. fsetdec. crush. crush.
      * rewrite subst_tvar_Tm_open_Tm_wrt_Tm. simpl+. fequals. fequals. if_dec. fsetdec. crush. crush.
  - specializes IHDEC1. fsetdec. specializes IHDEC2. fsetdec.
    simpl+. eauto.
  - simpl+. applys_eq (Dec__Let (L ∪ {{x__in}} ∪ {{x__out}})).
    + rewrite subst_tvar_Tm_open_Tm_wrt_Tm. 2:crush. fequals.
      apply subst_tvar_Tm_close_Tm_wrt_A. crush. simpl+. crush.
    + applys_eq IHDEC. fsetdec+.
    + intros x NIL__x. applys_eq (H x); simpl+.
      * fequals. unfold_subst_var. if_dec. fsetdec. fsetdec.
      * rewrite subst_var_Ex_open_Ex_wrt_Ex. simpl+. fequals. fequals. if_dec. fsetdec. crush. crush.
      * rewrite subst_tvar_Tm_open_Tm_wrt_Tm. simpl+. fequals. fequals. if_dec. fsetdec. crush. crush.
      * fsetdec.
      * fsetdec.
    + simpl+. eassumption.
Qed.

Corollary Dec_subst_name_open : forall x__out ψ e τ t σ,
    (ψ ::x x__out :- σ) ⊢d open_Ex_wrt_Ex e (e__Var_f x__out) ▸ τ ⤳ open_Tm_wrt_Tm t (t__Var_f x__out)
  -> x__out ∉ E_names ψ ∪ E_t_names ψ ∪ fv__x(e) ∪ fv__x(t)
  -> forall x__in, x__in ∉ (E_names (ψ ::x x__out :- σ))
  -> (ψ ::x x__in :- σ) ⊢d open_Ex_wrt_Ex e (e__Var_f x__in) ▸ τ ⤳ open_Tm_wrt_Tm t (t__Var_f x__in).
Proof.
  introv DEC NIE1 NIE2. forwards: Dec_subst_name x__in x__out. eassumption. fsetdec.
  applys_eq H.
  - simpl+. fequals. symmetry. apply subst_name_E_notin. fsetdec.
  - rewrite subst_var_Ex_open_Ex_wrt_Ex. simpl+. if_taut.
    fequals. symmetry. apply subst_var_Ex_notin. fsetdec. crush.
  - rewrite subst_tvar_Tm_open_Tm_wrt_Tm. simpl+. if_taut.
    fequals. symmetry. apply subst_tvar_Tm_notin. fsetdec. crush.
Qed.

(*** Dec_rename_skvar *)
Lemma Dec_rename_skvar_E__lethelper1 : forall a α__out α__in σ,
    α__in ∉ (fv__α(σ) ∪ varl a)
  -> {T__Var_f α__in ≔ α__out}close_Sc_wrt_A σ a = close_Sc_wrt_A ({T__Var_f α__in ≔ α__out}σ) ({α__in ↤ α__out}a).
Proof.
  intro a. ind_a a. crush.
  intros α__out α__in σ NIS. simpl+. fequals. rewrite <- IHa.
  unfold_subst_var. if_dec.
  - rewrite <- close_Sc_wrt_T_subst_skvar_Sc. apply subst_skvar_Sc_notin. intro.
    rewrite fsk_Sc_close_Sc_wrt_T in H. fsetdec.
    rewrite fsk_Sc_close_Sc_wrt_T. rewrite fsk_close_Sc_wrt_A. fsetdec.
  - apply subst_skvar_Sc_close_Sc_wrt_T. crush. crush. simpl+. intro.
    rewrite singleton_iff in H. subst. apply NIS. fsetdec+.
  - fsetdec+.
Qed.

Lemma Dec_rename_skvar_E__lethelper2 : forall a α__out α__in t,
    α__in ∉ (fv__α(t) ∪ varl a)
  -> {T__Var_f α__in ≔ α__out} (close_Tm_wrt_A t a) = close_Tm_wrt_A ({T__Var_f α__in ≔ α__out}t) ({α__in ↤ α__out}a).
Proof.
  intro a. ind_a a. crush.
  introv NIS. simpl+. fequals. rewrite <- IHa.
  unfold_subst_var. if_dec.
  - rewrite <- close_Tm_wrt_T_subst_skvar_Tm. apply subst_skvar_Tm_notin. intro.
    rewrite fsk_Tm_close_Tm_wrt_T in H. fsetdec.
    rewrite fsk_Tm_close_Tm_wrt_T. rewrite fsk_close_Tm_wrt_A. fsetdec.
  - apply subst_skvar_Tm_close_Tm_wrt_T. crush. crush. simpl+. intro.
    rewrite singleton_iff in H. subst. apply NIS. fsetdec+.
  - fsetdec+.
Qed.

Lemma Dec_subst : forall α ψ e τ t,
    ψ ⊢d e ▸ τ ⤳ t
  -> exists L, forall β, β ∉ L
  -> {β ↤ α} ψ ⊢d e ▸ {T__Var_f β ≔ α} τ ⤳ {T__Var_f β ≔ α} t.
Proof.
  introv DEC. induction DEC.
  - exists empty. intros β NIL__β.
    econstructor. eauto using E_lookup_rename_skvar_E. applys_eq SubSumpTm_rename_skvar_E. 2:eassumption. crush.
  - exists empty. intros β NIL__β.
    econstructor; crush.
  - forwards [x NIL__x]: atom_fresh (L ∪ E_names ψ ∪ E_t_names ψ ∪ fv__x(e) ∪ fv__x(t0)).
    specializes H x. specializes H. fsetdec. destruct H as [L' IH].
    exists L'. intros β NIL__β. specializes IH β. specializes IH. clear - NIL__β. fsetdec.
    simpl+. applys Dec__Abs (E_names ({β ↤ α}ψ ::x x :- S__T (subst_skvar_T (T__Var_f β) α τ1))).
    eauto using WfT_rename_skvar_E.
    intros y NIL__y. simpl+ in IH.
    rewrite subst_skvar_Tm_open_Tm_wrt_Tm in IH. simpl+ in IH.
    eapply Dec_subst_name_open in IH. eassumption. simpl+. clear - NIL__x.
    rewrite ftv_Tm_subst_skvar_Tm_upper. fsetdec.
    eassumption.
  - destruct IHDEC1 as [L1 IHDEC1]. simpl+ in IHDEC1.
    destruct IHDEC2 as [L2 IHDEC2]. simpl+ in IHDEC2.
    exists (L1 ∪ L2). intros β NIL__β.
    simpl+. econstructor. eapply IHDEC1. fsetdec. eapply IHDEC2. fsetdec.
  - destruct IHDEC as [L1 IH1].
    forwards [x NIL__x]: atom_fresh (L ∪ ((E_names ψ ∪ E_t_names ψ) ∪ fv__x(e2)) ∪ fv__x(t2)).
    specializes H x. specializes H. fsetdec.
    destruct H as [L2 IH2].
    exists (L1 ∪ L2 ∪ fv__α(S__T τ1) ∪ varl a ∪ E_skvars ψ ∪ fv__α(t1)). intros β NIL__β.
    specializes IH1 β. specializes IH1. fsetdec. simpl+ in IH1.
    specializes IH2 β. specializes IH2. fsetdec. simpl+ in IH2.
    forwards: Dec__Let (E_names ψ ∪ Metatheory.singleton x).
    + apply IH1.
    + intros y NILy. simpl+ in IH2.
      forwards IH2': Dec_subst_name_open ({T__Var_f β ≔ α} t2) y. applys_eq IH2.
      rewrite subst_skvar_Tm_open_Tm_wrt_Tm. simpl+. reflexivity.
      simpl+. rewrite ftv_Tm_subst_skvar_Tm_upper. clear - NIL__x. fsetdec.
      simpl+. fsetdec. applys_eq IH2'. simpl+. fequals.
      symmetry. apply Dec_rename_skvar_E__lethelper1. clear - NIL__β. fsetdec.
    + unfolds. split. apply NoDup_rename_skvar_A. eauto. fsetdec.
      destruct (decide_in α (varl a)).
      * rewrite varl_rename_skvar_A_upper.
        assert (α ∉ E_skvars ψ). unfolds in H0. eapply in_disj1; jauto.
        rewrite rename_skvar_E_notin. 2:fsetdec.
        disj_union. jauto. clear - NIL__β. simpl+. fsetdec.
      * rewrite rename_skvar_A_notin. 2:assumption.
        rewrite E_skvars_rename_skvar_E_upper.
        symmetry. disj_union. symmetry. eauto. simpl+. fsetdec.
    + applys_eq H. rewrite subst_skvar_Tm_open_Tm_wrt_Tm. fequals.
      apply Dec_rename_skvar_E__lethelper2. clear - NIL__β. fsetdec.
Qed.

(*** Dec_subst_A *)
(** θ_for_A *)
Inductive θ_for_A : A -> A -> Sub -> atoms -> Prop :=
  | A_for_A__nil : forall L,
      θ_for_A [] [] [] L
  | A_for_A__cons : forall α β a b θ L,
      θ_for_A a b θ L
    -> β ∉ (L ∪ varl b)
    -> θ_for_A (α :: a) (β :: b) ((T__Var_f β, α) :: θ) L.
#[export] Hint Constructors θ_for_A : core.

Fact θ_for_A_FrA : forall a b θ L,
    θ_for_A a b θ L
    -> b ### L.
Proof. induction 1. crush. apply FrA_cons. split; crush. Qed.

Fact θ_for_A_FrA_codom_Sub : forall a b θ L,
    θ_for_A a b θ L
  -> skvars_codom_Sub θ ≡ varl b.
Proof. intros. induction H. crush. simpl+. fsetdec. Qed.

Fact close_θ_for_A__σ : forall a a' θ L σ,
    θ_for_A a a' θ L
  -> varl a ⊆ L
  -> fv__α(σ) ⊆ L
  -> close_Sc_wrt_A σ a = close_Sc_wrt_A (⟦θ ▹ σ⟧) a'.
Proof.
  intro a. ind_a a; introv θFA SUB1 SUB2.
  - inverts θFA. crush.
  - inverts θFA. simpl+. fequals.
    erewrite IHa. 2:eassumption. dist.
    rewrite <- subst_skvar_Sc_close_Sc_wrt_A.
    applys_eq close_Sc_wrt_T_subst_skvar_Sc.
    (*side conditions*)
    + rewrite fsk_Sc_close_Sc_wrt_T. rewrite fsk_close_Sc_wrt_A. rewrite Sub_app_Sc_fsk'.
      forwards: θ_for_A_FrA_codom_Sub. eassumption. fsetdec.
    + crush.
    + forwards: θ_for_A_FrA. eassumption. unfolds in H. eapply in_disj2. jauto. fsetdec+.
    + fsetdec+.
    + fsetdec+.
    + fsetdec+.
Qed.

Fact close_θ_for_A__t : forall a b θ L t,
    θ_for_A a b θ L
  -> varl a ⊆ L
  -> fv__α(t) ⊆ L
  -> close_Tm_wrt_A t a = close_Tm_wrt_A (⟦θ ▹ t⟧) b.
Proof.
  intro a. ind_a a; introv θFA SUB1 SUB2; inverts θFA. crush.
  simpl+. fequals. erewrite IHa. 2:eassumption.
  rewrite <- subst_skvar_Tm_close_Tm_wrt_A.
  applys_eq close_Tm_wrt_T_subst_skvar_Tm.
  (*side conditions*)
  + rewrite fsk_Tm_close_Tm_wrt_T. rewrite fsk_close_Tm_wrt_A. rewrite Sub_app_Tm_fsk'.
    forwards: θ_for_A_FrA_codom_Sub. eassumption. fsetdec.
  + crush.
  + forwards: θ_for_A_FrA. eassumption. unfolds in H. eapply in_disj2. jauto. fsetdec+.
  + fsetdec+.
  + fsetdec+.
  + fsetdec+.
Qed.

(** subst_A *)
Lemma Dec_subst_A : forall a1 a2 ψ e τ t L,
    ψ ::a (a2 ++ a1) ⊢d e ▸ τ ⤳ t
  -> (a2 ++ a1) ### E_skvars ψ
  -> exists L' a1' θ,
    θ_for_A a1 a1' θ L'
  /\ ψ ::a (a2 ++ a1') ⊢d e ▸ ⟦θ ▹ τ⟧ ⤳ ⟦θ ▹ t⟧
  /\ L ⊆ L'.
Proof.
  intro a1. ind_a a1; introv DEC FR.
  exists L. do 2 eexists []. simpl+. crush.
  forwards [L' [a1' [θ [θFA [DEC' SUB'']]]]]: IHa1 (a2 ++ [α]) (L ∪ {{α}}). applys_eq DEC. fequals. simpl+. crush. applys_eq FR. crush.
  forwards [L'' DEC'']: Dec_subst. apply DEC'.
  forwards [β NIL__β]: atom_fresh (L' ∪ varl a1' ∪ L'').
  exists L'. do 2 eexists. splits.
  - applys A_for_A__cons β. eassumption. fsetdec.
  - applys_eq DEC''. 2:fsetdec.
    simpl+. fequals.
    + symmetry. apply rename_skvar_E_notin. inverts FR. simpl+ in H0. eapply in_disj1; jauto.
    + unfold_subst_var. if_taut. inverts FR. norm in H. fequals. 2:fequals.
      * symmetry. apply rename_skvar_A_notin. eapply NoDup_app'2. applys_eq H. simpl+. fsetdec.
      * symmetry. eapply rename_skvar_A_notin.
        forwards: θ_for_A_FrA. eassumption. unfolds in H1.
        eapply in_disj2. jauto. fsetdec.
  - fsetdec.
Qed.

Corollary Dec_subst_A' : forall a ψ e τ t L,
    ψ ::a a ⊢d e ▸ τ ⤳ t
  -> a ### E_skvars ψ
  -> exists L' a' θ,
    ψ ::a a' ⊢d e ▸ ⟦θ ▹ τ⟧ ⤳ ⟦θ ▹ t⟧
  /\ θ_for_A a a' θ L'
  /\ L ⊆ L'.
Proof.
  intros. forwards [L' [a' [θ [DEC' [θFA SUB]]]]]: Dec_subst_A a ([]:A). applys_eq H. crush.
  exists L' a' θ. splits; try eassumption.
Qed.


(*** Weakening *)
(** Args *)
Module Type DecWeakeningArgs.
  Parameter R : E -> E -> Prop.
  #[export] Hint Unfold R : core.
  Parameter R_app_proper : Proper (R ==> eq ==> R) E__app.

  Parameter R_vars : forall σ x ψ1 ψ2 ψ3 (τ:T) (t:Tm),
      E_lookup ψ3 x = None
    -> E_lookup ψ1 x = Some σ
    -> SubSumpTm (ψ1 +++ ψ3) (t__Var_f x) σ t τ
    -> R ψ1 ψ2
    -> exists σ',
        E_lookup ψ2 x = Some σ'
      /\ SubSumpTm (ψ2 +++ ψ3) (t__Var_f x) σ' t τ.

  Parameter R_SS : forall ψ1 ψ2 ψ3 x σ t τ,
      SubSumpTm (ψ1 +++ ψ3) (t__Var_f x) σ t τ
    -> R ψ1 ψ2
    -> SubSumpTm (ψ2 +++ ψ3) (t__Var_f x) σ t τ.

  Parameter R_WfT : forall ψ1 ψ2 ψ3 τ,
      WfT (ψ1 +++ ψ3) τ
    -> R ψ1 ψ2
    -> WfT (ψ2 +++ ψ3) τ.
End DecWeakeningArgs.

(** Weakening *)
Module DecWeakening (Import Args : DecWeakeningArgs).
  Lemma Dec_R_app' : forall e,
      lc(e)
    -> forall ψ1 ψ2 ψ3 τ t,
      (ψ1 +++ ψ3) ⊢d e ▸ τ ⤳ t
    -> R ψ1 ψ2
    -> (ψ2 +++ ψ3) ⊢d e ▸ τ ⤳ t.
  Proof.
    introv LC. induction LC; introv DEC REL; inverts DEC.
    - apply E_lookup_distr in IN. destruct IN as [IN|[IN1 IN2]].
      + applys Dec__Var σ. eauto using E_lookup_distr. crush. eauto using R_SS.
      + forwards [σ' [IN' SS']]: R_vars. 1,2,3,4:eassumption.
        econstructor. 2:eassumption. crush.
    - crush.
    - applys Dec__App; eauto.
    - applys Dec__Abs L. eauto using R_WfT.
      intros x NIL__x.
      forwards: H0 x ψ1 ψ2 (ψ3 ::x x :- S__T τ1). apply DEC0. fsetdec. eassumption.
      applys_eq H1.
    - forwards [L' [a' [θ [DEC1' [θFA SUB]]]]]: Dec_subst_A' (E_skvars (ψ2 +++ ψ3) ∪ varl a ∪ fv__α(t1) ∪ fv__α(S__T τ1)). apply DEC1. eassumption.
      (* apply Dec_subst_A' in DEC1. destruct DEC1 as [L' DEC1]. *)
      (* forwards [θ θFA]: create_θ_for_A a (E_A_O_skvars (ψ2 +++ ψ3) ∪ L'). *)
      erewrite close_θ_for_A__t. 2:eassumption. 2,3:fsetdec.
      applys Dec__Let L.
      + forwards IH: IHLC ψ1 ψ2 (ψ3 ::a a'). applys_eq DEC1'. eassumption.
        applys_eq IH.
      + intros x NIL__x. asserts_rewrite (S__T ⟦θ ▹ τ1⟧ = ⟦θ ▹ S__T τ1⟧). crush.
        erewrite <- close_θ_for_A__σ. 2:eassumption. 2,3:fsetdec.
        specializes DEC2 x. specializes DEC2. fsetdec.
        forwards: H0 ψ1 ψ2 (ψ3 ::x x :- close_Sc_wrt_A (S__T τ1) a). apply DEC2. eassumption.
        applys_eq H1.
      + forwards: θ_for_A_FrA. eassumption. FrA_L_sub.
  Qed.

  Theorem Dec_R_app : forall ψ1 ψ2 ψ3 e τ t,
      (ψ1 +++ ψ3) ⊢d e ▸ τ ⤳ t
    -> R ψ1 ψ2
    -> (ψ2 +++ ψ3) ⊢d e ▸ τ ⤳ t.
  Proof. intros. eapply Dec_R_app'. 2,3:eassumption. eauto. Qed.

  Theorem Dec_R : forall ψ1 ψ2 e τ t,
      ψ1 ⊢d e ▸ τ ⤳ t
    -> R ψ1 ψ2
    -> ψ2 ⊢d e ▸ τ ⤳ t.
  Proof. introv Dec REL. forwards: Dec_R_app ψ1 ψ2 E__Nil. apply Dec. crush. crush. Qed.
End DecWeakening.

(** ID *)
Lemma eq_proper : Proper (eq ==> eq ==> eq) E__app. crush. Qed.
Lemma eq_vars : forall σ x ψ1 ψ2 ψ3 (τ:T) (t:Tm),
    E_lookup ψ3 x = None
  -> E_lookup ψ1 x = Some σ
  -> SubSumpTm (ψ1 +++ ψ3) (t__Var_f x) σ t τ
  -> eq ψ1 ψ2
  -> exists σ',
      E_lookup ψ2 x = Some σ'
    /\ SubSumpTm (ψ2 +++ ψ3) (t__Var_f x) σ' t τ.
Proof. intros. exists σ. crush. Qed.
Lemma eq_SS : forall ψ1 ψ2 ψ3 x σ t τ,
    SubSumpTm (ψ1 +++ ψ3) (t__Var_f x) σ t τ
  -> eq ψ1 ψ2
  -> SubSumpTm (ψ2 +++ ψ3) (t__Var_f x) σ t τ.
Proof. crush. Qed.
Lemma eq_WfT : forall ψ1 ψ2 ψ3 τ,
    WfT (ψ1 +++ ψ3) τ
  -> eq ψ1 ψ2
  -> WfT (ψ2 +++ ψ3) τ.
Proof. crush. Qed.

Module DecWeakeningArgs_ID <: DecWeakeningArgs.
  Definition R := eq (A:=E).
  Definition R_app_proper := eq_proper.
  Definition R_vars := eq_vars.
  Definition R_SS := eq_SS.
  Definition R_WfT := eq_WfT.
End DecWeakeningArgs_ID.

Module DecWeakening_ID := DecWeakening DecWeakeningArgs_ID.

(** E_sk_x_sub *)
Module DecWeakeningArgs_E_sk_x_sub <: DecWeakeningArgs.
  Definition R := E_sk_sub_x_list_eq.
  Definition R_app_proper := E_sk_sub_x_eq_app_proper.
  Definition R_vars := E_sk_sub_x_list_eq_vars.
  Definition R_SS := E_sk_sub_x_list_eq_SS.
  Definition R_WfT := E_sk_sub_x_list_eq_WfT.
End DecWeakeningArgs_E_sk_x_sub.

Module DecWeakening_E_sk_x_sub := DecWeakening DecWeakeningArgs_E_sk_x_sub.

Theorem Dec_weaken : forall ψ1 ψ2 e τ t,
      ψ1 ⊢d e ▸ τ ⤳ t
    -> ψ1 ⊆ψα ψ2
    -> ψ1 =ψx ψ2
    -> ψ2 ⊢d e ▸ τ ⤳ t.
Proof. intros. eapply DecWeakening_E_sk_x_sub.Dec_R. eauto. unfold DecWeakeningArgs_E_sk_x_sub.R. crush. Qed.

Theorem Dec_weaken_anil : forall ψ e τ t,
    ψ ::a [] ⊢d e ▸ τ ⤳ t
  -> ψ       ⊢d e ▸ τ ⤳ t.
Proof.
  introv Dec. eapply Dec_weaken. eauto.
  - clfsetdec'+.
  - unfolds. simpl+. crush.
Qed.
