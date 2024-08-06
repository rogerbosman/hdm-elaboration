Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.
Require Import Defs.HdmLems.

Require Import Defs.Dec.Notation.
Require Import Defs.E.
Require Import Defs.ELookup.
Require Import Defs.ERels.
Require Import Defs.Freevars.
Require Import Defs.FrA.
(* Require Import Defs.Lc. *)
Require Import Defs.List.
Require Import Defs.NoDup.
(* Require Import Defs.Freevars. *)
Require Import Defs.OpenClose.
Require Import Defs.Subst.
Require Import Defs.WfE.
Require Import Defs.WfSTt.

Notation  "ψ ⊢t t ▸ σ" := (TmTy ψ t σ) (at level 70, format "ψ  ⊢t  t  ▸  σ" ) : type_scope.

(*** TmTy weaken *)
Definition E_lookup_equiv (ψ1 ψ2:E) : Prop := forall x σ, E_lookup ψ1 x = Some σ -> E_lookup ψ2 x = Some σ.

Theorem TmTy_weaken : forall ψ1 ψ2 t σ,
      ψ1 ⊢t t ▸ σ
    -> ψ1 ⊆ψα ψ2
    -> E_lookup_equiv ψ1 ψ2
    -> ψ2 ⊢t t ▸ σ.
Proof.
  introv TMTY. gen ψ2. induction TMTY; introv SUB LU. 1,2,3,4:crush.
  - econstructor. eauto. intros.
    apply H. eassumption. unfolds. simpl+. assumption.
    unfolds. intros. clear - LU H1. simpl+ in *. if_dec. eassumption. crush.
  - eauto.
  - econstructor. intros.
    eapply H. eassumption. unfolds. simpl+. unfolds in SUB. fsetdec.
    unfolds. introv LU'. clear - LU LU'. simpl+ in *. crush.
  - econstructor. eauto. eauto.
Qed.

(*** TmTy Wft *)
(** LC *)
Lemma TmTy_lc_t : forall ψ t σ,
    ψ ⊢t t ▸ σ
  -> lc(t).
Proof. introv TMTY. induction TMTY; crush. Qed.

Lemma TmTy_skvars_t : forall ψ t σ,
    ψ ⊢t t ▸ σ
  -> fv__α(t) ⊆ E_A_skvars ψ.
Proof.
  introv TMTY (* WF *). induction TMTY. 1,2,3,4:crush. all:simpl+.
  - forwards [x NIL__x]: atom_fresh L.
    specializes H x. specializes H. fsetdec.
    simpl+ in H. apply union_subset_iff. eauto.
    etransitivity. 2:eassumption. crush.
  - fsetdec.
  - forwards [x NIL__x]: atom_fresh (L ∪ fv__α(t0)).
    specializes H x. specializes H. fsetdec.
    rewrite <- fsk_Tm_open_Tm_wrt_T_lower in H. simpl+ in H.
    fsetdec.
  - apply WfT_sk in WFT. fsetdec.
Qed.

Lemma TmTy_tvars_t : forall ψ t σ,
    ψ ⊢t t ▸ σ
  -> fv__x(t) ⊆ E_names ψ.
Proof.
  introv TMTY (* WFE *). induction TMTY. 2,3,4:crush. all:simpl+.
  - apply E_lookup_some1 in IN. fsetdec.
  - forwards [x NIL__x]: atom_fresh (L ∪ fv__x(t0)).
    specializes H x. specializes H. fsetdec.
    applys subset_notin x. 2:fsetdec.
    rewrite <- ftv_Tm_open_Tm_wrt_Tm_lower in H. crush.
  - fsetdec.
  - forwards [x NIL__x]: atom_fresh (L ∪ fv__α(t0)).
    specializes H x. specializes H. fsetdec.
    rewrite <- ftv_Tm_open_Tm_wrt_T_lower in H. simpl+ in H.
    fsetdec.
  - apply WfT_sk in WFT. fsetdec.
Qed.

Lemma TmTy_Wft : forall ψ t σ,
    ψ ⊢t t ▸ σ
  -> ψ ⊢wft t.
Proof.
  intros. splits; eauto using TmTy_lc_t, TmTy_skvars_t, TmTy_tvars_t.
Qed.
#[export] Hint Resolve TmTy_Wft : core.

(*** TmTy WfS *)
(** LC *)
Lemma TmTy_lc_Sc : forall ψ t σ,
    ψ ⊢t t ▸ σ
  -> wf(ψ)
  -> lc(σ).
Proof.
  introv TMTY WFE. induction TMTY.
  - eauto using TmTy_wft_var.
  - crush.
  - crush.
  - crush.
  - forwards [x NIL__x]: atom_fresh (L ∪ E_names ψ). specializes H x. specializes H. fsetdec. eauto.
    inverts H. do 2 econstructor; crush.
  - specializes IHTMTY1. assumption. inverts IHTMTY1. inverts H0. crush.
  - forwards [α NIL__α]: atom_fresh (L ∪ E_skvars ψ).
    eapply lc_S__Forall_exists. applys H α. fsetdec.
    (* eapply WfE__A'. *) econstructor.
    assumption. constructor. eauto. simpl+. fsetdec.
  - assert (lc(S__Forall σ)). eauto. assert (lc(τ)). eauto. crush.
Qed.

Lemma TmTy_skvars_Sc : forall ψ t σ,
    ψ ⊢t t ▸ σ
  -> wf(ψ)
  -> fv__α(σ) ⊆ E_A_skvars ψ.
Proof.
  introv TMTY WFE. induction TMTY.
  - eauto using TmTy_wft_var.
  - crush.
  - crush.
  - crush.
  - forwards [x NIL__x]: atom_fresh (L ∪ E_names ψ). specializes H x. specializes H. fsetdec. eauto.
    simpl+. apply union_subset_iff. eauto.
    simpl+ in H. eassumption.
  - specializes IHTMTY1. assumption. simpl+ in IHTMTY1. fsetdec.
  - forwards [α NIL__α]: atom_fresh (L ∪ E_skvars ψ ∪ fv__α(σ)).
    specializes H α. specializes H. fsetdec.
    (* apply WfE__A'. *) econstructor.
    auto.
    constructor. auto. simpl+. fsetdec.
    simpl+. simpl+ in H.
    rewrite <- fsk_Sc_open_Sc_wrt_T_lower in H. fsetdec.
  - specializes IHTMTY. eassumption.
    etransitivity. apply fsk_Sc_open_Sc_wrt_T_upper.
    apply union_subset_iff. eauto.
    rewrite fsk_S__Forall in IHTMTY. crush.
Qed.

Lemma TmTy_WfS : forall ψ t σ,
    ψ ⊢t t ▸ σ
  -> wf(ψ)
  -> ψ ⊢wfσ σ.
Proof. intros. split; eauto using TmTy_lc_Sc, TmTy_skvars_Sc. Qed.

Lemma TmTy_WfS_closed : forall t σ,
    • ⊢t t ▸ σ
  -> • ⊢wfσ σ.
Proof. intros. eapply TmTy_WfS. eassumption. crush. Qed.
#[export] Hint Resolve TmTy_WfS_closed : core.

(*** subst skvar *)
(** Main lemma *)
Lemma TmTy_subst_skvar_binding_E : forall τ α ψ t σ,
    ψ ⊢t t ▸ σ
  -> remove_sk_E α ψ ⊢wfτ τ
  -> ({τ ⇏ α} ψ) ⊢t {τ ≔ α}t ▸ {τ ≔ α}σ.
Proof.
  introv TMTY WF. induction TMTY.
  - econstructor. simpl+. eauto using E_lookup_subst_skvar_binding_E.
  - crush.
  - crush.
  - crush.
  - simpl+. econstructor. eauto using WfT_subst_skvar_binding_E.
    intros. specializes H. eassumption.
    eapply WfT_E_A_sk_sub. eassumption. unfolds. simpl. fsetdec.
    applys_eq H. rewrite subst_skvar_Tm_open_Tm_wrt_Tm.
    simpl+. reflexivity.
  - simpl+. econstructor; crush.
  - simpl+. applys TmTy__TAbs (L ∪ {{α}}).
    intros.
    assert (α0 <> α). intro. subst. clear - H0. fsetdec.
    specializes H α0. specializes H. fsetdec.
    simpl+. if_taut.
    eapply WfT_E_A_sk_sub. eassumption. unfolds. simpl+. fsetdec.
    applys_eq H. simpl+. if_dec. crush. reflexivity.
    rewrite subst_skvar_Tm_open_Tm_wrt_T. simpl+. if_dec. crush. reflexivity.
    eauto.
    rewrite subst_skvar_Sc_open_Sc_wrt_T. simpl+. if_dec. crush. reflexivity.
    eauto.
  - simpl+. rewrite subst_skvar_Sc_open_Sc_wrt_T. 2:eauto.
    econstructor. eauto using WfT_subst_skvar_binding_E.
    apply IHTMTY. eassumption.
Qed.

Corollary TmTy_subst_skvar_binding_E_head : forall τ α ψ t σ,
    ψ ::a [α] ⊢t t ▸ σ
  -> ψ ⊢wfτ τ
  -> α ∉ E_skvars ψ
  -> ψ ⊢t {τ ≔ α}t ▸ {τ ≔ α}σ.
Proof.
  introv TMTY TMTY__in NIE. forwards TMTY': TmTy_subst_skvar_binding_E τ α t0. eassumption.
  eapply WfT_E_A_sk_sub. eassumption. simpl+. if_taut. unfolds. simpl+. rewrite <- E_A_skvars_E_skvars in NIE. fsetdec.
  eapply TmTy_weaken. applys_eq TMTY'. simpl+. if_taut. rewrite subst_skvar_binding_E_notin. 2:fsetdec.
  unfolds. simpl+. clfsetdec.
  simpl+. if_taut. unfolds. introv IN. simpl in IN. rewrite subst_skvar_binding_E_notin in IN; crush.
Qed.

Corollary TmTy_TLam_subst : forall ψ α t σ τ,
    ψ ⊢t t__TLam (close_Tm_wrt_T α t) ▸ S__Forall (close_Sc_wrt_T α σ)
  -> ψ ⊢wfτ τ
  -> ψ ⊢t {τ ≔ α} t ▸ {τ ≔ α}σ.
Proof.
  introv TMTY WFT. inverts TMTY. rename TMTY0 into TMTY.
  forwards [β NIL__β]: atom_fresh (L ∪ {{α}} ∪ fv__α(t0) ∪ fv__α(σ) ∪ E_skvars ψ).
  specializes TMTY β. specializes TMTY. fsetdec.
  rewrite <- subst_skvar_Tm_spec in TMTY. rewrite <- subst_skvar_Sc_spec in TMTY.
  forwards: TmTy_subst_skvar_binding_E_head TMTY. eassumption. fsetdec. applys_eq H.
  - rewrite subst_skvar_Tm_subst_skvar_Tm_samevar. reflexivity. fsetdec.
  - rewrite subst_skvar_Sc_subst_skvar_Sc_samevar. reflexivity. fsetdec.
Qed.

(* Corollary TmTy_subst_skvar_binding_E' : forall ψ a α t σ τ, *)
(*     ψ ::a (α :: a) ⊢t t ▸ σ *)
(*   -> (ψ ::a      a) ⊢wfτ τ *)
(*   -> α ∉ E_skvars (ψ ::a a) *)
(*   -> ψ ::a      a  ⊢t {τ ≔ α}t ▸ {τ ≔ α}σ. *)
(* Proof. *)
(*   Axiom remove_sk_E_notin_E_skvars: forall (ψ : E) (α : skvar), *)
(*       α ∉ E_skvars ψ *)
(*     -> remove_sk_E α ψ = ψ. *)
(*   Axiom subst_skvar_binding_E_notin_E_skvars: forall (ψ : E) (α : skvar) τ, *)
(*       α ∉ E_skvars ψ *)
(*     -> {τ ≔ α} ψ = ψ. *)
(*   introv TMTY WFT NIE. *)
(*   forwards: TmTy_subst_skvar_binding_E α. eassumption. *)
(*   applys_eq WFT. simpl+. if_taut. *)
(*   forwards: remove_sk_E_notin_E_skvars. eassumption. simpl+ in H. crush. *)
(*   applys_eq H. simpl+. if_taut. *)
(*   forwards: subst_skvar_binding_E_notin_E_skvars. eassumption. simpl+ in H. crush. *)
(* Qed. *)

(*** rename skvar *)
Lemma TmTy_rename_skvar : forall α β ψ t σ,
    ψ ⊢t t ▸ σ
  -> ({β ↤ α}ψ) ⊢t ({T__Var_f β ≔ α}t) ▸ ({T__Var_f β ≔ α}σ).
Proof.
  introv TMTY. induction TMTY. 2,3,4:crush.
  - econstructor. eauto using E_lookup_rename_skvar_E.
  - simpl+. applys TmTy__Abs L. eauto using WfT_rename_skvar_E.
    intros x NIL__x.
    specializes H x. specializes H. fsetdec.
    applys_eq H.
    + rewrite subst_skvar_Tm_open_Tm_wrt_Tm. simpl+. reflexivity.
  - simpl+. econstructor. eassumption. eassumption.
  - simpl+. applys TmTy__TAbs (L ∪ {{α}} ∪ {{β}}). intros α' NIL__α'.
    specializes H α'. specializes H. fsetdec.
    applys_eq H.
    + simpl+. fequals. unfold rename_var. if_dec. fsetdec. crush.
    + rewrite subst_skvar_Tm_open_Tm_wrt_T. 2:crush. simpl+. if_dec. fsetdec. reflexivity.
    + rewrite subst_skvar_Sc_open_Sc_wrt_T. 2:crush. simpl+. if_dec. fsetdec. reflexivity.
  - simpl+. rewrite subst_skvar_Sc_open_Sc_wrt_T. 2:crush.
    econstructor. eauto using WfT_rename_skvar_E. eassumption.
Qed.

(*** subst var *)
Lemma TmTy_subst_name : forall t__in x σ__in ψ t σ,
    ψ ⊢t t ▸ σ
  -> E_lookup ψ x = Some σ__in
  -> remove_var_E x ψ ⊢t t__in ▸ σ__in
  -> remove_var_E x ψ ⊢t {t__in ≔__x x} t ▸ σ.
Proof.
  introv TMTY LU TMTY__in. induction TMTY.
  - simpl+. if_dec. crush. constructor.
    eapply (remove_var_E_E_lookup x) in IN. destruct IN. crush. eassumption.
  - crush.
  - crush.
  - crush.
  - simpl+. applys TmTy__Abs (L ∪ {{x}} ∪ E_names (remove_var_E x ψ)).
    eapply WfT_E_A_sk_sub. eassumption. unfolds. simpl+. reflexivity.
    intros y NIL__y. assert (x <> y). intro. fsetdec.
    specializes H y. specializes H.
    + fsetdec.
    + simpl+. if_taut.
    + simpl+. if_taut. eapply TmTy_weaken.
      * eassumption.
      * unfolds. simpl+. reflexivity.
      * unfolds. intros. simpl+. if_dec.
        forwards: E_lookup_some1. eassumption. fsetdec. eassumption.
    + applys_eq H. simpl+. if_taut.
      rewrite subst_tvar_Tm_open_Tm_wrt_Tm. simpl+. if_taut. eauto.
  - simpl+. eauto.
  - simpl+. econstructor. intros. simpl+.
    specializes H. eassumption. simpl+. crush.
    eapply TmTy_weaken. eassumption. unfolds. simpl+. fsetdec.
    unfolds. intros. simpl+. clear - H. destruct ψ; simpl in *; crush.
    eapply TmTy_weaken. applys_eq H.
    rewrite subst_tvar_Tm_open_Tm_wrt_T. reflexivity. eauto.
    unfolds. simpl+. fsetdec.
    unfolds. introv LU'. clear - LU'. destruct ψ; simpl+ in *; crush.
  - simpl+. econstructor. eapply WfT_E_A_sk_sub. eassumption. unfolds. simpl+. reflexivity.
    eauto.
Qed.

Corollary TmTy_subst_name' : forall ψ x σ__in t t__in σ,
    ψ ::x x :- σ__in ⊢t t ▸ σ
  -> ψ ⊢t t__in ▸ σ__in
  -> x ∉ E_names ψ
  -> ψ ⊢t {t__in ≔__x x} t ▸ σ.
Proof.
  introv DEC DEC__in NIE. forwards: TmTy_subst_name x DEC. simpl+. if_taut. reflexivity.
  simpl+. if_taut. rewrite remove_var_E_notin. 2:assumption. eassumption.
  applys_eq H. simpl+. if_taut. rewrite remove_var_E_notin. 2:assumption. reflexivity.
Qed.

(*** Dec_TmTy *)
Lemma Dec_TmTy__Var : forall t1 t2 ψ σ τ,
    SubSumpTm ψ t1 σ t2 τ
  -> ψ ⊢t t1 ▸ σ
  -> ψ ⊢t t2 ▸ S__T τ.
Proof. introv SS IN. induction SS; eauto. Qed.

Lemma TmTy_close_Tm_wrt_A : forall ψ a t σ,
    ψ ::a a ⊢t t ▸ σ
  -> a ### E_skvars ψ
  -> ψ ⊢t Λ a ⬪ t ▸ (∀ a ⬪ σ).
Proof.
  intros ψ a. gen ψ. ind_a_rev a.
  - introv TMTY _. simpl+.
    eapply TmTy_weaken. eassumption. unfolds. simpl+. fsetdec. unfolds. simpl+. crush.
  - introv TMTY [ND NI]. apply NoDup_snoc in ND. destruct ND as [NI' ND].
    applys_eq IHa. 4:split; [assumption|disj_sub].
    rewrite close_Tm_wrt_A_app. reflexivity.
    rewrite close_Sc_wrt_A_app. reflexivity.
    simpl+. applys TmTy__TAbs empty. intros β NIL__β.
    rewrite <- subst_skvar_Tm_spec.
    rewrite <- subst_skvar_Sc_spec.
    eapply (TmTy_rename_skvar α β) in TMTY. simpl+ in TMTY.
    rewrite rename_skvar_A_notin in TMTY. 2:eauto.
    rewrite rename_skvar_E_notin in TMTY. 2:in_disj.
    eapply TmTy_weaken. eassumption. unfolds. simpl+. fsetdec. unfolds. simpl+. crush.
Qed.

Lemma Dec_TmTy : forall ψ e τ t,
    ψ ⊢d e ▸ τ ⤳ t
  -> ψ ⊢t t ▸ (S__T τ).
Proof.
  introv TMTY. induction TMTY; simpl+.
  - eapply Dec_TmTy__Var.  eassumption. crush.
  - eauto.
  - applys TmTy__Abs L; eauto.
  - eauto.
  - forwards [x NIL__x]: atom_fresh (L ∪ fv__x(t2) ∪ E_names ψ). specializes H x. specializes H. fsetdec.
    assert (TMTY': ψ ⊢t Λ a ⬪ t1 ▸ (∀ a ⬪ S__T τ1)).
      eapply TmTy_close_Tm_wrt_A. eassumption. eassumption.
    forwards: TmTy_subst_name'. eapply H. instantiate (1 := (Λ a ⬪ t1)). assumption. fsetdec.
    applys_eq H1. rewrite subst_tvar_Tm_open_Tm_wrt_Tm. 2:eauto.
    simpl+. if_taut. subst_notin.
Qed.

(*** All the old stuff *)

(* (*** TmTy_WfS *) *)

(* Lemma NoDup_singleton : forall (X:Type) (x:X), *)
(*     NoDup [x]. *)
(* Proof. intros. constructor. crush. constructor. Qed. *)
(* #[export] Hint Resolve NoDup_singleton : core. *)

(* Lemma FrA_singleton : forall α L, *)
(*     α ∉ L *)
(*   -> FrA [α] L. *)
(* Proof. intros. constructor. eauto. simpl+. fsetdec. Qed. *)
(* #[export] Hint Resolve FrA_singleton : core. *)

(* Lemma Subset_remove : forall L1 L2 α, *)
(*     L1 ⊆ L2 *)
(*   -> α ∉ L *)
(*   -> L1 ⊆ AtomSetImpl.remove α L2. *)
(* Proof. intros. fsetdec. Qed. *)

(* Lemma TmTy_WfS : forall ψ t σ, *)
(*     ψ ⊢t t ▸ σ *)
(*   -> wf(ψ) *)
(*   -> ψ ⊢wfσ σ. *)
(* Proof. *)
(*   introv TMTY WFE. induction TMTY. *)
(*   - eauto using TmTy_wft_var. *)
(*   - crush. *)
(*   - crush. *)
(*   - crush. *)
(*   - forwards [x NIL__x]: atom_fresh L. specializes H x. specializes H. fsetdec. eauto. *)
(*     splits. *)
(*     + constructor. constructor. eauto. *)
(*       eauto. *)
(*     + simpl+. apply union_subset_iff. eauto. *)
(*       apply WfS_sk in H. simpl+ in H. eassumption. *)
(*   - specializes IHTMTY1. assumption. destruct IHTMTY1 as [LC FV]. *)
(*     simpl+ in LC. simpl+ in FV. *)
(*     splits. *)
(*     + inverts LC. inverts H0. crush. *)
(*     + fsetdec. *)
(*   - forwards [α NIL__α]: atom_fresh (L ∪ E_skvars ψ ∪ fv__α(σ)). *)
(*     forwards [LC SUB]: H α. fsetdec. constructor. assumption. eauto. apply FrA_singleton. fsetdec. *)
(*     split. eapply lc_S__Forall_exists. apply LC. simpl+. simpl+ in SUB. *)
(*     rewrite <- fsk_Sc_open_Sc_wrt_T_lower in SUB. fsetdec. *)
(*   - splits. *)
(*     + eauto. assert (lc(S__Forall σ)). eauto. *)
(*       assert (lc(τ)). eauto. *)
(*       crush. *)
(*     + specializes IHTMTY. eassumption. *)
(*       etransitivity. apply fsk_Sc_open_Sc_wrt_T_upper. *)
(*       apply union_subset_iff. eauto. *)
(*       unfolds in IHTMTY. rewrite fsk_S__Forall in IHTMTY. crush. *)
(*   (* - forwards [x NIL__X]: atom_fresh L. *) *)
(*   (*   specializes H0 x. specializes H0. fsetdec. *) *)
(*   (*   specializes H1 x. forwards [LC FV]: H1. fsetdec. constructor. assumption. *) *)
(*   (*   apply close_Sc_wrt_A_WfTy. eauto. *) *)
(*   (*   split. eauto. simpl+ in FV. eassumption. *) *)
(* Qed. *)
(* #[local] Hint Resolve TmTy_WfS : core. *)

(* Lemma TmTy_wft : forall ψ t σ, *)
(*     ψ ⊢t t ▸ σ *)
(*   -> wf(ψ) *)
(*   -> ψ ⊢wft t. *)
(* Proof. *)
(*   introv TMTY WF. induction TMTY. *)
(*   - splits. crush. auto. simpl+. apply E_lookup_some in IN. fsetdec. *)
(*   - splits; crush. *)
(*   - splits; crush. *)
(*   - splits; crush. *)
(*   - forwards [x NIL__x]: atom_fresh (L ∪ (fv__x(t0)) ∪ (E_names ψ)). *)
(*     specializes H x. specializes H. fsetdec. crush. *)
(*     unfolds. simpl+. splits. *)
(*     + eauto using lc_t__Lam_exists. *)
(*     + apply union_subset_iff. eauto. *)
(*       apply Wft_sk in H. simpl+ in H. etransitivity. 2:eassumption. crush. *)
(*     + apply Wft_names in H. simpl+ in H. *)
(*       applys subset_notin x. 2:fsetdec. *)
(*       rewrite <- ftv_Tm_open_Tm_wrt_Tm_lower in H. crush. *)
(*   - splits. *)
(*     + econstructor; eauto. *)
(*     + apply union_subset_iff; eauto. *)
(*     + simpl+. *)
(*       forwards: Wft_names t1. eauto. *)
(*       forwards: Wft_names t2. eauto. *)
(*       fsetdec. *)
(*   - forwards [α NIL__α]: atom_fresh (L ∪ E_skvars ψ ∪ fv__α(t0)). *)
(*     forwards [LC [SUB SUB__x]]: H α. fsetdec. constructor. assumption. eauto. apply FrA_singleton. fsetdec. *)
(*     splits. eapply lc_t__TLam_exists. apply LC. *)
(*     simpl+. simpl+ in SUB. rewrite <- fsk_Tm_open_Tm_wrt_T_lower in SUB. fsetdec. *)
(*     simpl+. simpl+ in SUB__x. rewrite <- ftv_Tm_open_Tm_wrt_T_lower in SUB__x. eassumption. *)
(*   - splits; simpl+; crush. *)
(* Qed. *)
(* #[export] Hint Resolve TmTy_wft : slow. *)

(* Lemma TmTy_closed : forall t σ, *)
(*     • ⊢t t ▸ σ *)
(*   -> fv__α(t) ≡ ∅. *)
(* Proof. introv TMTY. forwards: Wft_sk t0. eauto with slow. fsetdec. Qed. *)
(* #[export] Hint Resolve TmTy_closed : core. *)

(* (*** Dec_TmTy *) *)
(* Lemma TmTy_subst_var : forall t__x x ψ t σ σ__x, *)
(*     ψ ::x x :- σ__x ⊢t t ▸ σ *)
(*   -> ψ ⊢t t__x ▸ σ__x *)
(*   -> ψ ⊢t {t__x ≔__x x} t ▸ σ. *)
(* Admitted. *)

(* Lemma TmTy_E_sk_sub_x_list_eq : forall ψ1 ψ2 t σ, *)
(*     ψ1 ⊢t t ▸ σ *)
(*   -> E_sk_sub_x_list_eq ψ1 ψ2 *)
(*   -> ψ2 ⊢t t ▸ σ. *)
(* Proof. *)
(*   introv TMTY [SUB EQ]. gen ψ2. induction TMTY; intros. *)
(*   - econstructor. erewrite E_lookup_E_x_list_eq. eassumption. crush. *)
(*   - crush. *)
(*   - crush. *)
(*   - crush. *)
(*   - econstructor. eauto. *)
(*     intros. eapply H. eassumption. *)
(*     unfolds. simpl+. crush. *)
(*     unfolds. simpl+. fequals. *)
(*   - eauto. *)
(*   - econstructor. intros. apply H. eassumption. *)
(*     unfolds. simpl+. unfolds in SUB. rewrite SUB. clfsetdec. *)
(*     unfolds. simpl+. crush. *)
(*   - eauto. *)
(* Qed. *)

(* Lemma TmTy_subst : forall α ψ t σ, *)
(*     ψ ⊢t t ▸ σ *)
(*   -> exists L, forall β, β ∉ L *)
(*   -> {β ≔__α α} ψ ⊢t {T__Var_f β ≔ α}t ▸ {T__Var_f β ≔ α} σ. *)
(* Admitted. *)

(* Lemma TmTy_close_tm_wrt_A : forall a ψ t σ, *)
(*     ψ ::a a ⊢t t ▸ σ *)
(*   -> FrA a (E_skvars ψ) *)
(*   -> ψ ⊢t close_Tm_wrt_A t a ▸ close_Sc_wrt_A σ a. *)
(* Proof. *)
(*   intro a. ind_a a; introv TMTY FR; simpl+. *)
(*   - eapply TmTy_E_sk_sub_x_list_eq. eassumption. split. *)
(*     unfolds. simpl+. crush. unfolds. simpl+. crush. *)
(*   - forwards [L TMTY']: TmTy_subst α. eassumption. *)
(*     simpl+. applys TmTy__TAbs (L ∪ varl a ∪ E_skvars ψ). intros. *)
(*     specializes TMTY' α0. specializes TMTY'. fsetdec. *)
(*     asserts_rewrite ({α0 ≔__α α}(ψ ::a α :: a) = ψ ::a α0 :: a) in TMTY'. *)
(*     simpl+. fequals. apply subst_skvar_binding_E_notin. inverts FR. in_disj. *)
(*     fequals. apply subst_skvar_A_notin. inverts FR. inverts H0. eauto. *)
(*     forwards: IHa (ψ ::a [α0]). *)
(*     eapply TmTy_E_sk_sub_x_list_eq. apply TMTY'. split; unfolds; simpl+; fsetdec. *)
(*     simpl+. apply FrA_extend_L. eauto. fsetdec. *)
(*     rewrite <- subst_skvar_Tm_spec. rewrite <- subst_skvar_Sc_spec. *)
(*     applys_eq H0. *)
(*     + rewrite subst_skvar_Tm_close_Tm_wrt_A. reflexivity. *)
(*       crush. inverts FR. inverts H1. eauto. simpl+. fsetdec. *)
(*     + rewrite subst_skvar_Sc_close_Sc_wrt_A. reflexivity. *)
(*       crush. inverts FR. inverts H1. eauto. simpl+. fsetdec. *)
(* Qed. *)


(* Ltac try_sub_notin := *)
(*   match goal with *)
(*     | [ |- context[subst ?t ?α ?x] ]  => *)
(*         match type of x with *)
(*         | Sc => rewrite subst_skvar_Sc_notin *)
(*         | T  => rewrite subst_skvar_T_notin *)
(*         | Tm => rewrite subst_skvar_Tm_notin *)
(*         end *)
(*     | [ |- context[subst__x ?t ?α ?x] ] => *)
(*         match type of x with *)
(*         | Tm => rewrite subst_tvar_Tm_notin *)
(*         end *)
(*   end; try reflexivity. *)
(* Ltac sub_notin := try_sub_notin; solve [fsetdec+|crush]. *)

(* Lemma subst_tvar_Tm_open_Tm_wrt_Tm' : forall x t t__in, *)
(*     x ∉ fv__x(t) *)
(*   -> lc t__in *)
(*   -> open_Tm_wrt_Tm t t__in = {t__in ≔__x x}open_Tm_wrt_Tm t (t__Var_f x). *)
(* Proof. intros. rewrite subst_tvar_Tm_open_Tm_wrt_Tm. 2:assumption. simpl+. if_taut. sub_notin. Qed. *)

(* Require Import Defs.Dec. *)


(* Lemma Dec_WfT : forall ψ e τ t, *)
(*     ψ ⊢d e ▸ τ ⤳ t *)
(*   -> wf(ψ) *)
(*   -> ψ ⊢wfτ τ. *)
(* Abort. *)
(* (* Proof. introv TMTY WF. apply Dec_TmTy in TMTY. apply TmTy_wfσ in TMTY. crush. assumption. Qed. *) *)

(* Lemma Dec_Wft : forall ψ e τ t, *)
(*     ψ ⊢d e ▸ τ ⤳ t *)
(*   -> wf(ψ) *)
(*   -> ψ ⊢wft t. *)
(* Abort. *)
(* (* Proof. introv TMTY WF. apply Dec_TmTy in TMTY. eauto. Qed. *) *)
