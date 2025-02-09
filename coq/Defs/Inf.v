Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.
Require Import Preamble.Tag.
Require Import Defs.HdmLems.

Require Import Defs.E.
Require Import Defs.ERels.
Require Import Defs.ELookup.
Require Import Defs.FrA.
Require Import Defs.Freevars.
Require Import Defs.Inst.
Require Import Defs.List.
Require Import Defs.OpenClose.
Require Import Defs.Shape.
Require Import Defs.Subst.
Require Import Defs.Unification.
Require Import Defs.WfE.
Require Import Defs.WfSTt.

(* Require Import Semantics.EquivRel. *)


Notation  "ψ1 ⊢ e ▸ ⟨ a ⟩ τ ⤳ t ⊣ ψ2" := (Inf ψ1 e a τ t ψ2) (at level 70, format "ψ1  ⊢  e  ▸  ⟨ a ⟩  τ  ⤳  t  ⊣  ψ2" ) : type_scope.

(*** Open/close *)
Lemma close_Sc_wrt_A_disj : forall σ a,
  varl a ∐ fv__α(close_Sc_wrt_A σ a).
Admitted.
Lemma close_Tm_wrt_A_disj : forall t a,
  varl a ∐ fv__α(close_Tm_wrt_A t a).
Admitted.

(*** WfSTt *)
(** WfT construct *)
Lemma WFT_close_Sc_wrt_A : forall ψ a σ,
    (ψ ::a a) ⊢wfσ σ
  -> ψ ⊢wfσ close_Sc_wrt_A σ a.
Admitted.

(** WfS construct *)

(** Wft construct *)
Lemma WFt_close_Sc_wrt_A : forall ψ a t,
    (ψ ::a a) ⊢wft t
  -> ψ ⊢wft close_Tm_wrt_A t a.
Admitted.


(*** Alg *)
Lemma Inf_alg : forall ψ1 e a τ t ψ2,
    ψ1 ⊢ e ▸ ⟨a⟩ τ ⤳ t ⊣ ψ2
  -> alg_E ψ1
  -> alg_E (ψ2 ::o ⦇t ▸ ⟨a⟩ S__T τ⦈).
Proof.
  introv EINST ALG. induction EINST.
  - norm. eapply alg_E_app. crush. unfolds. simpl+.
    forwards: Inst_alg_A. eassumption.
    forwards: Inst_alg_T. eassumption. eauto using E_lookup_alg_E.
    forwards: Inst_alg_Tm. eassumption. simpl+. crush.
    eapply alg_L_union. eapply alg_L_union.  eassumption. eassumption. eassumption.
  - norm. eapply alg_E_app. crush. unfolds. simpl+. crush.
  - freshx L. specializes H. eassumption.
    unfolds. simpl+. eapply alg_L_union. eapply alg_L_union.
    simpl+. assumption.
    simpl+. assumption.
    simpl+. assumption.
    eapply alg_E_subset. eassumption.
    simpl+. rewrite (fsk_Tm_open_Tm_wrt_Tm_lower t0 (t__Var_f x)). reldec.
  - specializes IHEINST1. eassumption.
    specializes IHEINST2. eapply alg_E_subset. eassumption. reldec.
    forwards: U_alg_E. eassumption. simpl+.
    applys alg_E_subset (ψ2 ::a a2 ++ a1' ::o ⦇t__App t1' t2 ▸ ⟨[]⟩ S__T T__Unit⦈ ::a [α]).
    unfolds. simpl+. eapply alg_L_union. eauto.
    unfolds in IHEINST2. applys alg_L_subset IHEINST2. reldec.
    reldec. applys alg_E_subset. eassumption. reldec.
  - specializes IHEINST. eassumption.
    freshx L. specializes H x. specializes H. fsetdec.
    applys alg_E_subset IHEINST. simpl+.
    rewrite fsk_Sc_close_Sc_wrt_A. rewrite fsk_Tm_close_Tm_wrt_A. reldec.
    unfolds. simpl+. rewrite fsk_Tm_open_Tm_wrt_Tm_upper.
    applys alg_L_subset. eapply H.
    simpl+.
    rewrite (fsk_Tm_open_Tm_wrt_Tm_lower t2 (t__Var_f x)). reldec.
Qed.


(*** Inf/Shape *)
Lemma Inf_SameShape : forall ψ__in ψ__out e τ a t,
      ψ__in ⊢ e ▸ ⟨a⟩ τ ⤳ t ⊣ ψ__out
    -> SameShape__E ψ__in ψ__out.
Proof.
  introv INST. induction INST.
  - crush.
  - crush.
  - freshx L. specializes H NIL__x. eauto.
    inv_SSE. crush.
  - etransitivity. eassumption.
    inv_SSE. etransitivity. eassumption.
    forwards: U_SameShape UNI. inv_SSE. assumption.
  - etransitivity. eassumption.
    freshx L. specializes H NIL__x.
    inv_SSE. eassumption.
Qed.

Corollary Inf_SameLength : forall ψ1 e a τ t ψ2,
    ψ1 ⊢ e ▸ ⟨a⟩ τ ⤳ t ⊣ ψ2
  -> SameLength__E ψ1 ψ2.
Proof. eauto using SSE_length, Inf_SameShape. Qed.

Corollary E_O_names_Inf : forall ψ1 ψ2 e a τ t,
    ψ1 ⊢ e ▸ ⟨a⟩ τ ⤳ t ⊣ ψ2
  -> E_O_names ψ1 = E_O_names ψ2.
Proof. eauto using Inf_SameShape, E_O_names_SameShape__E. Qed.

(*** Inf/lc *)
Lemma Inf_lc : forall e ψ__in a τ t ψ__out,
    ψ__in ⊢ e ▸ ⟨a⟩ τ ⤳ t ⊣ ψ__out
  -> lc(e).
Proof.
  introv INF. induction INF. econstructor. econstructor.
  - freshx L. eapply lc_e__Lam_exists. eauto.
  - constructor; eauto.
  - freshx L. eapply lc_e__Let_exists; eauto.
Qed.

(*** Inf Wf-ish *)
(** Well-formedness properties about output of Inf judgements without WfE
requirement *)
Lemma Inf_names_Tm : forall ψ__in e a τ t ψ__out,
    ψ__in ⊢ e ▸ ⟨a⟩ τ ⤳ t ⊣ ψ__out
  -> fv__x(t) ⊆ E_names ψ__out.
Proof.
  introv INF. induction INF.
  - erewrite <- Inst_names. 2:eassumption. eapply E_lookup_some1 in IN. simpl+. fsetdec.
  - simpl+. fsetdec.
  - simpl+.
    freshx (L ∪ fv__x(t0)). specializes H x. specializes H. fsetdec. simpl+ in H.
    eapply weird_open_sets_thing. apply ftv_Tm_open_Tm_wrt_Tm_lower. eassumption. fsetdec.
  - simpl+ in IHINF2.
    eapply U_SameShape in UNI. inv_SSE.
    erewrite <- ftv_SameShape__t. 2:eassumption. simpl+.
    erewrite <- E_names_SameShape__E. 2:eassumption.
    forwards: Inf_SameShape INF2. inv_SSE.
    erewrite <- ftv_SameShape__t. 2:eassumption.
    erewrite E_names_SameShape__E in IHINF1. 2:eassumption. fsetdec.
  - rewrite ftv_Tm_open_Tm_wrt_Tm_upper.
    freshx (L ∪ fv__x(t2)).
    specializes INF2 x. specializes INF2. fsetdec.
    specializes H x. specializes H. fsetdec. simpl+ in H.
    forwards: Inf_SameShape INF2. inv_SSE.
    eapply union_subset_iff.
    + erewrite <- ftv_SameShape__t. 2:eassumption.
      simpl+.
      erewrite <- E_names_SameShape__E. 2:eassumption. eassumption.
    + eapply weird_open_sets_thing. apply ftv_Tm_open_Tm_wrt_Tm_lower. eassumption. fsetdec.
Qed.

(*** Inf Wf *)
(** helper lemmas *)
Lemma Inf_Wf_var : forall t1 σ t2 a τ ψ x,
    E_lookup ψ x = Some σ
  -> Inst t1 σ t2 a τ (E_skvars ψ)
  -> ψ ⊢wft t1
  -> wf(ψ)
  -> wf(ψ ::o ⦇t2 ▸ ⟨a⟩ S__T τ⦈).
Proof.
  intros.
  forwards: E_lookup_wf; try eassumption.
  forwards: Inst_WfT. eassumption. eassumption. eassumption. destr.
  econstructor. eassumption. eauto using Inst_FrA. eauto. eauto.
Qed.

Lemma Inf_Wf_var' : forall t σ a τ ψ x,
    E_lookup ψ x = Some σ
  -> Inst (t__Var_f x) σ t a τ (E_skvars ψ)
  -> wf(ψ)
  -> wf(ψ ::o ⦇t ▸ ⟨a⟩ S__T τ⦈).
Proof. intros. eapply Inf_Wf_var; try eassumption. apply Wft_var. eauto using E_lookup_some1. Qed.

Lemma Inf_Wf_abs1 : forall ψ α x,
    wf(ψ)
  -> α ∉ (E_skvars ψ)
  -> x ∉ E_names ψ
  -> wf(ψ ::a α :: [] ::x x :- S__T (T__Var_f α)).
Proof.
  intros.
  econstructor. econstructor. eassumption. simpl+. eapply FrA_singleton. fsetdec.
  eapply WfS_var. simpl+. fsetdec. simpl+. fsetdec.
Qed.

Lemma Inf_Wf_abs2 : forall ψ a1 a2 x τ1 τ2 t,
    wf(ψ ::a a1 ::x x :- S__T τ1 ::o ⦇open_Tm_wrt_Tm t (t__Var_f x) ▸ ⟨a2⟩ S__T τ2⦈)
  -> x ∉ fv__x(t)
  -> wf(ψ ::o ⦇t__Lam τ1 t ▸ ⟨a2 ++ a1⟩ S__T (T__Fun τ1 τ2)⦈).
Proof.
  intros.
  inv_WfE. econstructor. eauto. eapply FrA_app. eassumption. eassumption. reldec.
  simpl+. apply WfST. eapply WfT_Fun. split; wfdec'.
  applys Wft_lam (S__T τ1). wfdec'. fsetdec. wfdec'.
Qed.

Lemma Inf_Wf_app : forall ψ t1 t2 a1 a2 τ τ1 α,
    wf(ψ ::o ⦇t1 ▸ ⟨a1⟩ S__T τ⦈ ::o ⦇t2 ▸ ⟨a2⟩ S__T τ1⦈)
  -> α ∉ (varl a2 ∪ varl a1) ∪ E_skvars ψ
  -> wf(ψ ::a (α :: a2) ++ a1 ::o ⦇t__App t1 t2 ▸ ⟨[]⟩ S__T (T__Var_f α)⦈).
Proof.
  intros. inv_WfE.
  econstructor. econstructor. eassumption.
  eapply FrA_app. eassumption. eapply FrA_cons. split. eassumption.
  simpl+. simpl+ in FR.
  eapply Wft_sk in WFt0. simpl+ in WFt0.
  eapply WfS_sk in WFS0. simpl+ in WFS0.
  rewrite E_A_skvars_E_skvars in *. fsetdec.
  reldec. auto. apply WfS_var. reldec.
  eapply Wft_app. split; wfdec.
Qed.

Lemma Inf_Wf_let1 : forall ψ t a σ x,
    wf(ψ ::o ⦇t ▸ ⟨a⟩ σ⦈)
  -> x ∉ E_names ψ
  -> wf(((ψ ::x x :- close_Sc_wrt_A σ a) ::o ⦇close_Tm_wrt_A t a ▸ ⟨[]⟩ S__T T__Unit⦈) ::o ⦇t__Unit ▸ ⟨a⟩ S__T T__Unit⦈).
Proof.
  intros. inv_WfE.
  econstructor. econstructor. econstructor. eauto.
  eapply WFT_close_Sc_wrt_A. eauto. fsetdec. auto. crush.
  eapply WFt_close_Sc_wrt_A. wfdec. simpl+. split. eauto.
  disj_union'. disj_union'. eauto.
  apply close_Sc_wrt_A_disj. apply close_Tm_wrt_A_disj. crush. crush.
Qed.

Lemma Inf_Wf_let2 : forall ψ σ t1 a1 t2 x a2 τ2,
    wf(ψ ::x x :- σ ::o ⦇t1 ▸ ⟨[]⟩ S__T T__Unit⦈ ::o ⦇t__Unit ▸ ⟨a1⟩ S__T T__Unit⦈ ::o ⦇open_Tm_wrt_Tm t2 (t__Var_f x) ▸ ⟨a2⟩ S__T τ2⦈)
  -> x ∉ fv__x(t1) ∪ fv__x(t2)
  -> wf(ψ ::o ⦇open_Tm_wrt_Tm t2 t1 ▸ ⟨a2⟩ S__T τ2⦈).
Proof.
  intros.
  inv_WfE. econstructor. eauto. FrA_L_sub. wfdec.
  forwards: Wft_strengthen ψ x σ t1. wfdec. fsetdec.
  applys Wft_open_Tm_wrt_Tm σ. wfdec. wfdec. fsetdec.
Qed.

(** Wf theorem *)
Theorem Inf_Wf : forall ψ__in e a τ t ψ__out,
    ψ__in ⊢ e ▸ ⟨a⟩ τ ⤳ t ⊣ ψ__out
  -> wf(ψ__in)
  -> wf(ψ__out ::o ⦇t ▸ ⟨a⟩ S__T τ⦈).
Proof.
  introv INF WF. induction INF.
  - eauto using Inf_Wf_var'.
  - eauto.
  - freshx (L ∪ E_names ψ__in ∪ fv__x(t0)).
    specializes H x. specializes H. fsetdec.
    apply Inf_Wf_abs1; try eassumption; fsetdec.
    eapply Inf_Wf_abs2; try eassumption; fsetdec.

  - specializes IHINF1. eassumption.
    specializes IHINF2. eassumption. simpl+ in FR.
    forwards: U_Wf UNI. eapply Inf_Wf_app; try eassumption.
    eapply WfE_cons_obj_shift. assumption.

  - freshx (L ∪ E_names ψ1 ∪ fv__x(t1') ∪ fv__x(t2)). specializes IHINF. eassumption.
    specializes H x. specializes H. fsetdec. eapply Inf_Wf_let1; try eassumption; fsetdec.
    eapply Inf_Wf_let2; try eassumption; fsetdec.
Qed.

(*** Subst name *)
Lemma Inf_subst_name : forall ψ__in e a τ t ψ__out,
    ψ__in ⊢ e ▸ ⟨a⟩ τ ⤳ t ⊣ ψ__out
  -> forall x__in x__out,
      x__in ∉ fv__x(e) ∪ E_O_names ψ__in
    -> ({ x__in ↤__x x__out } ψ__in) ⊢ { e__Var_f x__in ≔__x x__out } e ▸ ⟨a⟩ τ ⤳ { t__Var_f x__in ≔__x x__out } t ⊣ ({ x__in ↤__x x__out } ψ__out).
Proof.
  introv INF. induction INF; intros x__in x__out NIN.

  (*Var*)
  - simpl+. if_dec.
    + econstructor. eauto using subst_name_E_in__eq. simpl+.
      forwards INST': Inst_subst_name x__in x__out. eassumption.
      applys_eq INST'. simpl+. if_taut.
    + econstructor. eapply subst_name_E_in__neq. eassumption. eassumption. simpl+ in NIN. fsetdec.
      eapply Inst_ftv_sub__neq. eapply Inst_subset. eassumption. simpl+. fsetdec. eassumption.

  (*Unit*)
  - crush.

  (*Abs*)
  - simpl+. applys Inf__Abs (L ∪ {{x__out}} ∪ {{x__in}}).
    simpl+. eassumption. assumption.
    introx. specializes H x x__in x__out.
    destruct (x == x__out) as [?|NEQ1]. fsetdec.
    applys_eq H. 1,2,3,4:clear NIN.
    + simpl+. fequals. unfold_subst_var. if_taut.
    + rewrite subst_var_Ex_open_Ex_wrt_Ex. simpl+. if_taut. crush.
    + rewrite subst_tvar_Tm_open_Tm_wrt_Tm. simpl+. if_taut. crush.
    + simpl+. fequals. unfold_subst_var. if_taut.
    + simpl+. simpl+ in NIN. rewrite fv_Ex_open_Ex_wrt_Ex_upper. simpl+. fsetdec.

  (*App*)
  - simpl+. simpl+ in NIN. applys Inf__App ({x__in ↤__x x__out}ψ__in) ({x__in ↤__x x__out}ψ__out) ({x__in ↤__x x__out}ψ1) ({x__in ↤__x x__out}ψ2) α.
    eapply IHINF1. fsetdec.
    applys_eq IHINF2.
    + forwards: E_O_names_SameShape__E. applys Inf_SameShape INF1.
      simpl+. erewrite Inf_names_Tm. 2:apply INF1. simpl+. rewrite H in NIN.
      clear - NIN. rewrite E_names_E_O_names. fsetdec.
    + clear - FR. simpl+ in *. eassumption.
    + assumption.
    + forwards UNI': U_subst_name x__in x__out. eassumption. simpl+ in UNI'.
      applys_eq UNI'.

  (*Let*)
  - simpl+. simpl+ in NIN.
    rewrite subst_tvar_Tm_open_Tm_wrt_Tm. applys Inf__Let (L ∪ {{x__out}} ∪ {{x__in}}) σ__out a1'.
    eapply IHINF. fsetdec. 2:crush.
    introx. specializes H x x__in x__out.
    destruct (x == x__out) as [?|NEQ1]. fsetdec.
    applys_eq H. 1,2,3,4:clear NIN.
    + simpl+. fequals. fequals. unfold_subst_var. if_taut.
      rewrite subst_tvar_Tm_close_Tm_wrt_A. reflexivity. constructor. simpl+. crush.
    + rewrite subst_var_Ex_open_Ex_wrt_Ex. simpl+. if_taut. crush.
    + rewrite subst_tvar_Tm_open_Tm_wrt_Tm. simpl+. if_taut. crush.
    + simpl+. fequals. unfold_subst_var. if_taut.
    + simpl+. simpl+ in NIN. rewrite fv_Ex_open_Ex_wrt_Ex_upper. simpl+.
      erewrite Inf_names_Tm. 2:apply INF. simpl+.
      rewrite E_names_E_O_names. erewrite <- E_O_names_SameShape__E. 2:applys Inf_SameShape INF.
      clear - NIN NIL__x. fsetdec.
Qed.

Corollary Inf_subst_name_head : forall x__out ψ__in σ e a τ t ψ__out σ',
   ψ__in ::x x__out :- σ ⊢ open_Ex_wrt_Ex e (e__Var_f x__out) ▸ ⟨a⟩ τ ⤳ open_Tm_wrt_Tm t (t__Var_f x__out) ⊣ ψ__out ::x x__out :- σ'
 -> x__out ∉ (E_O_names ψ__in ∪ fv(e) ∪ fv__x(t))
 -> exists L, forall x__in, x__in ∉ L
 -> ψ__in ::x x__in  :- σ ⊢ open_Ex_wrt_Ex e (e__Var_f x__in ) ▸ ⟨a⟩ τ ⤳ open_Tm_wrt_Tm t (t__Var_f x__in ) ⊣ ψ__out ::x x__in  :- σ'.
Proof.
  introv INF NIE__xout. exists (fv_Ex (e__Var_f x__out) ∪ fv_Ex e ∪ E_O_names ψ__in ∪ Metatheory.singleton x__out). intros x__in NIL__x.
  forwards INF': Inf_subst_name x__in x__out. eassumption. simpl+.
    rewrite fv_Ex_open_Ex_wrt_Ex_upper. fsetdec.
  applys_eq INF'.
  - simpl+. fequals. symmetry. apply rename_name_E_fresh_eq. fsetdec.
  - rewrite subst_var_Ex_open_Ex_wrt_Ex. 2:crush. simpl+. if_taut.
    rewrite subst_var_Ex_fresh_eq. crush. fsetdec.
  - rewrite subst_tvar_Tm_open_Tm_wrt_Tm. 2:crush. simpl+. if_taut.
    rewrite subst_tvar_Tm_fresh_eq. crush. fsetdec.
  - simpl+. fequals. symmetry. apply rename_name_E_fresh_eq.
    forwards: Inf_SameShape. apply INF. inv_SSE.
    erewrite <- E_O_names_SameShape__E. 2:eassumption. fsetdec.
Qed.

Corollary Inf_subst_name_head' : forall x__out ψ__in e a τ t σ t__obj1 a__obj1 σ__obj1 t__obj2 a__obj2 σ__obj2 ψ__out σ' t__obj1' a__obj1' σ__obj1' t__obj2' a__obj2' σ__obj2',
    ψ__in ::x x__out :- σ ::o ⦇t__obj1 ▸ ⟨a__obj1⟩ σ__obj1⦈ ::o ⦇t__obj2 ▸ ⟨a__obj2⟩ σ__obj2⦈ ⊢ open_Ex_wrt_Ex e (e__Var_f x__out) ▸ ⟨a⟩ τ ⤳ open_Tm_wrt_Tm t (t__Var_f x__out) ⊣ ψ__out ::x x__out :- σ'::o ⦇t__obj1' ▸ ⟨a__obj1'⟩ σ__obj1'⦈ ::o ⦇t__obj2' ▸ ⟨a__obj2'⟩ σ__obj2'⦈
 -> x__out ∉ (E_O_names ψ__in ∪ fv(e) ∪ fv__x(t) ∪ fv__x(t__obj1) ∪ fv__x(t__obj2))
 -> exists L, forall x__in, x__in ∉ L
  -> ψ__in ::x x__in  :- σ ::o ⦇t__obj1 ▸ ⟨a__obj1⟩ σ__obj1⦈ ::o ⦇t__obj2 ▸ ⟨a__obj2⟩ σ__obj2⦈ ⊢ open_Ex_wrt_Ex e (e__Var_f x__in ) ▸ ⟨a⟩ τ ⤳ open_Tm_wrt_Tm t (t__Var_f x__in ) ⊣ ψ__out ::x x__in  :- σ'::o ⦇t__obj1' ▸ ⟨a__obj1'⟩ σ__obj1'⦈ ::o ⦇t__obj2' ▸ ⟨a__obj2'⟩ σ__obj2'⦈.
Proof.
  introv INF NIE__xout. exists ({{x__out}} ∪ fv(e) ∪ E_O_names ψ__in ∪ {{x__out}} ∪ fv__x(t__obj1) ∪ fv__x(t__obj2)). intros x__in NIL__x.
  forwards INF': Inf_subst_name x__in x__out. eassumption.
    rewrite fv_Ex_open_Ex_wrt_Ex_upper. simpl+. fsetdec.
  applys_eq INF'.
  - simpl+. subst_notin'. 2:fsetdec. subst_notin'. 2:fsetdec. do 3 fequals.
    symmetry. apply rename_name_E_fresh_eq. fsetdec.
  - rewrite subst_var_Ex_open_Ex_wrt_Ex. 2:crush. simpl+. if_taut.
    rewrite subst_var_Ex_fresh_eq. crush. fsetdec.
  - rewrite subst_tvar_Tm_open_Tm_wrt_Tm. 2:crush. simpl+. if_taut.
    rewrite subst_tvar_Tm_fresh_eq. crush. fsetdec.
  - forwards: Inf_SameShape. apply INF. inv_SSE.
    forwards EQ__xout: E_O_names_SameShape__E.
    applys SSE__O t__obj2 t__obj2' a__obj2 a__obj2'.
    applys SSE__O t__obj1 t__obj1' a__obj2 a__obj2'.
    all:try eassumption. simpl+ in EQ__xout.
    assert (NIE__xout' : x__out ∉ (E_O_names ψ__out ∪ fv__x(t__obj1') ∪ fv__x(t__obj2'))). rewrite <- EQ__xout. fsetdec.
    simpl+. subst_notin'. 2:fsetdec. subst_notin'. 2:fsetdec. do 3 fequals.
    symmetry. apply rename_name_E_fresh_eq.
    forwards: Inf_SameShape. apply INF. inv_SSE.
    erewrite <- E_O_names_SameShape__E. 2:eassumption. clear - NIE__xout. fsetdec.
Qed.

(*** Weakening *)
Section InfWeakening.
  Variable R : E -> E -> Prop.

  Notation "ψ1 ∼ ψ2" := (R ψ1 ψ2) (at level 70).

  Variable R_app_proper : Proper (R ==> eq ==> R) E__app.

  Variable R__var : forall ψ ψ'
                      σ x t a τ,
      ψ ∼ ψ'
    -> E_lookup ψ x = Some σ
    -> Inst (t__Var_f x) σ t a τ (E_skvars ψ)
    -> exists σ',
        E_lookup ψ' x = Some σ'
      /\ Inst (t__Var_f x) σ' t a τ (E_skvars ψ').

  Variable R__fv : forall ψ ψ'
                    α,
      ψ ∼ ψ'
    -> α ∉ E_skvars ψ
    -> α ∉ E_skvars ψ'.

  Variable R__destr : forall ψ__in ψ__in' ψ__out ψ__out' ψ__cons,
      ψ__out +++ ψ__cons ∼ ψ__out'
    -> ψ__in ∼ ψ__in'
    -> SameLength__E ψ__in ψ__out
    -> exists ψ__out'', ψ__out' = ψ__out'' +++ ψ__cons
              /\ ψ__out ∼ ψ__out''.

  Variable U_R : forall ψ__in ψ__in' ψ__out τ1 τ2,
      U ψ__in τ1 τ2 ψ__out
    -> ψ__in ∼ ψ__in'
    -> exists ψ__out',
        ψ__out ∼ ψ__out'
      /\ U ψ__in' τ1 τ2 ψ__out'.

  Theorem Inf_R : forall ψ__in ψ__in' ψ__out e a τ t,
      ψ__in ⊢ e ▸ ⟨a⟩ τ ⤳ t ⊣ ψ__out
    -> ψ__in ∼ ψ__in'
    -> exists ψ__out',
        ψ__in' ⊢ e ▸ ⟨a⟩ τ ⤳ t ⊣ ψ__out'
      /\ ψ__out ∼ ψ__out'.
  Proof.
    assert (X: R_app_proper = R_app_proper /\ R__var = R__var /\ R__fv = R__fv /\ R__destr = R__destr). crush. clear X.
    introv Inf REL. gen ψ__in'. induction Inf; intros.
    (*Var*)
    - exists ψ__in'. splits.
      + forwards [σ' [? ?]]: R__var; try eassumption. eauto.
      + auto.

    (*Unit*)
    - exists. splits. crush. eassumption.

    (*Abs*)
    -
      (* forwards [tx NIL__tx]: atom_fresh L. *)
      forwards [x NIL__x]: atom_fresh (L ∪ (E_O_names (ψ__in' ::a α :: []) ∪ fv__x(e)) ∪ fv__x(t0)).
      forwards [ψ__out'' [?INF' REL__out']]: H x. fsetdec.
        norm. repeat rewrite <- E_app_assoc. apply R_app_proper. eassumption. reflexivity.
      forwards [ψ__out' [EQ REL__out]]: R__destr.
        norm in REL__out'. repeat rewrite <- E_app_assoc in REL__out'. applys REL__out'.
        apply REL. eapply Inf_SameLength. eapply Inf__Abs; eauto.
        subst. simpl+ in INF'.
      apply Inf_subst_name_head in INF'. 2:fsetdec. destruct INF' as [L' INF'].
      exists. splits.
      + applys Inf__Abs L'. eapply R__fv. eassumption. eassumption. eassumption.
        introy. applys INF'. fsetdec.
      + eassumption.

    (*App*)
    - forwards [ψ1' [Inf1' REL1']]: IHInf1. eassumption.
      forwards [ψ2'' [INF2' REL2'']]: IHInf2 (ψ1' ::o ⦇t1 ▸ ⟨a1⟩ S__T τ⦈). norm. apply R_app_proper. eassumption. crush.
      forwards SL: Inf_SameLength. apply Inf2. simpl+ in SL. inverts SL.
      forwards [ψ2' [EQ REL2']]: R__destr. norm in REL2''; apply REL2''. apply REL1'. eassumption. subst. clear REL2''.
      forwards [ψ__out'' [REL__out'' UNI']]: U_R. eassumption. norm. repeat rewrite <- E_app_assoc. apply R_app_proper. eassumption. reflexivity.
      forwards SL: U_SameLength. apply UNI. simpl+ in SL. inverts SL.
      forwards [ψ__out' [EQ REl__out']]: R__destr. norm in REL__out''. rewrite <- E_app_assoc in REL__out''. apply REL__out''. apply REL2'. eassumption. subst.
      exists. split.
      + applys Inf__App α. eassumption. applys_eq INF2'. eapply R__fv. 2:eassumption. norm. apply R_app_proper. eassumption. auto.
        assumption. applys_eq UNI'.
      + crush.

  (*Let*)
  - forwards [x NIL__x]: atom_fresh (L ∪ E_O_names ψ__in' ∪ fv__x(e2) ∪ fv__x(t2) ∪ fv__x(t1)).
    forwards [ψ' [Inf1' REL1]]: IHInf. eassumption.
    forwards [ψ__out'' [Inf2' REL2']]: H x. fsetdec.
      norm. repeat rewrite <- E_app_assoc. apply R_app_proper. eassumption. reflexivity.
    forwards SL: Inf_SameLength. applys INF2 x. fsetdec. simpl+ in SL. inverts SL.
    forwards [ψ__out' [EQ REL2]]: R__destr REL1 H1. norm in REL2'. repeat rewrite <- E_app_assoc in REL2'. apply REL2'.
      subst. clear REL2'. simpl+ in Inf2'.
    (**)
    forwards EQ__names: E_O_names_Inf. eapply Inf1'.
    forwards [L' Inf2'']: Inf_subst_name_head'. apply Inf2'. simpl+. rewrite <- EQ__names. clear - NIL__x. fsetdec.
     exists. splits.
    + applys Inf__Let L'. eassumption. introy.
      applys Inf2''. fsetdec.
    + eassumption.
  Qed.
End InfWeakening.

Section Inf_Weaken_ANil.
  Fact Insert_ANil_at_app_proper : forall n, Proper (Insert_ANil_at n ==> eq ==> Insert_ANil_at n) E__app.
  Proof. intro. autounfold. intros ψ1 ψ2 IN ? ψ3 EQ. subst. induction ψ3; crush. Qed.
  #[local] Hint Resolve Insert_ANil_at_app_proper : core.

  Lemma Insert_ANil_at__var : forall n, forall ψ ψ'
                      σ x t a τ,
      Insert_ANil_at n ψ ψ'
    -> E_lookup ψ x = Some σ
    -> Inst (t__Var_f x) σ t a τ (E_skvars ψ)
    -> exists σ',
        E_lookup ψ' x = Some σ'
      /\ Inst (t__Var_f x) σ' t a τ (E_skvars ψ').
  Proof.
    introv IA IN INST. forwards [ψ'' [ψ''' [EQ1 EQ2]]]: Insert_ANil_at_destr. eassumption. subst.
    exists σ. split.
    - clear - IN. simpl+ in *. eapply E_lookup_distr in IN. destruct IN as [?|[? ?]]. crush.
      simpl+. rewrite E_lookup_none__r. 2:eassumption. crush.
    - clear - INST. simpl+ in *. eassumption.
  Qed.
  #[local] Hint Resolve Insert_ANil_at__var : core.

  Lemma Insert_ANil_at__fv : forall n, forall ψ ψ'
                    α,
      Insert_ANil_at n ψ ψ'
    -> α ∉ E_skvars ψ
    -> α ∉ E_skvars ψ'.
  Proof.
    introv IA NIE. forwards [ψ'' [ψ''' [EQ1 EQ2]]]: Insert_ANil_at_destr. eassumption. subst.
    clear - NIE. simpl+ in *. eassumption.
  Qed.
  #[local] Hint Resolve Insert_ANil_at__fv : core.

  Lemma Insert_ANil_at__destr : forall n, forall ψ__in ψ__in' ψ__out ψ__out' ψ__cons,
      Insert_ANil_at n (ψ__out +++ ψ__cons) ψ__out'
    -> Insert_ANil_at n ψ__in ψ__in'
    -> SameLength__E ψ__in ψ__out
    -> exists ψ__out'', ψ__out' = ψ__out'' +++ ψ__cons
              /\ Insert_ANil_at n ψ__out ψ__out''.
  Proof.
    introv IN2 IN1 SL.
    assert (L: n <= E_length ψ__out). rewrite <- SL. eauto using Insert_ANil_at_smaller.
    gen ψ__out'. induction ψ__cons; intros.
    - simpl+ in IN2. exists. simpl+. crush.
    - inverts IN2. simpl+ in L. crush.
      forwards [ψ__out' [EQ IA]]: IHψ__cons. eassumption.
      exists. splits; simpl+; crush.
    - inverts IN2. simpl+ in L. crush.
      forwards [ψ__out' [EQ IA]]: IHψ__cons. eassumption.
      exists. splits; simpl+; crush.
    - inverts IN2. simpl+ in L. crush.
      forwards [ψ__out' [EQ IA]]: IHψ__cons. eassumption.
      exists. splits; simpl+; crush.
  Qed.
  #[local] Hint Resolve Insert_ANil_at__destr : core.

  Lemma U_Insert_ANil_at : forall n, forall ψ__in ψ__in' ψ__out τ1 τ2,
      U ψ__in τ1 τ2 ψ__out
    -> Insert_ANil_at n ψ__in ψ__in'
    -> exists ψ__out',
        Insert_ANil_at n ψ__out ψ__out'
      /\ U ψ__in' τ1 τ2 ψ__out'.
  Proof. exact Defs.Unification.U_Insert_ANil_at. Qed.
  #[local] Hint Resolve U_Insert_ANil_at : core.

  Lemma Inf_Insert_ANil_at : forall n ψ__in ψ__in' e a τ t ψ__out,
      ψ__in ⊢ e ▸ ⟨a⟩ τ ⤳ t ⊣ ψ__out
    -> Insert_ANil_at n ψ__in ψ__in'
    -> exists ψ__out', ψ__in' ⊢ e ▸ ⟨a⟩ τ ⤳ t ⊣ ψ__out'
             /\ Insert_ANil_at n ψ__out ψ__out'.
  Proof. introv INF IA. eapply Inf_R; eauto. Qed.

  Corollary Inf_weaken_ANil : forall ψ__in1 ψ__in2 e a τ t ψ__out,
      ψ__in1 +++ ψ__in2 ⊢ e ▸ ⟨a⟩ τ ⤳ t ⊣ ψ__out
    -> exists ψ__out', (ψ__in1 ::a []) +++ ψ__in2 ⊢ e ▸ ⟨a⟩ τ ⤳ t ⊣ ψ__out'
             /\ Insert_ANil_at (E_length ψ__in1) ψ__out ψ__out'.
  Proof.
    introv INF.
    forwards [ψ__in' IA]: Insert_ANil_at_create (E_length ψ__in1) (ψ__in1 +++ ψ__in2). crush.
    forwards [ψ__out'' [INF' IA']]: Inf_Insert_ANil_at (E_length ψ__in1). eassumption. eassumption.
    exists. splits. 2:eassumption. applys_eq INF'. symmetry. eapply Insert_ANil_at_app_destr. eassumption.
  Qed.

  Corollary Inf_weaken_ANil' : forall ψ__in1 ψ__in2 ψ__out1 ψ__out2 e a τ t,
      ψ__in1 +++ ψ__in2 ⊢ e ▸ ⟨a⟩ τ ⤳ t ⊣ ψ__out1 +++ ψ__out2
    -> SameLength__E ψ__in1 ψ__out1
    -> (ψ__in1 ::a []) +++ ψ__in2 ⊢ e ▸ ⟨a⟩ τ ⤳ t ⊣ (ψ__out1 ::a []) +++ ψ__out2.
  Proof.
    introv INF SL.
    forwards [ψ__out' [INF' IA]]: Inf_weaken_ANil. eassumption.
    applys_eq INF'. symmetry. eapply Insert_ANil_at_app_destr. crush.
  Qed.
End Inf_Weaken_ANil.
