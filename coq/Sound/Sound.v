Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.
Require Import Defs.HdmLems.

Require Import LibHyps.LibHyps.

Require Import Defs.DecA.
Require Import Defs.E.
Require Import Defs.EInst.
Require Import Defs.ERels.
Require Import Defs.FrA.
Require Import Defs.Foralls.
Require Import Defs.Lc.
Require Import Defs.List.
Require Import Defs.Inf.
Require Import Defs.OpenClose.
Require Import Defs.Shape.
Require Import Defs.Sub.
Require Import Defs.Subx.
Require Import Defs.WfE.
Require Import Defs.WfSTt.

Require Import Sound.RandomLems.
Require Import Sound.App.
Require Import Sound.Sub.

Inductive WfInf : E -> Ex -> A -> T -> Tm -> E -> Prop :=    (* defn Inf *)
 | WfInf__Var : forall (ψ:E) (x:var) (a:A) (τ:T) (t:Tm) (σ:Sc)
     (IN:  (E_lookup  ψ   x  = Some  σ  ) )
     (INST:  (Inst   (t__Var_f  x )    σ   t   a   τ  (E_skvars  ψ ) ) ),
     WfInf ψ (e__Var_f x) a τ t ψ
 | WfInf__Unit : forall (ψ:E),
     WfInf ψ e__Unit  nil  T__Unit t__Unit ψ
 | WfInf__Abs : forall (L:vars) (ψ__in:E) (e:Ex) (a1 a2:A) (τ1 τ2:T) (t:Tm) (ψ__out:E) (α:skvar)
     (FR:  ( α  ∉ (E_skvars  ψ__in )) )
     (ALG:  (alg  α ) )
     (INF:  ( forall x , x ∉  L  -> WfInf (E__Var (E__A ψ__in  (  α  :: nil ) ) x (S__T (T__Var_f α)))  ( open_Ex_wrt_Ex e (e__Var_f x) )  a2 τ2  (open_Tm_wrt_Tm  t  (t__Var_f  x ))  (E__Var (E__A ψ__out a1) x (S__T τ1)) ) ),
     WfInf ψ__in (e__Lam e)  (  a2  ++  a1  )  (T__Fun τ1 τ2)  (t__Lam  τ1   t )  ψ__out
 | WfInf__App : forall (ψ__in:E) (e1 e2:Ex) (a__out:A) (τ__out:T) (t__out:Tm) (ψ__out:E) (a1:A) (τ:T) (t1:Tm) (ψ1:E) (a2:A) (τ1:T) (t2:Tm) (ψ2:E) (t1':Tm) (a1':A) (τ':T) (α:skvar)
     (INF1: WfInf ψ__in e1 a1 τ t1 ψ1)
     (INF2: WfInf (E__O ψ1 t1 a1 (S__T τ)) e2 a2 τ1 t2 (E__O ψ2 t1' a1' (S__T τ')))
     (FR:  ( α  ∉ (E_skvars  (E__A ψ2   (  a2  ++  a1'  )  ) )) )
     (ALG:  (alg  α ) )
     (UNI: U  (E__O  (E__A ψ2   (   ( cons  α   a2  )   ++  a1'  )  )   (t__App t1' t2)  (nil:A)  (S__T (T__Var_f α)) )  τ' (T__Fun τ1 (T__Var_f α))  (E__O  (E__A ψ__out a__out)   t__out  (nil:A)  (S__T τ__out) ) ),
     WfInf ψ__in (e__App e1 e2) a__out τ__out t__out ψ__out
 | WfInf__Let : forall (L:vars) (ψ__in:E) (e1 e2:Ex) (a2:A) (τ2:T) (t2 t1':Tm) (ψout:E) (a1:A) (τ:T) (t1:Tm) (ψ1:E) (σ__out:Sc) (a1':A)
     (INF1: WfInf ψ__in e1 a1 τ t1 ψ1)
     (INF2:  ( forall x , x ∉  L  -> WfInf  (E__O   (E__O  (E__Var ψ1 x  (close_Sc_wrt_A ( S__T  τ  )  a1 ) )    (close_Tm_wrt_A  t1   a1 )   (nil:A) (S__T T__Unit))   t__Unit  a1  (S__T T__Unit))   ( open_Ex_wrt_Ex e2 (e__Var_f x) )  a2 τ2  (open_Tm_wrt_Tm  t2  (t__Var_f  x ))   (E__O   (E__O  (E__Var ψout x σ__out)   t1'  (nil:A) (S__T T__Unit))   t__Unit  a1'  (S__T T__Unit))  ) ),
     WfInf ψ__in (e__Let e1 e2) a2 τ2  (open_Tm_wrt_Tm  t2   t1' )  ψout.

Notation  "ψ1 ⊢wf e ▸ ⟨ a ⟩ τ ⤳ t ⊣ ψ2" := (WfInf ψ1 e a τ t ψ2) (at level 70, format "ψ1  ⊢wf  e  ▸  ⟨ a ⟩  τ  ⤳  t  ⊣  ψ2" ) : type_scope.

Lemma WfInf_lc : forall e ψ__in a τ t ψ__out,
    ψ__in ⊢wf e ▸ ⟨a⟩ τ ⤳ t ⊣ ψ__out
  -> lc(e).
Proof.
  introv INF. induction INF. econstructor. econstructor.
  - freshx L. eapply lc_e__Lam_exists. eauto.
  - constructor; eauto.
  - freshx L. eapply lc_e__Let_exists; eauto.
Qed.

Theorem Inf_sound_Inst : forall e ψ__in a τ t ψ__out ψ__dec t__dec a__dec τ__dec,
    ψ__in ⊢ e ▸ ⟨a⟩ τ ⤳ t ⊣ ψ__out
  -> wf(ψ__in)
  -> ψ__out ::o ⦇t ▸ ⟨a⟩ S__T τ⦈ ⤳' ψ__dec ::o ⦇t__dec ▸ ⟨a__dec⟩ S__T τ__dec⦈
  -> ψ__dec ⊢d' e ▸ ⟨a__dec⟩ τ__dec ⤳ t__dec.
Proof.
  introv INF. forwards E:Inf_lc INF.
  gen ψ__in a τ t0 ψ__out ψ__dec a__dec τ__dec t__dec. induction E; introv INF [θ EINST]; inverts INF.
  - forwards IN': EInst_E_lookup x σ. eassumption. simpl+. eassumption. simpl+ in IN'.
    inv_EInst'. applys DecA__Var. eassumption.
    + admit.

  (** unit *)
  - inv_EInst'. crush.

  (** app *)
  - inv_EInst'. onAllHyps move_up_types.
    (**)
    forwards WF1: Inf_Wf INF1. eassumption.
    forwards WF2: Inf_Wf INF2. eassumption.
    forwards: Inf_Wf_app α. eassumption. simpl+ in FR. fsetdec.
    assert (FR': (α :: a2 ++ a1') ### E_skvars ψ2). admit.
    assert (WF2': wf(ψ2 ::a α :: a2 ++ a1' ::o ⦇t__App t1' t2 ▸ ⟨[]⟩ S__T (T__Var_f α)⦈ ::o ⦇t__Unit ▸ ⟨[]⟩ S__T τ'⦈ ::o ⦇t__Unit ▸ ⟨[]⟩ S__T (T__Fun τ1 (T__Var_f α))⦈)).
      econstructor. econstructor. eapply Inf_Wf_app. eassumption. simpl+ in FR. fsetdec. auto.
      wfdec'. auto. auto.  eapply WfST1. apply WfT_Fun. split.
      wfdec'. apply WfT_var. simpl+. fsetdec. auto.
    (**)
    eapply U_unifies in UNI. destruct UNI as [τ__u UNI].
    forwards [?θ INST2]: U_maintains_instantiation. eassumption. exists. applys_eq EInst__O. econstructor. econstructor. econstructor. eassumption.
      apply FR0. applys_eq AINST. simpl+. crush. apply FrA_nil. auto. apply FrA_nil. auto. apply FrA_nil. auto. simpl+ in INST2.
      forwards PS: EInst_P_Sub' INST2. assumption. admit. admit.
      inv_EInst'.
      match goal with | [ H : ⟦_ ▹ t__App t1' t2⟧ = _ |- _ ] => rename H into SA__tapp end.
      simpl+ in SA__tapp. forwards [?t [?t ?EQ]]: Sub_app_Tm_destruct_App SA__tapp. subst. simpl+ in SA__tapp. inverts SA__tapp.
    forwards INST1: Inf_maintains_instantiation INF2. exists. econstructor. eassumption. eassumption. simpl+. eassumption.
      inv_EInst'.
    (**)
    specializes IHE1. eassumption. eassumption. exists. applys_eq EInst__O. eassumption. instantiate (1 := a__dec). eassumption. simpl+. eassumption.
    (**)
    specializes IHE2 (ψ1 ::a [] ::o ⦇t1 ▸ ⟨a1⟩ S__T τ0⦈) (ψ2 ::a [] ::o ⦇t1' ▸ ⟨a1'⟩ S__T τ'⦈). specializes IHE2.
      eapply (Inf_weaken_anil_insert 1) in INF2. applys_eq INF2. econstructor. eauto. eapply FrA_L_sub. eauto. simpl+. fsetdec.
      eapply WfS_E_A_sk_sub; eauto; erel_fsetdec. eapply Wft_E_A_sk_sub; eauto; erel_fsetdec.
      exists. applys_eq EInst__O. econstructor. econstructor. eassumption. instantiate (1 := a__dec). eassumption. auto. 1,3:apply FrA_nil.
      1,2:eapply AInst_E_sk_sub; try eassumption; erel_fsetdec. simpl+ in IHE2.
    (**)
    match goal with | [ _ : {_, _} ⊢e ψ2 ⤳ {_, ?θ} |- _ ] => rename θ into θ__ψ2  end.
    match goal with| [ _ : _ ⊢a a1' ⤳ ?θ |- _ ]           => rename θ into θ__a1' end.
    match goal with| [ _ : _ ⊢a a2 ⤳ ?θ |- _ ]            => rename θ into θ__a2  end.
    (**)
    forwards IHE2': DecA_weaken IHE2. instantiate (1 := ψ__dec ::a a__dec).
      (*-*)unfolds. simpl+. assert (UNI_SUB: forall L1 L2, L2 ⊆ L1 -> L1 ∪ L2 ≡ L1). intros. fsetdec. apply UNI_SUB. apply union_subset_iff.
          (*by EINST1, INSTA*) admit.
          (*by WF2*) admit.
      (*-*)unfolds. simpl+. fsetdec.
      (*-*)unfolds. simpl+. fsetdec.
    assert (PEQ1: θ__a1' ++ θ__ψ2 ⊆θ (τ2, α) :: θ__a2 ++ θ__a1' ++ θ__ψ2).
        splits. 1,2:apply P_Sub'_P_Sub. eapply P_Sub'_bindings_Sub. eassumption. reldec'. applys_eq PS. simpl+. reflexivity. reldec'.
    assert (PEQ2: θ__a2 ++ θ__ψ2 ⊆θ (τ2, α) :: θ__a2 ++ θ__a1' ++ θ__ψ2).
        splits. 1,2:apply P_Sub'_P_Sub. eapply P_Sub'_bindings_Sub. eassumption. reldec'. applys_eq PS. simpl+. reflexivity. reldec'.
    (**)
    applys_eq DecA__App. instantiate (2 := []). crush. simpl+. reflexivity. applys_eq IHE1. 3:applys_eq IHE2'.
    + simpl+.
      (*H14*) asserts_rewrite (⟦θ5 ++ θ2 ▹ τ0⟧ = ⟦θ__a1' ++ θ__ψ2 ▹ τ'⟧). assumption.
      transitivity ⟦((τ2, α) :: θ__a2 ++ θ__a1') ++ θ__ψ2 ▹ τ'⟧.
      (*H11*) asserts_rewrite (⟦((τ2, α) :: θ__a2 ++ θ__a1') ++ θ__ψ2 ▹ τ'⟧ = ⟦((τ2, α) :: θ__a2 ++ θ__a1') ++ θ__ψ2 ▹ T__Fun τ1 (T__Var_f α)⟧). eassumption.
      * simpl+. fequals. eapply P_Sub_sub_app_T_rewr. eapply EInst_full_Sub_T. econstructor. eassumption.
        2:simpl+; eassumption. eassumption. eapply WfT_E_A_sk_sub. instantiate (1 := ψ2 ::o ⦇t1' ▸ ⟨a1'⟩ S__T τ'⦈ ::a a2). eauto. erel_fsetdec.
        eassumption.
      * simpl+. symmetry. eapply P_Sub_sub_app_T_rewr. eapply EInst_full_Sub_T. applys_eq EInst__A. eassumption. eassumption. simpl+. eassumption. eauto.
        eassumption.
    + simpl+. symmetry.
      (*H10*) asserts_rewrite (⟦θ5 ++ θ2 ▹ t1⟧ = ⟦θ__a1' ++ θ__ψ2 ▹ t1'⟧). assumption. rewrite <- Sub_app_t_cons.
      eapply P_Sub_sub_app_Tm_rewr. eapply EInst_full_Sub_Tm. applys_eq EInst__A. eassumption. eassumption. simpl+. eassumption. eauto.
      eassumption.
    + (** case got added somehow *) admit.

  (** let *)
  - inv_EInst'. simpl+ in *. (* onAllHyps move_up_types. *) clear H. rename H0 into IH.
    forwards [x NIL__x]: atom_fresh (L ∪ E_skvars ψ__in ∪ E_names (ψ__in ::a [α])). specializes INF0 x. specializes INF0. fsetdec.
    assert (WF__in': wf((ψ__in ::a [α]) ::x x :- S__T (T__Var_f α))). econstructor. econstructor. eassumption.
      eapply FrA_singleton. fsetdec. split. crush. erel_fsetdec. fsetdec.
    forwards WF__out: Inf_Wf. eassumption. eassumption.
    (**)
      specializes IH. eassumption. eassumption.
      exists. applys_eq EInst__O. econstructor. econstructor. eassumption. applys FrA_L_sub FR0. simpl+. fsetdec. simpl+. eassumption.
      eapply FrA_nil. simpl+. applys AInst_E_sk_sub INSTA0. erel_fsetdec. simpl+ in IH.
    (**)
    applys DecA__Abs a__dec ([]:A). admit. intros y NIL__y. asserts_rewrite (y = x). admit. applys_eq IH.
    fequals. fequals. admit. assumption.

  - clear H. rename IHE into IH__e1. rename H0 into IH__e2. rename a__dec into a__dec2. rename a into a2.
    forwards [x NIL__x]: atom_fresh (L ∪ E_names ψ1).
    specializes INF2 x. specializes INF2. fsetdec.
    (**)
    inv_EInst'. simpl+ in *.
    forwards [?θ AINST__tmp]: AInst_trivial a1'.
    forwards: Inf_maintains_instantiation INF2. exists. econstructor. econstructor. econstructor. eassumption.
      eapply FrA_nil. auto. eapply FrA_nil. eassumption. clear AINST__tmp.
    simpl+ in H.

    inv_EInst'. onAllHyps move_up_types.
    (**)
    forwards WF1: Inf_Wf INF1. eassumption.
    assert (WF1': wf((ψ1 ::x x :- (∀ a1 ⬪ S__T τ0)) ::o ⦇Λ a1 ⬪ t1 ▸ ⟨[]⟩ S__T T__Unit⦈ ::o ⦇t__Unit ▸ ⟨a1⟩ S__T T__Unit⦈)).
      inverts WF1.
      forwards FV__σ: WfS_sk WFS. forwards FV__t: Wft_sk WFt. forwards FX__t: Wft_names WFt.
      econstructor. econstructor. econstructor. eassumption.
      split. admit. clear - FV__σ. simpl+ in *. admit. (* fsetdec. *) fsetdec. auto. split; crush.
      splits. admit. clear - FV__t. simpl+ in *. (* fsetdec. *) admit.
      clear - FX__t. simpl+ in *. fsetdec.
      applys FrA_L_sub FR0. simpl+. clear - FV__σ FV__t.
      rewrite E_A_skvars_E_skvars in FV__σ. rewrite E_A_skvars_E_skvars in FV__t.
      simpl+ in *. (* fsetdec. *) admit. crush. split; crush.
    forwards WF2: Inf_Wf INF2. assumption.
    (**)
    assert (exists a__dec1 θ__dec1, a__dec1 ### E_skvars ψ__dec /\ (ψ__dec ::a a__dec1) ⊢a a1 ⤳ θ__dec1). admit.
      destruct H as [a__dec1 [θ__dec1 [?FR ?AINST]]].
    (**)
    specializes IH__e1. eassumption. eassumption. exists. applys_eq EInst__O. eassumption. applys FrA_L_sub FR0. clfsetdec. simpl+. eassumption.
      simpl+ in IH__e1.
    (**)
    forwards [?θ AINST__tmp]: AInst_trivial a1'.
    specializes IH__e2. 1,2:eassumption. exists. applys_eq EInst__O.
      econstructor. econstructor. econstructor. eassumption. apply FrA_nil. auto.
      applys FrA_L_sub FR. simpl+. assert (FV__σ: fv__α(⟦θ ▹ σ__out⟧) ⊆ E_skvars ψ__dec). admit. assert (FV__t: fv__α(⟦θ ▹ t1'⟧) ⊆ E_skvars ψ__dec). admit.
      clear - FV__σ FV__t. fsetdec. eassumption.
      applys FrA_L_sub FR. simpl+. (*reasoning about wf sub*) admit.
      simpl+. applys AInst_E_sk_sub AINST. unfolds. simpl+. fsetdec.
      simpl+ in IH__e2.
    (**)
    applys_eq DecA__Let. fequals. dist. rewrite <- H8. rewrite Sub_app_Tm_close_Tm_wrt_A. rewrite Sub_app_Tm_close_Tm_wrt_A. reflexivity.
      1,4:(*lc_sub*)admit. 1,3:(*codom <> dom*)admit.
Admitted.

Corollary Inf_sound_open : forall e ψ__in a τ t ψ__out,
    ψ__in ⊢ e ▸ ⟨a⟩ τ ⤳ t ⊣ ψ__out
  -> wf(ψ__in)
  -> ψ__out ⊢d' e ▸ ⟨a⟩ τ ⤳ t.
Proof.
  introv INF WF.
  forwards [θ [EINST ID]]: EInst_id (ψ__out ::o ⦇t0 ▸ ⟨a⟩ S__T τ⦈). eauto using Inf_Wf.
  eauto using Inf_sound_Inst.
Qed.
