Set Warnings "-notation-overridden".

Require Import Preamble.
Require Import Preamble.Tag.
Require Import Defs.HdmLems.

Require Import LibHyps.LibHyps.

Require Import Defs.E.
Require Import Defs.EInst.
Require Import Defs.ERels.
Require Import Defs.FrA.
Require Import Defs.Foralls.
Require Import Defs.Inf.
Require Import Defs.Lc.
Require Import Defs.List.
Require Import Defs.Sub.
Require Import Defs.Subst.
Require Import Defs.TmTy.
Require Import Defs.WfE.

Require Import Complete.PrincipalTyping.
(* Require Import Complete.CompleteSS. *)
(* Require Import Complete.CompleteInst. *)
(* Require Import Complete.CompleteUnit. *)
(* Require Import Complete.CompleteLet. *)

Require Import Semantics.FundPropAdmit.

Lemma close_Tm_wrt_Tm_Sub_app_Tm : forall θ t x,
    lc(θ)
  -> close_Tm_wrt_Tm x ⟦θ ▹ t⟧ = ⟦θ ▹ close_Tm_wrt_Tm x t⟧.
Proof.
  introv LC. induction θ as [|[?τ ?α] ?θ]. crush. dist. rewrite <- IHθ. remember ⟦θ ▹ t0⟧ as t.
  symmetry. apply subst_skvar_Tm_close_Tm_wrt_Tm. eauto. eauto.
Qed.

(* Lemma DecA_add_obj : forall ψ e a τ t t__o a__o σ__o, *)
(*       ψ ⊢d' e ▸ ⟨a⟩ τ ⤳ t *)
(*     -> ψ ::o ⦇t__o ▸ ⟨a__o⟩ σ__o⦈ ⊢d' e ▸ ⟨a⟩ τ ⤳ t. *)
(* Proof. *)
(*   introv DECA. applys DecA_weaken DECA; unfolds; simpl+. 2:crush. 2:crush. *)
(*   assert (ψ *)

(* Axiom  AInst_trivial : forall a ψ, exists θ, *)
(*     ψ ⊢a a ⤳ θ. *)


(* Lemma Inf_complete_let_rewr_e1 : forall σ' a1' ψ x σ a1 e a2 τ t, *)
(*     (ψ ::x x :- σ ::o ⦇t__Unit ▸ ⟨a1⟩ S__T T__Unit⦈) ⊢d' e ▸ ⟨a2⟩ τ ⤳ t *)
(*   -> SubSump' ψ σ σ' *)
(*   -> wf(ψ ::x x :- σ ::o ⦇t__Unit ▸ ⟨a1⟩ S__T T__Unit⦈) *)
(*   -> exists a2' τ' t', *)
(*     (ψ ::x x :- σ' ::o ⦇t__Unit ▸ ⟨a1'⟩ S__T T__Unit⦈) ⊢d' e ▸ ⟨a2'⟩ τ' ⤳ t' *)
(*   /\ (∀ a2 ⬪ S__T τ) = (∀ a2' ⬪ S__T τ') *)
(*   /\ ψ ⊢t≈ (Λ a2 ⬪ t) ≈ (Λ a2 ⬪ t') ▸ (∀ a2 ⬪ S__T τ). *)
(* Admitted. *)

(* Ltac EInst_constr := *)
(*     match goal with *)
(*     | |- {_, _} ⊢e E__Nil ⤳ {_, _}  => econstructor *)
(*     | |- {_, _}⊢e _ ::a _ ⤳ {_, _} => applys_eq EInst__A *)
(*     | |- {_, _}⊢e _ ::x _ :- _ ⤳ {_, _} => applys_eq EInst__S *)
(*     | |- {_, _}⊢e _ ::o ⦇_ ▸ ⟨_⟩ _⦈ ⤳ {_, _} => applys_eq EInst__O *)
(*     end. *)

Theorem Inf_complete_open : forall e ψ__dec a__np τ__np t__np,
    ψ__dec ⊢d' e ▸ ⟨a__np⟩ τ__np ⤳ t__np
  -> forall ψ__in, ψ__in ⤳' ψ__dec
  -> exists a__p τ__p t__p ψ__out a__alg τ__alg t__alg,
      ψ__dec ⊢d' e ▸ ⟨a__p⟩ τ__p ⤳ t__p
    /\ SubSumpTmEq ψ__dec a__p t__p τ__p a__np t__np τ__np
    /\ ψ__in ⊢ e ▸ ⟨a__alg⟩ τ__alg ⤳ t__alg ⊣ ψ__out
    /\ ψ__out ::o ⦇t__alg ▸ ⟨a__alg⟩ S__T τ__alg⦈ ⤳' ψ__dec ::o ⦇t__p ▸ ⟨a__p⟩ S__T τ__p⦈.
Proof.
  introv DEC. forwards E: DecA_lc DEC. gen ψ__dec a__np τ__np t__np. induction E.
  all: introv DECA [θ INST]; inverts DECA.

  (** var *)
  - admit.

  (** unit *)
  - admit.
  (* - exists. splits. 1,3:auto. *)
  (*   + unfolds. exists. simpl+. splits. eauto using complete_unit_SubSump. *)
  (*     eauto using FundamentalProperty, complete_unit_TmTy. *)
  (*   + exists. applys_eq EInst__O. 2:eassumption. 2:apply FrA_nil. 2:auto. simpl+. crush. *)

  (** app *)
  - admit.

  (** abs *)
  - clear H. rename H0 into IH. rename τ1 into τ__x. rename τ2 into τ__np2. rename t0 into t__np.
    rename a1 into a__x. rename a2 into a__np2. rename INST into INST__in.
    (**)
    freshx L.
    freshalgα (L ∪ dom_Sub θ ∪ E_skvars ψ__in).
    specializes DEC x. specializes DEC. fsetdec.
    specializes IH. eauto. exists. instantiate (2 := ψ__in ::a [α] ::x x :- S__T (T__Var_f α)).
      applys_eq EInst__S. 2:applys_eq EInst__A. 2:eassumption. instantiate (1 := [(τ__x, α)]). simpl+. fequals. fequals.
      dist. rewrite Sub_app_T_notindom. 2:simpl+; fsetdec. simpl+. if_taut. assumption.
      econstructor. auto. simpl+. applys_eq WFT.
      destruct IH as [a__p2 [τ__p2 [t__p [ψ__out' [a2 [τ2 [t [DECA__p [SSE [INF INST__out]]]]]]]]]].
      assert (ADM: exists ψ__out a1 τ__x', ψ__out' = ψ__out ::a a1 ::x x :- S__T τ__x'). admit.
      destruct ADM as [ψ__out [a1 [τ__x' EQ]]]. subst.
    (**)
    exists (a__p2 ++ a__x) (T__Fun τ__x τ__p2) (t__Lam τ__x (close_Tm_wrt_Tm x t__p)). exists ψ__out (a2 ++ a1) (T__Fun τ__x' τ2) (t__Lam τ__x' (close_Tm_wrt_Tm x t)). splits.
    + applys DecA__Abs L. eassumption.
      introy. asserts_rewrite (y = x) in *. admit. rewrite open_Tm_wrt_Tm_close_Tm_wrt_Tm. crush. eassumption.
    + admit.
    + applys Inf__Abs L α. fsetdec. assumption. introz. asserts_rewrite (z = x) in *. admit. applys_eq INF. apply open_Tm_wrt_Tm_close_Tm_wrt_Tm.
    + inv_EInst'. onAllHyps move_up_types. exists.
      applys_eq EInst__O. 2:eassumption. instantiate (1 := (θ3 ++ θ2)). simpl+. fequals. fequals.
      dist. symmetry. apply Sub_app_T_notindom. admit.
      apply close_Tm_wrt_Tm_Sub_app_Tm. admit. fequals. fequals.
      dist. symmetry. apply Sub_app_T_notindom. admit. admit. admit.

  (** let *)
  - clear E H. rename IHE into IH__e1. rename H0 into IH__e2. rename DEC1 into DEC__e1. rename DEC2 into DEC__e2.
    rename τ1 into τ__np1. rename τ__np into τ__np2. rename t1 into t__np1. rename t2 into t__np2.
    rename a1 into a__np1. rename a__np into a__np2. rename INST into INST__in. onAllHyps move_up_types.
    (** IH e1 *)
    specializes IH__e1. eassumption. exists. eassumption.
      destruct IH__e1 as [a__p1 [τ__p1 [t__p1 [ψ1 [a1 [τ1 [t1 [DEC__p1 [EQ1 [INF__e1 INST1]]]]]]]]]].
      clear INST__in. inv_EInst'. onAllHyps move_up_types.



    freshx L.
    forwards [a__np2' [τ__np2' [t__np2' [DEC__e2' [EQ__τ' EQ1']]]]]: Inf_complete_let_rewr_e1 (∀ a__p1 ⬪ S__T ⟦θ3 ++ θ0 ▹ τ1⟧) a__p1 DEC__e2.
      admit. admit. admit.

    specializes IH__e2 (ψ__dec ::x x :- (∀ a__p1 ⬪ S__T ⟦θ3 ++ θ0 ▹ τ1⟧) ::o ⦇t__Unit ▸ ⟨a__p1⟩ S__T T__Unit⦈)
                     (ψ1   ::x x :- (∀ a1 ⬪ S__T τ1)               ::o ⦇t__Unit ▸ ⟨a1 ⟩ S__T T__Unit⦈).
    specializes IH__e2. exists. EInst_constr. 2:EInst_constr. 2:eassumption. simpl+. reflexivity.








    (** trying *)
    freshx L.
    specializes DEC__e2 x. specializes DEC__e2. fsetdec.

    forwards EINST1: EInst__O t__Unit a1 (S__T T__Unit).
      instantiate (3 := ψ1 ::x x :- (∀ a1 ⬪ S__T τ1) ::o ⦇Λ a1 ⬪ t1 ▸ ⟨[]⟩ S__T T__Unit⦈).
      eapply EInst__O. eapply EInst__S. eassumption. admit. auto.
      applys FrA_L_sub FR. admit. simpl+. applys AInst_E_sk_sub AINST. reldec.
      simpl+ in EINST1.

    forwards [a__np2' [τ__np2' [t__np2' [DEC__e2' [EQ__τ' EQ1']]]]]: Inf_complete_let_rewr_e1 (∀ a__p1 ⬪ S__T ⟦θ3 ++ θ0 ▹ τ1⟧) a__p1 DEC__e2.
      admit. admit.

    forwards [a__np2'' [τ__np2'' [t__np2'' [DEC__e2'' [EQ__τ'' EQ1'']]]]]: Inf_complete_let_rewr_e1 (⟦θ0 ▹ ∀ a1 ⬪ S__T τ1⟧) a__p1 DEC__e2.
      admit. admit.


    specializes IH__e2. 2:exists; eapply EINST1. applys_eq DEC__e2'. admit.
      destruct IH__e2 as [a__p2 [τ__p2 [t__p2 [ψ__out' [a2 [τ2 [t2 [DEC__p2 [EQ2 [INF__e2 INST__out]]]]]]]]]].
      assert (ADM: exists ψ__out σ__out t1' a__p1', ψ__out' = ψ__out ::x x :- σ__out ::o ⦇t1' ▸ ⟨[]⟩ S__T T__Unit⦈ ::o ⦇t__Unit ▸ ⟨a__p1'⟩ S__T T__Unit⦈).
      admit. destruct ADM as [ψ__out [σ__out [t1' [a__p1' EQ]]]]. subst.
      inv_EInst'. onAllHyps move_up_types.

    exists. splits.
    + econstructor. eassumption. introy.
    + admit.
    + econstructor. eassumption. intros.

    (* (** IH e2 *) *)
    (* freshx L. specializes DEC__e2 x. specializes DEC__e2. fsetdec. *)


    (* assert ((∅) ⊢e' ψ1 ::x x :- (∀ a1 ⬪ S__T τ1) ::o ⦇Λ a1 ⬪ t1 ▸ ⟨[]⟩ S__T T__Unit⦈ ::o ⦇t__Unit ▸ ⟨a__np1⟩ S__T T__Unit⦈ ⤳ *)
    (*           ((ψ__dec ::x x :- ⟦θ0 ▹ ∀ a1 ⬪ S__T τ1⟧) ::o ⦇⟦θ0 ▹ Λ a1 ⬪ t1⟧ ▸ ⟨[]⟩ S__T T__Unit⦈) ::o ⦇t__Unit ▸ ⟨[]⟩ S__T T__Unit⦈). *)
    (* { forwards [?θ ?AINST]: AInst_trivial. *)
    (*   exists. applys_eq EInst__O. fequals. simpl+. reflexivity. simpl+. reflexivity. 2:auto. 2:eassumption. *)
    (*   applys_eq EInst__O. fequals. 3:applys_eq EInst__S. 4:eassumption. 5:auto. *)
    (*   all:simpl+; fequals. auto. *)
    (* } *)


    specializes IH__e2 (((ψ__dec ::x x :- ⟦θ0 ▹ ∀ a1 ⬪ S__T τ1⟧) ::o ⦇⟦θ0 ▹ Λ a1 ⬪ t1⟧ ▸ ⟨[]⟩ S__T T__Unit⦈) ::o ⦇t__Unit ▸ ⟨a__p1⟩ S__T T__Unit⦈)
                     (ψ1 ::x x :- (∀ a1 ⬪ S__T τ1) ::o ⦇Λ a1 ⬪ t1 ▸ ⟨[]⟩ S__T T__Unit⦈ ::o ⦇t__Unit ▸ ⟨a1⟩ S__T T__Unit⦈).
      applys_eq DEC__e2. admit. specializes IH__e2.
      forwards [?θ ?AINST]: AInst_trivial.
      exists. applys_eq EInst__O. fequals. 1,2:simpl+; reflexivity. 2:admit. 2:eassumption.
      applys_eq EInst__O. 2:applys_eq EInst__S. 2:eassumption. 3:auto. simpl+. fequals. auto.
      destruct IH__e2 as [a__p2 [τ__p2 [t__p2 [ψ__out' [a2 [τ2 [t2 [DEC__p2 [EQ2 [INF__e2 INST__out]]]]]]]]]].
      assert (ADM: exists ψ__out σ__out t1' a__p1', ψ__out' = ψ__out ::x x :- σ__out ::o ⦇t1' ▸ ⟨[]⟩ S__T T__Unit⦈ ::o ⦇t__Unit ▸ ⟨a__p1'⟩ S__T T__Unit⦈).
      admit. destruct ADM as [ψ__out [σ__out [t1' [a__p1' EQ]]]]. subst.
      clear EINST AINST. inv_EInst'. onAllHyps move_up_types.

    exists a__p2. exists. splits. econstructor. applys DEC__p1. introy. applys_eq DEC__p2. admit. admit. admit. admit.
    econstructor. eassumption. introy. applys_eq INF__e2. admit. admit. admit. admit.


    assert (TYP__e2: Typable (ψ__dec ::x x :- (∀ a__p1 ⬪ S__T τ__x) ::o ⦇Λ a__p1 ⬪ t__p1 ▸ ⟨[]⟩ S__T T__Unit⦈) (open_Ex_wrt_Ex e2 (e__Var_f x))).
      forwards [a' [τ' [t' DEC__e2']]]: DecA_generalize_binding (∀ a__p1 ⬪ S__T τ__x) DEC__e2.
      destruct PRIN1 as [_ H]. specializes H DEC__e1. destruct H as [t' [SST _]].
      eapply SubSumpTm'_SubSump. eassumption.
      forwards [a'' [τ'' [t'' DEC__e2'']]]: DecA_weaken_app  (<⦇Λ a__p1 ⬪ t__p1 ▸ ⟨[]⟩ S__T T__Unit⦈>o). eassumption.
      unfolds. exists. applys_eq DEC__e2''.
    assert (INST1': (∅) ⊢e' ψ1 ::x x :- (∀ a1 ⬪ S__T τ1) ::o ⦇Λ a1 ⬪ t1 ▸ ⟨[]⟩ S__T T__Unit⦈
                      ⤳ ψ__dec ::x x :- (∀ a__p1 ⬪ S__T τ__x) ::o ⦇Λ a__p1 ⬪ t__p1 ▸ ⟨[]⟩ S__T T__Unit⦈). admit.
    (**)
    specializes IH__e2 TYP__e2 INST1'.
      destruct IH__e2 as [a__p2 [τ__p2 [t__p2 [ψ__out' [a2 [τ2 [t2 [PRIN2 [INF__e2 INST__out]]]]]]]]].
      assert (ADM: exists ψ__out σ__out t1', ψ__out' = ψ__out ::x x :- σ__out ::o ⦇t1' ▸ ⟨[]⟩ S__T T__Unit⦈).
      admit. destruct ADM as [ψ__out [σ__out [t1' EQ]]]. subst.
      clear INST1 INST1' DEC__e1 DEC__e2. onAllHyps move_up_types.
    (**)
    exists a__p2 τ__p2 ({(Λ a__p1 ⬪ t__p1) ≔__x x} t__p2). exists ψ__out a2 τ2 ({t1' ≔__x x} t2). splits.
    + admit.
    + applys_eq Inf__Let. rewrite subst_tvar_Tm_spec. reflexivity. eassumption.
      intros y NIL__y. asserts_rewrite (y = x). admit. applys_eq INF__e2. apply open_Tm_wrt_Tm_close_Tm_wrt_Tm.
    + clear PRIN1 PRIN2 INF__e1 INF__e2 TYP__e2.
      inv_EInst'. simpl+ in *. onAllHyps move_up_types.
      exists. applys_eq EInst__O. 2:eassumption. 2:instantiate (1 := a__p2); admit. 2:applys_eq AINST; admit.
      simpl+. fequals.
      rewrite <- Sub_app_Tm_subst_tvar_Tm'. fequals. admit.
Admitted.
d
