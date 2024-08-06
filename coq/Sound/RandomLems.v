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

Lemma Inst_sound : forall t1 t2 σ τ ψ a L,
    Inst t1 σ t2 a τ L
  -> E_skvars ψ ⊆ L
  -> SubSumpTmA ψ t1 σ t2 a τ.
Proof.
  introv INST SUB. gen ψ. induction INST; intros. eauto.
  specializes IHINST (ψ ::a [α]). specializes IHINST. erel_fsetdec.
  applys_eq SSTA__L. 4:eassumption. crush. eapply FrA_singleton. fsetdec.
  split. econstructor. erel_fsetdec.
Qed.

Corollary Inf_Wf' : forall e ψ__in a τ t ψ__out,
    ψ__in ⊢ e ▸ ⟨a⟩ τ ⤳ t ⊣ ψ__out
  -> wf(ψ__in)
  -> wf(ψ__out).
Proof. intros. forwards: Inf_Wf. all:eauto. Qed.

Definition Sub_id (θ:Sub) : Prop := forall τ α, (τ, α) ∈τx bindings_Sub θ -> τ = T__Var_f α.

Fact Sub_id_nil :
    Sub_id [].
Proof. unfolds. intros. simpl+ in H. crush. Qed.
#[export] Hint Resolve Sub_id_nil : core.

Lemma Sub_id_cons: forall (α : skvar) (θ : Sub),
    Sub_id θ
  -> Sub_id ((T__Var_f α, α) :: θ).
Proof.
  unfold Sub_id in *. intros. simpl+ in H0. destr_union. inverts H0. crush. eauto.
Qed.
#[export] Hint Resolve Sub_id_cons : core.

Lemma Sub_id_cons_destr : forall τ (α : skvar) (θ : Sub),
    Sub_id ((τ, α) :: θ)
  -> Sub_id θ.
Proof.
  unfold Sub_id in *. intros. eapply H. simpl+. fsetdec'.
Qed.
#[export] Hint Resolve Sub_id_cons_destr : core.

Lemma Sub_id_app : forall (θ1 θ2:Sub),
    Sub_id θ1
  -> Sub_id θ2
  -> Sub_id (θ1 ++ θ2).
Proof. unfold Sub_id; intros. simpl+ in H1. destr_union; auto. Qed.
#[export] Hint Resolve Sub_id_app : core.

Lemma Sub_app_Sc_id : forall θ (σ:Sc),
    Sub_id θ
  -> ⟦θ ▹ σ⟧ = σ.
Proof.
  intro θ. ind_Sub θ. crush.
  intros. dist. rewrite IHθ. 2:eauto.
  unfolds in H. specializes H τ α. specializes H. simpl+. fsetdec. subst.
  rewrite subst_skvar_Sc_spec. rewrite open_Sc_wrt_T_close_Sc_wrt_T. crush.
Qed.

Lemma Sub_app_Tm_id : forall θ (t:Tm),
    Sub_id θ
  -> ⟦θ ▹ t⟧ = t.
Proof.
  intro θ. ind_Sub θ. crush.
  intros. dist. rewrite IHθ. 2:eauto.
  unfolds in H. specializes H τ α. specializes H. simpl+. fsetdec. subst.
  rewrite subst_skvar_Tm_spec. rewrite open_Tm_wrt_T_close_Tm_wrt_T. crush.
Qed.


Lemma AInst_id : forall a ψ,
    exists θ,
    (ψ ::a a) ⊢a a ⤳ θ
  /\ Sub_id θ.
Proof.
  intro a. ind_a a; introv.
  - exists. auto.
  - specializes IHa (ψ ::a [α]). destruct IHa as [θ [AINST ID]].
    exists. split. applys AInst__C (T__Var_f α). applys AInst_E_sk_sub AINST. erel_fsetdec.
    split. crush. erel_fsetdec. eauto.
Qed.

Lemma EInst_id : forall ψ,
    wf(ψ)
  -> exists θ,
    {•, []} ⊢e ψ ⤳ {ψ, θ}
  /\ Sub_id θ.
Proof.
  intro ψ. induction ψ; introv WF; inverts WF.
  - exists. auto.
  - specializes IHψ WFE. destruct IHψ as [θ [EINST ID]].
    forwards [θ__a [AINST ID__a]]: AInst_id a.
    exists. econstructor. econstructor. eassumption. simpl+. eassumption. simpl+. eassumption. auto.
  - specializes IHψ WFE. destruct IHψ as [θ [EINST ID]].
    exists. split. applys_eq EInst__S. 2,3:eassumption. fequals. simpl+. eauto. symmetry. apply Sub_app_Sc_id. auto.
  - specializes IHψ WFE. destruct IHψ as [θ [EINST ID]].
    forwards [θ__a [AINST ID__a]]: AInst_id a.
    exists. split. applys_eq EInst__O. 2,5:eassumption. 2:applys FrA_L_sub FR; fsetdec. 2:simpl+; applys_eq AINST. fequals; symmetry; simpl+.
    + eauto using Sub_app_Tm_id.
    + eauto using Sub_app_Sc_id.
Qed.

Lemma Inf_maintains_instantiation : forall e ψ__in a τ t ψ__out ψ__dec,
    ψ__in ⊢ e ▸ ⟨a⟩ τ ⤳ t ⊣ ψ__out
  -> ψ__out ⤳' ψ__dec
  -> ψ__in  ⤳' ψ__dec.
Admitted.

Lemma  AInst_trivial : forall a ψ, exists θ,
    ψ ⊢a a ⤳ θ.
Proof. intro a. ind_a a; intros. exists ([]:Sub). crush. specializes IHa. destruct IHa as [θ AINST]. exists ((T__Unit, α) :: θ). econstructor. eassumption. crush. Qed.


Lemma SubSumpTmA_shift_a : forall σ ψ t__in t__out a τ,
    SubSumpTmA ψ        t__in σ t__out  a τ
  -> SubSumpTmA (ψ ::a a) t__in σ t__out [] τ.
Proof.
  intro σ. forall_ind σ; introv SS; inverts SS.
  - econstructor. crush.
  - forwards: IHn SS0. simpl+. crush.
    applys_eq SSTA__L. instantiate (1 := []). crush. auto.
    applys WfT_E_A_sk_sub WFT. erel_fsetdec.
    applys SubSumpTmA_E_A_sk_sub H. erel_fsetdec. erel_fsetdec.
Qed.

Lemma SubSumpTm_SubSumpTmA : forall σ ψ a t__in t__out τ,
    SubSumpTm  (ψ ::a a) t__in σ t__out   τ
  -> SubSumpTmA ψ        t__in σ t__out a τ.
Abort.

Lemma SubSumpTm_SubSumpTmA : forall σ ψ a t__in t__out τ,
    SubSumpTm  (ψ ::a a) t__in σ t__out   τ
  -> SubSumpTmA ψ        t__in σ t__out a τ.
Proof.
  intro σ. forall_ind σ; introv SS; inverts SS.
  - econstructor. admit.
  - forwards: IHn. 2:eassumption. simpl+. crush.

    applys_eq SSTA__L. instantiate (1 := []). simpl+. reflexivity. 2:eassumption. admit.
Abort.

Lemma Inf_sound_Inst_var : forall σ t1 t2 a τ L ψ__dec θ θ__a,
    Inst t1 σ t2 a τ L
  -> fv__α(t1) ⊆ L
  (* -> fv__α(⟦θ ▹ t1⟧) ⊆ L *)
  -> dom_Sub θ ∐ varl a
  (* -> skvars_codom_Sub θ ⊆ L *)
  (* -> skvars_codom_Sub θ ⊆ L *)
  -> ψ__dec ⊢a a ⤳ θ__a
  -> SubSumpTm ψ__dec ⟦θ ▹ t1⟧ ⟦θ ▹ σ⟧ ⟦θ__a ++ θ ▹ t2⟧ ⟦θ__a ++ θ ▹ τ⟧.
Proof.
  intro σ. forall_ind σ.
  - introv INST _ _ AINST. inverts INST. inv_AInst. simpl+. crush.
  - introv INST SUB1 DISJ1 AINST. inverts INST. inv_AInst.
    specializes IHn ((τ0, α) :: θ) INST0. simpl+. crush. specializes IHn. simpl+. fsetdec. simpl+.
    admit.
    eassumption.
    (**)
    assert (DISJ2: dom_Sub θ ∐ Metatheory.singleton α). clear - DISJ1. disj_sub.
    simpl+. econstructor. eassumption.
    applys_eq IHn; simpl+.
    + fequals. subst_notin'. admit. admit.
    + rewrite Sub_app_Sc_open_Sc_wrt_T. 2:admit. fequals.
      dist. subst_notin'. admit. dist. Sub_notin'. simpl+. if_taut. crush.
    + (** sub_reorder *) admit.
    + (** sub_reorder *) admit.
Admitted.

Lemma SubSumpTm_SubSumpTmA' : forall σ ψ t1 t2 a τ,
    SubSumpTm (ψ ::a a) t1 σ t2 τ
  -> a ### E_skvars ψ
  -> SubSumpTmA ψ t1 σ t2 a τ.
Proof.
  intro σ. forall_ind σ.
  - introv SS FR. inverts SS. eauto.
  - introv SS FR. inverts SS.
    applys_eq SSTA__L. 3:eassumption. instantiate (1 := []). crush. eassumption.
    apply SubSumpTmA_shift_a. eapply IHn. 2:eassumption. simpl+. crush. eassumption.
Qed.

Lemma Inf_sound_Inst_var_A : forall σ t1 t2 a τ L a__dec ψ__dec θ θ__a,
    Inst t1 σ t2 a τ L
  -> fv__α(t1) ⊆ L
  -> fv__α(⟦θ ▹ t1⟧) ⊆ L
  -> dom_Sub θ ∐ varl a
  -> (ψ__dec ::a a__dec) ⊢a a ⤳ θ__a
  -> a__dec ### E_skvars ψ__dec
  -> SubSumpTmA ψ__dec ⟦θ ▹ t1⟧ ⟦θ ▹ σ⟧ ⟦θ__a ++ θ ▹ t2⟧ a__dec ⟦θ__a ++ θ ▹ τ⟧.
Proof. intros. apply SubSumpTm_SubSumpTmA'. eauto using Inf_sound_Inst_var. eassumption. Qed.


(* Lemma Inf_sound_Inst_var' : forall σ t1 t2 a τ L a__dec ψ__dec θ θ__a, *)
(*     Inst t1 σ t2 a τ L *)
(*   -> a__dec ### (E_skvars ψ__dec) *)
(*   -> fv__α(t1) ⊆ L *)
(*   -> skvars_codom_Sub θ ⊆ L *)
(*   (* -> skvars_codom_Sub θ ⊆ L *) *)
(*   -> (ψ__dec ::a a__dec) ⊢a a ⤳ θ__a *)
(*   -> SubSumpTmA ψ__dec ⟦θ ▹ t1⟧ ⟦θ ▹ σ⟧ ⟦θ__a ++ θ ▹ t2⟧ a__dec ⟦θ__a ++ θ ▹ τ⟧. *)
(* Proof. *)
(*   intro σ. forall_ind σ. *)
(*   - admit. *)
(*   - introv INST FR SUB1 SUB2 AINST. inverts INST. inv_EInst'. *)
(*     forwards: IHn ([]:A) (ψ__dec ::a a__dec) ((τ0, α) :: θ) INST0. simpl+. crush. auto. simpl+. fsetdec. admit. simpl+. applys_eq AINST0. admit. *)
(*     (**) *)
(*     simpl+. applys_eq SSTA__L. instantiate (1 := []). simpl+. reflexivity. auto. *)
(*     instantiate (1 := {τ0 ≔ α}⟦θ2 ++ θ ▹ T__Var_f α⟧). admit. *)
(*     applys_eq H. simpl+. fequals. *)
(*     + subst_notin'. rewrite Sub_app_Tm_fsk'. admit. *)

(*     + dist. fequals. Sub_notin'. Sub_notin'. admit. admit. *)
(*     + admit. *)
(*     + admit. *)
(*     + admit. *)
(* Admitted. *)



Lemma Sub_app_Tm_destruct_App: forall t1 t2 t θ,
    t__App t1 t2 = ⟦θ ▹ t⟧
  -> exists t1' t2', t = t__App t1' t2'.
Proof. intros. destruct t0; simpl+ in H; inverts H. exists. crush. Qed.


#[derive(equations=no)] Equations E_take (n:nat) : E -> E :=
  E_take 0 _                  := •;
  E_take n •                  := •;
  E_take n (ψ ::a a)           := (E_take (n - 1) ψ) ::a a;
  E_take n (ψ ::x x :- σ)      := (E_take (n - 1) ψ) ::x x :- σ;
  E_take n (ψ ::o ⦇t ▸ ⟨a⟩ σ⦈) := (E_take (n - 1) ψ) ::o ⦇t ▸ ⟨a⟩ σ⦈.

#[derive(equations=no)] Equations E_drop (n:nat) : E -> E :=
  E_drop 0 ψ                  := ψ;
  E_drop n •                  := •;
  E_drop n (ψ ::a a)           := E_drop (n - 1) ψ;
  E_drop n (ψ ::x x :- σ)      := E_drop (n - 1) ψ;
  E_drop n (ψ ::o ⦇t ▸ ⟨a⟩ σ⦈) := E_drop (n - 1) ψ.

Notation E_split n ψ := (E_drop n ψ, E_take n ψ).

Fact E_split_app : forall n ψ ψ1 ψ2, E_split n ψ = (ψ1, ψ2) -> ψ = ψ1 +++ ψ2.
Proof.
  intro n. induction n; intros. simpl+ in H. inverts H. crush.
  destruct ψ; simpl in H.
  - inverts H. crush.
  - inverts H. asserts_rewrite (n - 0 = n). crush. simpl+. fequals. eauto.
  - inverts H. asserts_rewrite (n - 0 = n). crush. simpl+. fequals. eauto.
  - inverts H. asserts_rewrite (n - 0 = n). crush. simpl+. fequals. eauto.
Qed.

Notation insert_a_at n ψ a := (((E_drop n ψ) ::a a) +++ (E_take n ψ)).

Lemma Inf_weaken_anil_insert : forall n ψ__in e a τ t ψ__out,
    ψ__in ⊢ e ▸ ⟨a⟩ τ ⤳ t ⊣ ψ__out
  -> (insert_a_at n ψ__in []) ⊢ e ▸ ⟨a⟩ τ ⤳ t ⊣ (insert_a_at n ψ__out []).
Admitted.
Lemma Inf_weaken_anil : forall ψ__in e a τ t ψ__out,
    ψ__in ⊢ e ▸ ⟨a⟩ τ ⤳ t ⊣ ψ__out
  -> ψ__in ::a [] ⊢ e ▸ ⟨a⟩ τ ⤳ t ⊣ ψ__out ::a [].
Proof. intros. applys Inf_weaken_anil_insert 0. eassumption. Qed.
Lemma Inf_strengthen_anil : forall ψ__in e a τ t ψ__out,
    ψ__in ::a [] ⊢ e ▸ ⟨a⟩ τ ⤳ t ⊣ ψ__out ::a []
  -> ψ__in ⊢ e ▸ ⟨a⟩ τ ⤳ t ⊣ ψ__out.
Admitted.

Lemma Inf_weaken_obj : forall t__obj a__obj σ__obj ψ__in e a τ t ψ__out,
    ψ__in ⊢ e ▸ ⟨a⟩ τ ⤳ t ⊣ ψ__out
  -> exists t__obj' a__obj' σ__obj', (ψ__in ::o ⦇t__obj ▸ ⟨a__obj⟩ σ__obj⦈) ⊢ e ▸ ⟨a⟩ τ ⤳ t ⊣ (ψ__out ::o ⦇t__obj' ▸ ⟨a__obj'⟩ σ__obj'⦈).
Admitted.
Lemma Inf_strengthen_obj : forall t__obj a__obj σ__obj t__obj' a__obj' σ__obj' ψ__in e a τ t ψ__out,
    (ψ__in ::o ⦇t__obj ▸ ⟨a__obj⟩ σ__obj⦈) ⊢ e ▸ ⟨a⟩ τ ⤳ t ⊣ (ψ__out ::o ⦇t__obj' ▸ ⟨a__obj'⟩ σ__obj'⦈)
  -> ψ__in ⊢ e ▸ ⟨a⟩ τ ⤳ t ⊣ ψ__out.
Admitted.

(** based on dom lemmas *)
Corollary EInst_full_Sub_T : forall ψ__in ψ ψ__dec θ τ,
    {ψ__in, []} ⊢e ψ ⤳ {ψ__dec, θ}
  -> ψ ⊢wfτ τ
  -> full_Sub_T θ τ.
Admitted.

Corollary EInst_full_Sub_Tm : forall ψ__in ψ ψ__dec θ t,
    {ψ__in, []} ⊢e ψ ⤳ {ψ__dec, θ}
  -> ψ ⊢wft t
  -> full_Sub_Tm θ t.
Admitted.


#[export] Hint Unfold bindings_Sub_sub : rels.


