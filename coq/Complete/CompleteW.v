Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.
Require Import Preamble.Tag.
Require Import Defs.HdmLems.

Require Import LibHyps.LibHyps.

Require Import Defs.E.
Require Import Defs.Dec.Notation.
Require Import Defs.DecA.
Require Import Defs.EInst.
Require Import Defs.ERels.
Require Import Defs.FrA.
Require Import Defs.Inf.
Require Import Defs.Lc.
Require Import Defs.List.
Require Import Defs.OpenClose.
Require Import Defs.Shape.
Require Import Defs.SubSump.
Require Import Defs.Sub.
Require Import Defs.TmTy.

(* Require Import Complete.PrincipalTyping. *)
(* Require Import Complete.CompleteSS. *)
(* Require Import Complete.CompleteInst. *)
(* Require Import Complete.CompleteUnit. *)
(* Require Import Complete.CompleteLet. *)

Require Import Semantics.FundPropAdmit.
Require Import Semantics.EquivRel.

Require Import Complete.DecAWeaken.

Notation  "ψ1 ⊢ e ▸ ⟨ a ⟩ τ ⤳ t ⊣ ψ2" := (Inf ψ1 e a τ t ψ2) (at level 70, format "ψ1  ⊢  e  ▸  ⟨ a ⟩  τ  ⤳  t  ⊣  ψ2" ) : type_scope.

(* Lemma subst_skvar_Sc_SubSump : forall ψ σ τ τ' α, *)
(*     SubSump ψ σ τ *)
(*   -> α ∉ E_A_skvars ψ *)
(*   -> lc(τ') *)
(*   -> SubSump ψ ({τ' ≔ α}σ) ({τ' ≔ α}τ). *)
(* Proof. *)
(*   introv SS NIE LC. induction SS. simpl+. crush. *)
(*   simpl+. econstructor. eassumption. *)
(*   rewrite subst_skvar_Sc_open_Sc_wrt_T in IHSS. 2:assumption. *)
(*   applys_eq IHSS. fequals. subst_notin'. *)
(*   apply WfT_sk in WFT. fsetdec. fsetdec. *)
(* Qed. *)

(* Lemma wf_Sub_E_A_sk_sub : forall ψ1 ψ2 θ, *)
(*     ψ1 ⊢θ θ *)
(*   -> ψ1 ⊆ψα ψ2 *)
(*   -> ψ2 ⊢θ θ. *)
(* Admitted. *)


Definition subst_skvar_Sub (τ:T) (α:skvar) : Sub -> Sub :=
    map (fun p => ({τ ≔ α}(fst p), snd p)).

#[export] Instance substable_skvar_Sub  : substable Sub T skvar := { subst := subst_skvar_Sub }.

Fact subst_skvar_Sub_Sub_to_A : forall θ α τ,
    Sub_to_A ({τ ≔ α}θ) = Sub_to_A θ.
Proof. introv. ind_Sub θ; simpl+; crush. Qed.

(* Fact subst_skvar_Sub_dom_Sub : forall θ α τ, *)
(*     dom_Sub ({τ ≔ α}θ) ≡ dom_Sub θ. *)
(* Proof. introv. ind_Sub θ; simpl+; crush. Qed. *)

Lemma Sub_app_T_subst_skvar_T : forall τ α (θ:Sub) (τ':T),
    α ∉ dom_Sub θ
  -> fv__α(τ) ∐ dom_Sub θ
  -> {τ ≔ α}⟦θ ▹ τ'⟧ = ⟦({τ ≔ α}θ) ▹ {τ ≔ α} τ'⟧.
Proof.
  introv NID DISJ. ind_Sub θ. crush.
  dist. simpl+ in *. rewrite <- IHθ. 2:fsetdec. 2:disj_sub.
  rewrite subst_skvar_T_subst_skvar_T. reflexivity. 2:fsetdec.
  in_disj.
Qed.

(* Lemma Sub_app_SubSump : forall θ τ ψ, *)
(*     dom_Sub θ ∐ E_A_skvars ψ *)
(*   -> ψ ⊢θ θ *)
(*   -> SubSump ψ (∀ (Sub_to_A θ)⬪ S__T τ) ⟦θ ▹ τ⟧. *)
(* Proof. *)
(*   intro θ. ind_Sub θ; introv DISJ WFS. *)
(*   - simpl+. crush. *)
(*   - simpl+. simpl+ in DISJ. *)
(*     assert (ψ ⊢wfτ τ). eapply WFS. reldec. *)
(*     applys SS__L τ. eassumption. *)
(*     rewrite <- subst_skvar_Sc_spec. dist. *)
(*     eapply subst_skvar_Sc_SubSump. eapply IHθ. disj_sub. eauto. in_disj. eauto. *)
(* Qed. *)

(* Lemma Sub_app_SubSump' : forall a θ τ ψ, *)
(*     dom_Sub θ ∐ E_A_skvars (ψ ::a a) *)
(*   -> fv__α(τ) ∐ varl a *)
(*   -> ψ ::a a ⊢θ θ *)
(*   -> NoDup a *)
(*   -> SubSump' ψ (∀ (Sub_to_A θ)⬪ S__T τ) (∀ a ⬪ S__T ⟦θ ▹ τ⟧). *)
(* Proof. *)
(*   intro a. ind_a a; introv DISJ1 DISJ2 WFS ND. *)
(*   - simpl+. econstructor. eapply Sub_app_SubSump. *)
(*     simpl+ in DISJ1. eassumption. applys wf_Sub_E_A_sk_sub WFS. reldec. *)
(*   - simpl+ in *. applys SS'__R (dom_Sub θ ∪ varl a). introβ. *)
(*     rewrite <- subst_skvar_Sc_spec. *)
(*     rewrite subst_skvar_Sc_close_Sc_wrt_A. 2:crush. 2:inverts ND; eauto. 2:simpl+; fsetdec. *)
(*     simpl+. rewrite Sub_app_T_subst_skvar_T. 2:in_disj. 2:simpl+; fsetdec. *)
(*     subst_notin'. 2:in_disj. *)
(*     erewrite <- subst_skvar_Sub_Sub_to_A. eapply IHa. rewrite subst_skvar_Sub_dom_Sub. *)
(*     assert (dom_Sub θ ∐ {{β}}). symmetry. simpl+. fsetdec. *)
(*     forwards: atoms_facts.disj_union' DISJ1 H. clear - H0. disj_sub. disj_sub. admit. inverts ND. auto. *)
(* Admitted. *)

(* Require Import Semantics.EquivRel. *)
(* Lemma subst_skvar_Sc_SubSumpTm : forall ψ (σ:Sc) (τ τ':T) (α:skvar) (t1 t2:Tm), *)
(*     SubSumpTm ψ t1 σ t2 τ *)
(*   -> α ∉ E_A_skvars ψ *)
(*   -> lc(τ') *)
(*   -> SubSumpTm ψ ({τ' ≔ α}t1) ({τ' ≔ α}σ) ({τ' ≔ α}t2) ({τ' ≔ α}τ). *)
(* Admitted. *)

Definition Sub_TList_app (t:Tm) (θ:Sub) : Tm := fold_left (fun (t:Tm) (τ:T) => t__TApp t τ) (map fst θ) t.
Arguments Sub_TList_app _ _ : simpl never.

(* Fact Sub_TList_app_nil : forall t, *)
(*     Sub_TList_app t [] = t. *)
(* Proof. unfold Sub_TList_app. crush. Qed. *)
(* #[export] Hint Rewrite Sub_TList_app_nil : core. *)

Fact Sub_TList_app_cons : forall t τ α θ,
    Sub_TList_app t ((τ, α) :: θ) = Sub_TList_app (t__TApp t τ) θ.
Proof. unfold Sub_TList_app. crush. Qed.
#[export] Hint Rewrite Sub_TList_app_cons : core.

Fact subst_skvar_Tm_Sub_TList_app : forall θ τ α t,
    {τ ≔ α}(Sub_TList_app t θ) = Sub_TList_app ({τ ≔ α}t) ({τ ≔ α}θ).
Proof. intro θ. ind_Sub θ; intros; simpl+. crush. rewrite IHθ. crush. Qed.

Lemma Sub_app_SubSumpTm : forall θ t τ ψ,
    SubSumpTm ψ t (∀ (Sub_to_A θ)⬪ S__T τ) (Sub_TList_app t θ) ⟦θ ▹ τ⟧.
Proof.
  intro θ. ind_Sub θ; introv.
  - econstructor.
  - simpl+.
    applys SST__L τ. admit. dist.
    forwards: IHθ (t__TApp t0 τ) ({τ ≔ α}τ0) ψ. applys_eq H.
    + rewrite <- subst_skvar_Sc_spec. rewrite subst_skvar_Sc_close_Sc_wrt_A. crush.
      admit. admit. admit.
    + admit.
Admitted.

Lemma Sub_app_SubSumpTm' : forall t τ a θ ψ,
    SubSumpTm' ψ t (∀ (Sub_to_A θ)⬪ S__T τ) (Λ a ⬪ (Sub_TList_app t θ) ) (∀ a ⬪ S__T ⟦θ ▹ τ⟧).
Proof.
  intros t τ a. gen τ t. ind_a a; introv.
  - simpl+. econstructor. eapply Sub_app_SubSumpTm.
  - simpl+ in *.
    applys SST'__R empty. introβ.
    rewrite <- subst_skvar_Tm_spec.
    rewrite <- subst_skvar_Sc_spec.
    specializes IHa τ t0 ({T__Var_f β ≔ α}θ) (ψ ::a [β]).
    (* specializes IHa ({T__Var_f β ≔ α}t0). *)
    applys_eq IHa.
    + rewrite subst_skvar_Sub_Sub_to_A. crush.
    + rewrite subst_skvar_Tm_close_Tm_wrt_A. 2,3,4:admit. fequals.
      rewrite subst_skvar_Tm_Sub_TList_app. fequals.
      subst_notin'. admit.
    + rewrite subst_skvar_Sc_close_Sc_wrt_A. 2,3,4:admit. fequals.
      simpl+. fequals. rewrite Sub_app_T_subst_skvar_T. 2,3:admit. fequals.
      subst_notin'. admit.
Admitted.

Lemma Sub_app_Sc_close_Sc_wrt_T : forall θ σ α,
    lc(θ)
  -> α ∉ dom_Sub θ
  -> α ∉ skvars_codom_Sub θ
  -> ⟦θ ▹ close_Sc_wrt_T α σ⟧ = close_Sc_wrt_T α ⟦θ ▹ σ⟧.
Proof.
  introv LC NID NICD. ind_Sub θ. crush.
  dist. rewrite IHθ. 2:eauto. 2:crush. 2:crush. remember ⟦θ ▹ σ⟧ as σ'.
  eapply subst_skvar_Sc_close_Sc_wrt_T. eauto. fsetdec+. crush.
Qed.

Lemma Sub_app_Sc_close_Sc_wrt_A : forall θ σ a,
    lc(θ)
  -> varl a ∐ dom_Sub θ
  -> varl a ∐ skvars_codom_Sub θ
  -> ⟦θ ▹ ∀ a ⬪ σ⟧ = (∀ a ⬪ ⟦θ ▹ σ⟧).
Proof.
  introv LC NID NICD. ind_a a. crush.
  simpl+. fequals. rewrite <- IHa.
  2:clear - NID; disj_sub.
  2:clear - NICD; disj_sub.
  apply Sub_app_Sc_close_Sc_wrt_T. auto.
  in_disj.
  in_disj.
Qed.

Ltac cl_SSE_ :=
  match goal with
    | [ H : SameShape__E _ _ |- _ ] => clear H
    | [ H : SameShape__A _ _ |- _ ] => clear H
    | [ H : SameShape__σ _ _ |- _ ] => clear H
    | [ H : SameShape__τ _ _ |- _ ] => clear H
    | [ H : SameShape__t _ _ |- _ ] => clear H
  end.
Ltac cl_SSE := repeat cl_SSE_.

(* Axiom DecA_generalize_binding : forall σ1 ψ x σ2 e a τ t, *)
(*     ψ ::x x :- σ2 ⊢d' e ▸ ⟨a⟩ τ ⤳ t *)
(*   -> SubSump' ψ σ1 σ2 *)
(*   -> exists t', *)
(*       ψ ::x x :- σ1 ⊢d' e ▸ ⟨a⟩ τ ⤳ t *)
(*     /\ ψ ::x x :- σ1 ⊢t≈ t ≈ t' ▸ S__T τ. *)

(* (* Axiom DecA_generalize_binding' : forall σ1 ψ x σ2 e a τ t, *) *)
(* (*     ψ ::x x :- σ2 ⊢d' e ▸ ⟨a⟩ τ ⤳ t *) *)
(* (*   -> SubSump' ψ σ1 σ2 *) *)
(* (*   -> exists a' τ' t', *) *)
(* (*       ψ ::x x :- σ1 ⊢d' e ▸ ⟨a'⟩ τ' ⤳ t' *) *)
(* (*     /\ (∀ a'⬪ S__T τ') = (∀ a⬪ S__T τ) *) *)
(* (*     /\ ψ ::x x :- σ1 ⊢t≈ t ≈ t' ▸ S__T τ. *) *)
(* (*     /\ (Λ a'⬪ t') = (Λ a⬪ t). *) *)
(* About SubSumpTm'. *)


(* Lemma Inf_remove_obj : forall t__obj a__obj τ__obj t__obj' a__obj' τ__obj' ψ__in e a__alg τ__alg t__alg ψ__out, *)
(*     ψ__in ::o ⦇t__obj ▸ ⟨a__obj⟩ S__T τ__obj⦈ ⊢ e ▸ ⟨a__alg⟩ τ__alg ⤳ t__alg ⊣ ψ__out ::o ⦇t__obj' ▸ ⟨a__obj'⟩ S__T τ__obj'⦈ *)
(*   -> ψ__in ⊢ e ▸ ⟨a__alg⟩ τ__alg ⤳ t__alg ⊣ ψ__out. *)
(* Admitted. *)

Fact SameShapeA_nil : forall a,
    SameShape__A [] a
  -> a = [].
Proof. introv SSA. inverts SSA. destruct a; crush. Qed.

Ltac inv_SSASTt_ :=
  match goal with
    | [ H : SameShape__A ([]) _ |- _ ] => apply SameShapeA_nil in H
    | [ H : SameShape__σ (S__T _) _ |- _ ] => inverts H
    | [ H : SameShape__τ T__Unit _ |- _ ] => inverts H
    | [ H : SameShape__t t__Unit _ |- _ ] => inverts H
  end.
Ltac inv_SSASTt := repeat (inv_SSASTt_; subst).

(* Ltac inv_SSE' := inv_SSE; inv_SSASTt. *)

(* Lemma EquivRel_symm : forall ψ t1 t2 σ, *)
(*     ψ ⊢t≈ t1 ≈ t2 ▸ σ *)
(*   -> ψ ⊢t≈ t2 ≈ t1 ▸ σ. *)
(* Admitted. *)

Lemma EquivRel_trans : forall ψ t1 t2 t3 σ,
    ψ ⊢t≈ t1 ≈ t2 ▸ σ
  -> ψ ⊢t≈ t2 ≈ t3 ▸ σ
  -> ψ ⊢t≈ t1 ≈ t3 ▸ σ.
Admitted.

(* (* Lemma EquivRel_open : forall, *) *)
(* (*     ψ__d ⊢t≈ t1 ≈ t1' ▸ σ1 *) *)
(* (*   -> ψ__d ⊢t≈ t2 ≈ t2' ▸ σ1 *) *)
(* (* Lemma close_Tm_wrt_T_open_Tm_wrt_Tm : forall t1, *) *)
(* (*     lc(t1) *) *)
(* (*   -> forall α t2, *) *)
(* (*       lc(t2) *) *)
(* (*     -> close_Tm_wrt_T α (open_Tm_wrt_Tm t1 t2) = open_Tm_wrt_Tm (close_Tm_wrt_T α t1) (close_Tm_wrt_T α t2). *) *)
(* (* Proof. *) *)
(* (*   introv LC1. unfold open_Tm_wrt_Tm. generalize 0. unfold close_Tm_wrt_T. generalize 0. *) *)
(* (*   induction LC1; intros; simpl+. *) *)
(* (*   1,2,3,4,5,6:crush. *) *)
(* (*   - admit. *) *)
(* (*   - admit. *) *)
(* (* Abort. *) *)

(* (* Lemma close_Tm_wrt_T_open_Tm_wrt_Tm : forall t1 t2 α, *) *)
(* (*     close_Tm_wrt_T α (open_Tm_wrt_Tm t1 t2) = open_Tm_wrt_Tm (close_Tm_wrt_T α t1) (close_Tm_wrt_T α t2). *) *)
(* (* Proof. *) *)
(* (*   intro t1. unfold open_Tm_wrt_Tm. generalize 0. unfold close_Tm_wrt_T. generalize 0. *) *)
(* (*   induction t1; intros; simpl+. *) *)
(* (*   2,3,4,5,6,7,8:crush. *) *)
(* (*   - admit. *) *)
(* (*   - fequals. *) *)
(* (*     erewrite IHt1. *) *)
(* (* Abort. *) *)

(* (* Lemma close_Tm_wrt_T_open_Tm_wrt_Tm' : forall α t1 t2, *) *)
(* (*     t__TLam (close_Tm_wrt_T α (open_Tm_wrt_Tm t1 t2)) = open_Tm_wrt_Tm (t__TLam (close_Tm_wrt_T α t1)) (close_Tm_wrt_T α t2). *) *)
(* (* Proof. intros. unfold open_Tm_wrt_Tm. simpl+. fequals. eapply close_Tm_wrt_T_open_Tm_wrt_Tm. Qed. *) *)

Fact open_Tm_wrt_Tm_TLam : forall t1 t2,
    open_Tm_wrt_Tm (t__TLam t1) t2 = t__TLam (open_Tm_wrt_Tm t1 t2).
Proof. unfold open_Tm_wrt_Tm. intros. crush. Qed.
#[export] Hint Rewrite open_Tm_wrt_Tm_TLam : core.



(* Lemma close_Tm_wrt_T_open_Tm_wrt_Tm_rec : forall t1 t2 α n m, *)
(*     degree_Tm_wrt_T n t1 *)
(*   -> degree_Tm_wrt_Tm m t1 *)
(*   -> close_Tm_wrt_T_rec n α (open_Tm_wrt_Tm_rec m t2 t1) = open_Tm_wrt_Tm_rec m t2 (close_Tm_wrt_T_rec n α t1). *)
(* Proof. *)
(*   intro t1. *)
(*   induction t1; introv DEG1 DEG2; intros; simpl+. *)
(*   2,3,4,5:crush. *)
(*   - lt_eq_dec. 1,3:crush. *)
(*     inverts DEG2. crush. *)
(*   - inverts DEG1. inverts DEG2. crush. *)
(*   - inverts DEG1. inverts DEG2. crush. *)
(*   - inverts DEG1. inverts DEG2. crush. *)
(*   - inverts DEG1. inverts DEG2. crush. *)
(* Qed. *)

Lemma close_Tm_wrt_T_open_Tm_wrt_Tm : forall t1 t2 α,
    α ∉ fv__α(t2)
  -> lc(t2)
  -> close_Tm_wrt_T α (open_Tm_wrt_Tm t1 t2) = open_Tm_wrt_Tm (close_Tm_wrt_T α t1) t2.
Proof.
  intros. unfold close_Tm_wrt_T. generalize 0. unfold open_Tm_wrt_Tm. generalize 0.
  induction t1; intros.
  - simpl+. lt_eq_dec; crush.
  - crush.
  - crush.
  - crush.
  - crush.
  - crush.
  - crush.
  - crush.
  - simpl+. fequals.
Qed.

Lemma close_Tm_wrt_A_open_Tm_wrt_Tm : forall a t1 t2,
    lc(t2)
  -> varl a ∐ fv__α(t2)
  -> Λ a⬪ (open_Tm_wrt_Tm t1 t2) = open_Tm_wrt_Tm (Λ a⬪ t1) t2.
Proof.
  intros. ind_a a. crush.
  simpl+ in *. fequals. rewrite IHa. 2:disj_sub.
  eapply close_Tm_wrt_T_open_Tm_wrt_Tm. in_disj. assumption.
Qed.

Lemma complete_generalize_let : forall t1 σ1 t2 σ2 t__o1' a__o1' σ__o1' t__o2 a__o2 σ__o2 ψ x t__o1 a__o1 σ__o1 e a τ t,
    (ψ ::x x :- σ2) ::o ⦇t__o1 ▸ ⟨a__o1⟩ σ__o1⦈ ⊢d' open_Ex_wrt_Ex e (e__Var_f x) ▸ ⟨a⟩ τ ⤳ open_Tm_wrt_Tm t (t__Var_f x)
  -> SubSumpTm' ψ t1 σ1 t2 σ2
  (* -> ψ ⊢t t2  ▸ σ2 *)
  (* -> ψ ⊢t t1 ▸ σ1 *)
  -> exists a' τ' t',
      (ψ ::x x :- σ1) ::o ⦇t__o1' ▸ ⟨a__o1'⟩ σ__o1'⦈ ::o ⦇t__o2 ▸ ⟨a__o2⟩ σ__o2⦈ ⊢d' open_Ex_wrt_Ex e (e__Var_f x) ▸ ⟨a'⟩ τ' ⤳ open_Tm_wrt_Tm t' (t__Var_f x)
    /\ (∀ a'⬪ S__T τ') = (∀ a⬪ S__T τ)
    /\ ψ ⊢t≈ (Λ a'⬪ (open_Tm_wrt_Tm t' t1)) ≈ (Λ a⬪ (open_Tm_wrt_Tm t t2)) ▸ (∀ a⬪ S__T τ).
Admitted.

Lemma CompatOpen : forall ψ t1 t1' t2 t2' σ1 σ2 x,
    ψ ⊢t≈ t1 ≈ t1' ▸ σ1
  -> ψ ::x x :- σ1 ⊢t≈ (open_Tm_wrt_Tm t2 (t__Var_f x)) ≈ (open_Tm_wrt_Tm t2 (t__Var_f x)) ▸ σ2
  -> ψ ⊢t≈ (open_Tm_wrt_Tm t2 t1) ≈ (open_Tm_wrt_Tm t2' t1') ▸ σ2.
Admitted.

Lemma CompatOpen' : forall t1 t1' t2 t2' t2'' σ1 σ2 ψ,
    ψ ⊢t≈ open_Tm_wrt_Tm t1 t2 ≈ open_Tm_wrt_Tm t1' t2' ▸ σ1
  -> ψ ⊢t≈ t2' ≈ t2'' ▸ σ2
  -> ψ ⊢t≈ open_Tm_wrt_Tm t1 t2 ≈ open_Tm_wrt_Tm t1' t2'' ▸ σ1.
Admitted.

Lemma complete_generalize_let_eq : forall t1 σ1 t2 σ2 t2' t__o1' a__o1' σ__o1' t__o2 a__o2 σ__o2 ψ x t__o1 a__o1 σ__o1 e a τ t,
    (ψ ::x x :- σ2) ::o ⦇t__o1 ▸ ⟨a__o1⟩ σ__o1⦈ ⊢d' open_Ex_wrt_Ex e (e__Var_f x) ▸ ⟨a⟩ τ ⤳ open_Tm_wrt_Tm t (t__Var_f x)
  -> SubSumpTm' ψ t1 σ1 t2' σ2
  -> ψ ⊢t≈ t2' ≈ t2 ▸ σ2
  -> lc(t2)
  -> varl a ∐ fv__α(t2)
  -> lc(t2')
  -> varl a ∐ fv__α(t2')
  -> exists a' τ' t',
      (ψ ::x x :- σ1) ::o ⦇t__o1' ▸ ⟨a__o1'⟩ σ__o1'⦈ ::o ⦇t__o2 ▸ ⟨a__o2⟩ σ__o2⦈ ⊢d' open_Ex_wrt_Ex e (e__Var_f x) ▸ ⟨a'⟩ τ' ⤳ open_Tm_wrt_Tm t' (t__Var_f x)
    /\ (∀ a'⬪ S__T τ') = (∀ a⬪ S__T τ)
    /\ ψ ⊢t≈ (Λ a'⬪ (open_Tm_wrt_Tm t' t1)) ≈ (Λ a⬪ (open_Tm_wrt_Tm t t2)) ▸ (∀ a⬪ S__T τ).
Proof.
  intros.
  forwards [a' [τ' [t' ?]]]: complete_generalize_let. eassumption. eassumption. destr.
  exists a' τ' t'. splits. eassumption. crush.
  eapply EquivRel_trans. eassumption.
  rewrite close_Tm_wrt_A_open_Tm_wrt_Tm. 2,3:crush.
  rewrite close_Tm_wrt_A_open_Tm_wrt_Tm. 2,3:crush.
  eapply CompatOpen'. 2:eassumption.
  eapply FundamentalProperty.
  rewrite <- close_Tm_wrt_A_open_Tm_wrt_Tm. 2,3:crush. crush.
Qed.

(* Lemma subst_skvar_Tm__forall : forall a t t' τ α, *)
(*     {τ ≔ α}t = (Λ a ⬪ t') *)
(*   -> exists t'', *)
(*       t = Λ a ⬪ t''. *)
(* Proof. *)
(*   intro a. ind_a a; intros. admit. *)
(*   simpl+ in H. destruct t0; simpl+ in H; inverts H. *)
(*   (** Discuss with Tom *) *)
(* Abort. *)

(* Lemma Sub_app_Tm_forall : forall a θ t t', *)
(*     ⟦θ ▹ t⟧ = (Λ a ⬪ t') *)
(*   -> exists t'', *)
(*       t = Λ a ⬪ t''. *)
(* Proof. *)
(*   intros. ind_Sub θ. simpl+ in H. exists t'. crush. *)
(*   simpl+ in H. *)
(* Abort. *)

(* Lemma Sub_app_Tm_forall : forall a θ1 θ2 t t', *)
(*     ⟦θ1 ▹ t⟧ = ⟦θ2 ▹ Λ a ⬪ t'⟧ *)
(*   -> exists t'', *)
(*       t = Λ a ⬪ t''. *)
(* Proof. *)
(*   intro. ind_a a; intros. *)
(*   - exists t0. simpl+. reflexivity. *)
(*   - destruct t0; simpl+ in H; inverts H. *)
(*     forwards: IHa θ1 θ2 (close_Tm_wrt_T α t0) t'. *)
(*     applys open_Tm_wrt_T_inj α. *)
(* Admitted. *)

Lemma EInst_dom_Sub : forall ψ__in θ__in ψ ψ' θ,
    {ψ__in, θ__in} ⊢e ψ ⤳ {ψ', θ}
  -> dom_Sub θ ≡ E_A_skvars ψ.
Proof.
  introv EINST. induction EINST. crush.
  - simpl+. rewrite IHEINST.
    forwards: AInst_Sub_to_A. eassumption. subst.
    rewrite varl_Sub_to_A_dom. crush.
  - simpl+. crush.
  - simpl+. crush.
Qed.

Corollary EInst_dom_Sub' : forall ψ__in θ__in ψ ψ' θ,
    {ψ__in, θ__in} ⊢e ψ ⤳ {ψ', θ}
  -> dom_Sub θ ⊆ E_skvars ψ.
Proof. intros. forwards: EInst_dom_Sub. eassumption. rewrite <- E_A_skvars_E_skvars. crush. Qed.

Require Import Defs.WfE.
Require Import Defs.Inf.

Fact dec_L_union : forall L1 L2,
    dec_L L1
  -> dec_L L2
  -> dec_L (L1 ∪ L2).
Proof. intros. unfolds. intros. destr_union; eauto. Qed.

(* Lemma AInst_codom_skvar_Sub_dec : forall ψ a θ, *)
(*     ψ ⊢a a ⤳ θ *)
(*   -> dec_E ψ *)
(*   -> dec_L (skvars_codom_Sub θ). *)
(* Proof. *)
(*   introv AINST DEC. induction AINST. crush. *)
(*   simpl+. eapply dec_L_union. 2:eauto. erewrite WfT_sk. 2:eassumption. *)
(*   rewrite E_A_skvars_E_skvars. crush. *)
(* Qed. *)

Lemma EInst_skvars_codom_Sub : forall ψ__in θ__in ψ ψ' θ,
    {ψ__in, θ__in} ⊢e ψ ⤳ {ψ', θ}
  -> (skvars_codom_Sub θ) ⊆ E_skvars (ψ__in +++ ψ').
Proof. intros. rewrite Sub_wf_codom. rewrite E_A_skvars_E_skvars. reflexivity. eauto. Qed.
Lemma EInst_skvars_codom_Sub' : forall ψ ψ' θ,
    {•, []} ⊢e ψ ⤳ {ψ', θ}
  -> (skvars_codom_Sub θ) ⊆ E_skvars (ψ').
Proof. intros. eapply EInst_skvars_codom_Sub in H. simpl+ in H. eassumption. Qed.

Lemma Sub_wf_dec : forall ψ θ,
    ψ ⊢θ θ
  -> dec_E ψ
  -> dec_L (skvars_codom_Sub θ).
Proof. intros. rewrite Sub_wf_codom. rewrite E_A_skvars_E_skvars. eassumption. eassumption. Qed.

Lemma fsk_Sc_close_Sc_wrt_A' : forall a σ,
    fv__α(∀ a ⬪ σ) ⊆ fv__α(σ).
Proof. intros. rewrite fsk_Sc_close_Sc_wrt_A. fsetdec. Qed.

(* Lemma EInst_codom_skvar_Sub_dec : forall ψ__in θ__in ψ ψ' θ, *)
(*     {ψ__in, θ__in} ⊢e ψ ⤳ {ψ', θ} *)
(*   -> dec_E ψ__in *)
(*   -> dec_L (skvars_codom_Sub θ__in) *)
(*   -> dec_E ψ' *)
(*   -> dec_L (skvars_codom_Sub θ). *)
(* Proof. *)
(*   introv EINST DEC1 DEC2. induction EINST; simpl+ in *. *)
(*   - crush. *)
(*   - specializes IHEINST. eassumption. eassumption. destruct IHEINST. *)
(*     split. *)
(*     + unfolds. simpl+. *)
(*       eapply dec_L_union; eassumption. *)
(*     + eapply dec_L_union. eapply AInst_codom_skvar_Sub_dec. eassumption. *)
(*       unfolds. simpl+. eapply dec_L_union. eassumption. *)
(*       eapply dec_L_union. eassumption. eassumption. eassumption. *)
(*   - specializes IHEINST. eassumption. eassumption. destr. *)
(*     split. *)
(*     + unfolds. simpl+. eapply dec_L_union. eassumption. *)
(*   - *)
(*     split *)

(* Lemma TmTy_close : forall ψ a t τ, *)
(*     ψ ::a a ⊢t t ▸ S__T τ *)
(*   -> ψ ⊢t Λ a ⬪ t ▸ (∀ a ⬪ S__T τ). *)

Require Import Defs.Rename.
Corollary DecA_add_A : forall ψ a1 e a2 τ t2,
    ψ ⊢d' e ▸ ⟨a2⟩ τ ⤳ t2
  -> exists a2' τ' t2',
    ψ ::a a1 ⊢d' e ▸ ⟨a2'⟩ τ' ⤳ t2'
    /\ (∀ a2'⬪ S__T τ') = (∀ a2⬪ S__T τ)
    /\ (Λ a2'⬪ t2') = (Λ a2⬪ t2).
Proof.
  introv DEC.
  forwards [θ [?EQ [?EQ DEC']]]: DecA_weaken' (fv__α(S__T τ) ∪ fv__α(t2)) (ψ ::a a1). eassumption. reldec. reldec.
  forwards: Rename_gen_T θ (S__T τ). subst. simpl+. FrA_L_sub.
  forwards: Rename_gen_Tm θ t2. subst. simpl+. FrA_L_sub.
  exists. splits. eassumption. crush. crush.
Qed.


Lemma EInst_lookup_complete : forall ψ__a ψ__d θ σ__d x,
    {•, []} ⊢e ψ__a ⤳ {ψ__d, θ}
  -> E_lookup ψ__d x = Some σ__d
  -> wf(ψ__a)
  -> exists σ__a, E_lookup ψ__a x = Some σ__a
        /\ ⟦θ ▹ σ__a⟧ = σ__d.
Proof.
  introv EINST LU WF. induction EINST; simpl+ in LU.
  - inverts LU.
  - specializes IHEINST. eassumption. eauto.
    destr. exists σ__a. split. simpl+. eassumption.
    dist. admit.
  - if_dec.
    + inverts LU. exists. split. simpl+. if_taut. reflexivity.
      dist. admit.
    + specializes IHEINST. eauto. eauto.
      destr. exists. simpl+. if_taut. split. eassumption. reflexivity.
  - specializes IHEINST. eassumption. eauto.
    destr. exists. split. simpl+. eassumption. reflexivity.
Admitted.

Require Import Defs.Foralls.

Fact close_Tm_wrt_A_app : forall a1 a2 t,
    (Λ (a1 ++ a2) ⬪ t) = (Λ a1 ⬪ (Λ a2 ⬪ t)).
Proof. intros. induction a1; crush. Qed.

Fact close_Sc_wrt_A_app : forall a1 a2 τ,
    (∀ (a1 ++ a2) ⬪ τ) = (∀ a1 ⬪ (∀ a2 ⬪ τ)).
Proof. intros. induction a1; crush. Qed.

Lemma Var_complete : forall σ__a t__ain ψ__d t__din θ t__dout a__d τ__d L,
    SubSumpTmA ψ__d t__din ⟦θ ▹ σ__a⟧ t__dout a__d τ__d
  -> ψ__d ⊢t≈ ⟦θ ▹ t__ain⟧ ≈ t__din ▸ ⟦θ ▹ σ__a⟧
  -> exists a t__aout τ__a (θ__a:Sub),
      Inst t__ain σ__a t__aout a τ__a L
    /\ (ψ__d ::a a__d) ⊢a a ⤳ θ__a
    /\ ⟦θ__a ++ θ ▹ τ__a⟧ = τ__d
    /\ ψ__d ⊢t≈ (Λ a__d ⬪ ⟦θ__a ++ θ ▹ t__aout⟧) ≈ (Λ a__d ⬪ t__dout) ▸ ∀ a__d ⬪ (S__T ⟦θ__a ++ θ ▹ τ__a⟧).
Proof.
  intro. forall_ind σ__a.
  - introv SS EQ__t. inverts SS.
    exists ([]:A) t__ain τ ([]:Sub). splits; auto. simpl+. admit.
  - introv SS EQ__t. inverts SS.

    freshalgα (L ∪ dom_Sub θ ∪ fv__α(⟦θ ▹ σ__Forall⟧) ∪ fv__α(⟦θ ▹ t__ain⟧) ∪ varl a2).

    assert (⟦(τ1, α) :: θ ▹ T__Var_f α⟧ = τ1).
      dist. Sub_notin'. simpl+. if_taut. simpl+. fsetdec.

    specializes IHn (open_Sc_wrt_T σ__Forall (T__Var_f α)).
      specializes IHn (t__TApp t__ain (T__Var_f α)) ((τ1, α) :: θ).
      simpl+. crush. specializes IHn. applys_eq SS0.
      dist. admit.
      simpl+. rewrite Sub_app_Sc_open_Sc_wrt_T. 2:admit.
      applys_eq CompatTApp. rewrite H. fequals.
      subst_notin'. dist. subst_notin'. applys_eq EQ__t. admit.
      fsetdec. fsetdec.
      rewrite H. eassumption.
    destr.

    exists. splits.
    + applys InstP α. fsetdec. assumption. eassumption.
    + econstructor. eapply AInst_E_sk_sub. eassumption. reldec.
      wfdec.
    + admit.
    + do 2 rewrite close_Tm_wrt_A_app. rewrite close_Sc_wrt_A_app.
      eapply CompatTLamA. applys_eq H4.
      fequals. fequals. dist. admit.
      fequals. fequals. dist. admit.
      eapply FrA_L_sub. eassumption.
      z






      admit.
Admitted.


Theorem Inf_complete_open : forall e ψ__in ψ__d a__d τ__d t__d,
    ψ__d ⊢d' e ▸ ⟨a__d⟩ τ__d ⤳ t__d
  -> ψ__in ⤳' ψ__d
  -> wf(ψ__in)
  -> alg_E ψ__in
  -> dec_E ψ__d
  -> exists a__d' τ__d' t__d' a__a τ__a t__a ψ__out,
      (∀ a__d' ⬪ S__T τ__d') = (∀ a__d ⬪ S__T τ__d)
    /\ ψ__in ⊢ e ▸ ⟨a__a⟩ τ__a ⤳ t__a ⊣ ψ__out
    /\ ψ__out ::o ⦇t__a ▸ ⟨a__a⟩ S__T τ__a⦈ ⤳' ψ__d ::o ⦇t__d' ▸ ⟨a__d'⟩ S__T τ__d'⦈
    /\ ψ__d ⊢t≈ (Λ a__d' ⬪ t__d') ≈ (Λ a__d ⬪ t__d) ▸ (∀ a__d ⬪ S__T τ__d).
Proof.
  introv DEC. forwards E: DecA_lc DEC. gen ψ__in ψ__d a__d τ__d t__d. induction E.
  all: introv DECA [θ INST] WF__in ALG__in DEC__in; inverts DECA.

  (** Var *)
  - forwards [σ__a [IN' SA]]: EInst_lookup_complete. eassumption. eassumption. eassumption.
    subst.
    forwards [a [t [τ [θ__a [INS [AINST [EQ__T EQ__t]]]]]]]: Var_complete (t__Var_f x) (E_skvars ψ__in). eassumption.
    admit.

    exists a__d ⟦θ__a ++ θ ▹ τ⟧ ⟦θ__a ++ θ ▹ t⟧. exists a τ t ψ__in. splits.
    + crush.
    + econstructor. eassumption. eassumption.
    + exists.
      applys_eq EInst__O.
      2:eassumption.
      2:eapply SubSumpTmA_FrA; eassumption.
      2:simpl+; eassumption.
      simpl+. crush.
    + crush.

  (** Unit *)
  - exists. splits. reflexivity. eauto.
    exists. applys_eq EInst__O. fequals. simpl+. reflexivity. eassumption. eassumption. auto.
    simpl+. eapply FundamentalProperty. eapply TmTy_close_Tm_wrt_A. auto. auto.

  (** App *)
  - rename a1 into a__d1. rename a2 into a__d2.
    rename τ1 into τ__d1. rename τ__d into τ__d2.
    rename t1 into t__d1. rename t2 into t__d2.

    specializes IHE1. eassumption. exists. eassumption. eassumption. eassumption. eassumption.
    destruct IHE1 as [a__d1' [τ__d1' [t__d1' [a1 [τ1 [t1 [ψ1 [EQ__T1 [INF__e1 [INST1 EQ__t1]]]]]]]]]].
    inv_EInst'. onAllHyps move_up_types.

    assert (EINST1: {•, []} ⊢e ψ1 ::a [] ::o ⦇t1 ▸ ⟨a1⟩ S__T τ1⦈ ⤳ {ψ__d ::a a__d1 ::o ⦇⟦θ3 ++ θ0 ▹ t1⟧ ▸ ⟨a__d1'⟩ S__T ⟦θ3 ++ θ0 ▹ τ1⟧⦈, θ0}).
    applys_eq EInst__O. simpl+. fequals.
    applys_eq EInst__A. instantiate (2 := []). simpl+. reflexivity.
    eassumption. eauto using DecA_FrA. auto. admit. applys AInst_E_sk_sub AINST. reldec.

    forwards [a__d' [τ__d1' [t__d2' [DEC2' [EQ__T EQ__t]]]]]: DecA_add_obj DEC2.

    specializes IHE2. 2:exists; applys EINST1. eassumption. admit. admit. admit.
    destruct IHE2 as [a__d2'' [τ__d2'' [t__d2'' [a2 [τ2 [t2 [ψ__out [EQT' [INF__e2 [INST__out EQ__t']]]]]]]]]].
      forwards: Inf_SameShape INF__e2. inv_SSE. inv_SSASTt. cl_SSE.
      inv_EInst'. onAllHyps move_up_types.
      rename ψ3 into ψ__out.

    exists. splits.
    + admit.
    + econstructor. eassumption. applys_eq INF__e2. admit.
      admit. admit. admit.
    + admit.
    + admit.

  - rename a1 into a__d1. rename a2 into a__d2.
    rename τ1 into τ__d1. rename τ2 into τ__d2.
    rename H0 into IH.

    freshx L. specializes DEC x. specializes DEC. fsetdec.
    freshalgα (E_skvars ψ__in ∪ dom_Sub θ).
    assert (SA__α1: ⟦ θ ▹ T__Var_f α⟧ = T__Var_f α).
      Sub_notin'. simpl+. fsetdec.
    assert (SA__α2: ⟦(τ__d1, α) :: θ ▹ T__Var_f α⟧ = τ__d1).
      dist. rewrite SA__α1. simpl+. if_taut.

    assert (EINST: {•, []} ⊢e ψ__in ::a [α] ::x x :- S__T (T__Var_f α) ⤳ {ψ__d ::a a__d1 ::x x :- S__T τ__d1, ((τ__d1, α) :: θ)}).
      applys_eq EInst__S. simpl+. fequals. fequals. crush.
      applys_eq EInst__A. instantiate (2 := [(τ__d1, α)]). simpl+. reflexivity.
      assumption. eassumption. simpl+. econstructor. auto. assumption.

    specializes IH. eassumption. exists. eassumption. admit. admit. admit.
    destruct IH as [a__d2' [τ__d2' [t__d' [a [τ [t [ψ__out [EQ__T [INF [INST' EQ__t]]]]]]]]]].
      forwards: Inf_SameShape INF. inv_SSE. inv_SSASTt. cl_SSE.
      inv_EInst'. onAllHyps move_up_types.
      remember ⟦θ2 ▹ T__Var_f α⟧ as τ__d1.
      rename ψ0 into ψ__out.

    exists (a__d2' ++ a__d1) (T__Fun ⟦θ5 ++ θ6 ++ θ7 ▹ τ2⟧ ⟦θ5 ++ θ6 ++ θ7 ▹ τ⟧) (t__Lam ⟦θ5 ++ θ6 ++ θ7 ▹ τ2⟧ ⟦θ5 ++ θ6 ++ θ7 ▹ close_Tm_wrt_Tm x t⟧).
    exists (a ++ a2) (T__Fun τ2 τ) (t__Lam τ2 (close_Tm_wrt_Tm x t)) ψ__out. splits.
    + simpl+. admit.
    + applys Inf__Abs α. fsetdec. assumption.
      introy. asserts_rewrite (y = x). admit.
      applys_eq INF. rewrite open_Tm_wrt_Tm_close_Tm_wrt_Tm. reflexivity.
    + exists. applys_eq EInst__O. 2:eassumption. simpl+. fequals. fequals.
      rewrite app_assoc. fequals. simpl+. reflexivity. simpl+. reflexivity.
      eapply FrA_app. eassumption. eassumption.
      reldec. eapply AInst_merge; eapply AInst_E_sk_sub; try eassumption; reldec.
    + admit.

  - clear E H. rename IHE into IH__e1. rename H0 into IH__e2. rename DEC1 into DEC__e1. rename DEC2 into DEC__e2.
    rename τ1 into τ__d1. rename τ__d into τ__d2. rename t1 into t__d1. rename t2 into t__d2.
    rename a1 into a__d1. rename a__d into a__d2. rename INST into INST__in.

    (** IH1 *)
    specializes IH__e1. eassumption. exists. eassumption. eassumption. eassumption. eassumption.
      destruct IH__e1 as [a__d1' [τ__d1' [t__d1' [a1 [τ1 [t1 [ψ1 [EQ__T1 [INF__e1 [INST1 EQ__t1]]]]]]]]]].
      (* remember t__d1'. remember τ__d1'. remember t__d1. *)
      clear INST__in. inv_EInst'. rename θ0 into θ__ψ1. onAllHyps move_up_types.

    forwards WF1: Inf_Wf. 1,2:eassumption.

    freshx L. specializes DEC__e2 x. specializes DEC__e2. fsetdec.

    (** Instantiating the desired input env for e2 *)
    assert (EINST': {•, []} ⊢e ψ1 ::x x :- close_Sc_wrt_A (S__T τ1) a1
          ⤳ {ψ__d ::x x :- ⟦θ__ψ1 ▹ close_Sc_wrt_A (S__T τ1) a1⟧, θ__ψ1}).
      applys_eq EInst__S. fequals. simpl+. fequals. eassumption.
    forwards DEC__e2': (complete_generalize_let_eq ⟦θ__ψ1 ▹ Λ a1 ⬪ t1⟧ ⟦θ__ψ1 ▹ ∀ a1 ⬪ S__T τ1⟧ (Λ a__d1 ⬪ t__d1) (∀ a__d1 ⬪ S__T τ__d1)) DEC__e2.
      forwards SS: Sub_app_SubSumpTm' ⟦θ__ψ1 ▹ Λ a1 ⬪ t1⟧ ⟦θ__ψ1 ▹ τ1⟧ a__d1' θ3 ψ__d.
      applys_eq SS. forwards: AInst_Sub_to_A AINST. subst.
      rewrite Sub_app_Sc_close_Sc_wrt_A. reflexivity. eauto. eapply FrA_props2.
      inverts WF1. applys FrA_L_sub FR0. eapply EInst_dom_Sub'. eassumption.
      eapply L_alg_dec_disj. eapply alg_L_subset. applys Inf_alg INF__e1. eassumption.
      rewrite varl_Sub_to_A_dom. reldec. eapply Sub_wf_dec. eauto.
      unfolds. eapply dec_L_subset. eassumption. simpl+.
      (** something about full subs here *)
      rewrite Sub_app_Sc_fsk'. rewrite EInst_skvars_codom_Sub'. 2:eapply EINST.
      rewrite fsk_Sc_close_Sc_wrt_A'. simpl+.
      (** doesn't work since τ1 is alg *)

      admit.
      dist. dist in EQ__T1. crush.
      admit. admit. admit. admit. admit.
      destruct DEC__e2' as [a__d2' [τ__d2' [t__d2' [DEC__e2' [EQ__T2 EQ__t2]]]]].

    assert (EINST'': {•, []} ⊢e (ψ1 ::x x :- (∀ a1 ⬪ S__T τ1) ::o ⦇Λ a1 ⬪ t1 ▸ ⟨[]⟩ S__T T__Unit⦈
                                  ::o ⦇t__Unit ▸ ⟨a1⟩ S__T T__Unit⦈)
                      ⤳ {ψ__d ::x x :- ⟦θ__ψ1 ▹ ∀ a1 ⬪ S__T τ1⟧ ::o ⦇⟦θ__ψ1 ▹ Λ a1 ⬪ t1⟧ ▸ ⟨[]⟩ S__T T__Unit⦈
                            ::o ⦇t__Unit ▸ ⟨a__d1'⟩ S__T T__Unit⦈, θ__ψ1}).
      applys_eq EInst__O. 2:applys_eq EInst__O. 2:eassumption. 2:apply FrA_nil. 2:auto.
      2:applys FrA_L_sub FR; admit.
      2:applys AInst_E_sk_sub AINST; reldec.
      simpl+. crush.

    (** IH2 with objects *)
    specializes IH__e2 x. specializes IH__e2. eassumption. exists. eassumption. admit. admit. admit.
      destruct IH__e2 as [a__d2'' [τ__d2'' [t__d2'' [a2 [τ2 [t2 [ψ__out' [EQ__T2' [INF__e2 [INST__out EQ__t2']]]]]]]]]].
      forwards: Inf_SameShape INF__e2. inv_SSE. inv_SSASTt. cl_SSE.
      rename σ3 into σ__out. rename t4 into t1''. rename a3 into a__out. rename ψ2 into ψ__out.
      inv_EInst'. onAllHyps move_up_types. clear H12 H17.
      assert (Sub_app_Tm_forall : forall θ1 θ2 t t' a, ⟦θ1 ▹ t⟧ = ⟦θ2 ▹ Λ a ⬪ t'⟧ -> exists t'', t = Λ a ⬪ t''). admit.
      forwards [t1' ?EQ]: Sub_app_Tm_forall H9. subst.
      rename θ0 into θ__ψ2.
      remember (⟦θ2 ++ θ__ψ2 ▹ τ2⟧) as τ__d2''.
      remember (⟦θ2 ++ θ__ψ2 ▹ close_Tm_wrt_Tm x t2⟧) as t__d2''.

    exists a__d2'' τ__d2'' (open_Tm_wrt_Tm t__d2'' ⟦θ2 ++ θ__ψ2 ▹ Λ a1 ⬪ t1'⟧).
    exists a2 τ2 (open_Tm_wrt_Tm (close_Tm_wrt_Tm x t2) (Λ a1 ⬪ t1')) ψ__out.
    splits.
    + subst. etransitivity. eassumption. eassumption.
    + econstructor. eassumption.
      introy. asserts_rewrite (y = x). admit.
      applys_eq INF__e2. rewrite open_Tm_wrt_Tm_close_Tm_wrt_Tm. reflexivity.
    + exists. applys_eq EInst__O. 2:eassumption.
      2:applys FrA_L_sub FR0; reldec.
      2:applys AInst_E_sk_sub AINST0; reldec.
      simpl+. fequals.
    + eapply EquivRel_trans. 2:eassumption.
      rewrite close_Tm_wrt_A_open_Tm_wrt_Tm. 2,3:admit.
      rewrite close_Tm_wrt_A_open_Tm_wrt_Tm. 2,3:admit.
      applys CompatOpen ⟦θ__ψ1 ▹ ∀ a1 ⬪ S__T τ1⟧ x.
      * rewrite <- H9. applys_eq FundamentalProperty. admit. admit.
      * applys_eq EQ__t2'. admit. crush. subst. admit. admit.
Admitted.


Theorem Dec_DecA : forall e ψ a τ t,
    ψ ::a a ⊢d e ▸ τ ⤳ t
  -> exists t', ψ ⊢d' e ▸ ⟨a⟩ τ ⤳ t'
        /\ ψ ⊢t≈ t ≈ t' ▸ S__T τ.
Admitted.
