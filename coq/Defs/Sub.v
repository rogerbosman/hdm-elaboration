Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.
Require Import Preamble.Tag.
Require Import Defs.HdmLems.

Require Import Defs.Lc.
Require Import Defs.List.
Require Export Defs.Freevars.

(* Require Export Defs.Subst. *)
Require Export Defs.Subst.HdmSubst.
Require Export Defs.Subst.Notation.
Require Export Defs.Subst.NotInTac.
Require Import Defs.Subst.subst_skvar_binding_E.

Require Export Defs.WfSTt.

(*** Tactics 1 *)
Ltac ind_Sub θ := induction θ as [|[?τ ?α] ?θ].
Ltac ind_Sub_rev θ := induction θ as [|[?τ ?α] ?θ] using rev_ind.

(*** Definitions *)
Definition full_Sub_T (θ:Sub) (τ:T) := fv__α(τ) ⊆ dom_Sub θ.
#[export] Hint Unfold full_Sub_T : defs.

Definition full_Sub_Sc (θ:Sub) (σ:Sc) := fv__α(σ) ⊆ dom_Sub θ.
#[export] Hint Unfold full_Sub_Sc : defs.

Definition full_Sub_Tm (θ:Sub) (t:Tm) := fv__α(t) ⊆ dom_Sub θ.
#[export] Hint Unfold full_Sub_Sc : defs.

Definition Sub_wf (ψ:E) (θ:Sub) := forall (τ:T), τ ∈τ (codom_Sub θ) -> WfT ψ τ.
Notation "ψ ⊢θ θ" := (Sub_wf ψ θ) (at level 70).
#[export] Hint Unfold Sub_wf : defs.

Notation Sub_to_A θ := (map snd θ).

Fact Sub_to_A_app : forall (θ1 θ2:Sub), Sub_to_A (θ1 ++ θ2) = (Sub_to_A θ1) ++ (Sub_to_A θ2).
Proof. intros. rewrite map_app. crush. Qed.
#[export] Hint Rewrite Sub_to_A_app : core.

(*** Sub_app_dist *)
(** Sub distribution *)
(* T *)
Theorem Sub_app_T_cons : forall (τ1 τ2:T) (α:skvar) (θ:Sub),
    ⟦(τ1, α) :: θ ▹ τ2⟧ = {τ1 ≔ α} ⟦θ ▹ τ2⟧.
Proof. reflexivity. Qed.
#[export] Hint Rewrite Sub_app_T_cons : sub_dist.

Theorem Sub_app_T_app : forall (τ:T) (θ1 θ2:Sub),
    ⟦θ1 ++ θ2 ▹ τ⟧ = ⟦θ1 ▹ ⟦θ2 ▹ τ⟧⟧.
Proof. introv. ind_Sub θ1; crush; dist; crush. Qed.
#[export] Hint Rewrite Sub_app_T_app : sub_dist.

(* Sc *)
Fact Sub_app_Sc_cons : forall (σ:Sc) (τ:T) (α:skvar) (θ:Sub),
    ⟦(τ, α) :: θ ▹ σ⟧ = {τ ≔ α} ⟦θ ▹ σ⟧.
Proof. introv. induction σ; cbn; crush. Qed.
#[export] Hint Rewrite Sub_app_Sc_cons : sub_dist.

Fact Sub_app_Sc_app : forall (σ:Sc) (θ1 θ2:Sub),
    ⟦θ1 ++ θ2 ▹ σ⟧ = ⟦θ1 ▹ ⟦θ2 ▹ σ⟧⟧.
Proof. introv. ind_Sub θ1; crush; dist; crush. induction σ; cbn; crush. Qed.
#[export] Hint Rewrite Sub_app_Sc_app : sub_dist.

(* t *)
Theorem Sub_app_t_cons : forall (τ:T) (t:Tm) (α:skvar) (θ:Sub),
    ⟦(τ, α) :: θ ▹ t⟧ = {τ ≔ α} ⟦θ ▹ t⟧.
Proof. reflexivity. Qed.
#[export] Hint Rewrite Sub_app_t_cons : sub_dist.

Theorem Sub_app_t_app : forall (t:Tm) (θ1 θ2:Sub),
    ⟦θ1 ++ θ2 ▹ t⟧ = ⟦θ1 ▹ ⟦θ2 ▹ t⟧⟧.
Proof. introv. ind_Sub θ1; crush; dist; crush. Qed.
#[export] Hint Rewrite Sub_app_t_app : sub_dist.

(*** Sub_app_simpl *)
(** Sub_app_T *)
Section Sub_app_T_simpl.
  Variable (θ:Sub).
  Lemma Sub_app_T_id : forall (τ:T),
      (forall (τ':T) (α:skvar), { τ' ≔ α } τ = τ)
    -> ⟦θ ▹ τ⟧ = τ.
  Proof. introv. induction θ; crush. dist. crush. Qed.
  #[local] Hint Rewrite Sub_app_T_id : core.

  Fact Sub_app_T_Skvar_b : forall (n:nat),
      ⟦θ ▹ T__Var_b n⟧ = T__Var_b n.
  Proof. crush. Qed.

  Fact Sub_app_T_Unit :
      ⟦θ ▹ T__Unit⟧ = T__Unit.
  Proof. crush. Qed.

  Fact Sub_app_T_Bool :
      ⟦θ ▹ T__Bool⟧ = T__Bool.
  Proof. crush. Qed.

  Fact Sub_app_T_Fun : forall (τ1 τ2:T),
      ⟦θ ▹ T__Fun τ1 τ2⟧ = T__Fun ⟦θ ▹ τ1⟧ ⟦θ ▹ τ2⟧.
  Proof. induction θ; crush. dist. crush. Qed.

  Fact Sub_app_T_nil : forall (τ:T),
      ⟦[] ▹ τ⟧ = τ.
  Proof. crush. Qed.
End Sub_app_T_simpl.
#[export] Hint Rewrite Sub_app_T_Skvar_b Sub_app_T_Unit Sub_app_T_Bool Sub_app_T_Fun : core.
#[export] Hint Rewrite Sub_app_T_nil : core.

(** Sub_app_Sc *)
Section Sub_app_Sc_simpl.
  Variable (θ:Sub).
  (* Lemma Sub_app_Sc_id : forall (σ:Sc), *)
  (*     (forall (τ':T) (α:skvar), { τ' ≔ α } σ = σ) *)
  (*   -> ⟦θ ▹ σ⟧ = σ. *)
  (* Proof. *)
  (*   introv ID. induction σ; crush. rewrite Sub_app_T_id. reflexivity. introv. *)
  (*   forwards: ID τ'. inverts H. crush. *)
  (*   rewrite IHσ. reflexivity. introv. apply ID. *)

  (*   crush. Qed. *)
  (* #[local] Hint Rewrite Sub_app_Sc_id : core. *)

  Fact Sub_app_Sc_nil : forall (σ:Sc),
    ⟦[] ▹ σ⟧ = σ.
  Proof. induction σ; cbn; crush. Qed.
End Sub_app_Sc_simpl.
#[export] Hint Rewrite Sub_app_Sc_nil : core.

(** Sub_app_Tm *)
Section Sub_app_Tm_simpl.
  Variable (θ:Sub).
  Lemma Sub_app_Tm_id : forall (tm:Tm),
      (forall (τ':T) (α:skvar), { τ' ≔ α } tm = tm)
    -> ⟦θ ▹ tm⟧ = tm.
  Proof. introv. induction θ; cbn; crush. Qed.
  #[local] Hint Resolve Sub_app_Tm_id : core.

  Fact Sub_app_Tm_Tvar_b : forall (n:nat),
      ⟦θ ▹ t__Var_b n⟧ = t__Var_b n.
  Proof. crush. Qed.

  Fact Sub_app_Tm_Tvar_f : forall (x:var),
      ⟦θ ▹ t__Var_f x⟧ = t__Var_f x.
  Proof. crush. Qed.

  Fact Sub_app_Tm_Unit :
      ⟦θ ▹ t__Unit⟧ = t__Unit.
  Proof. crush. Qed.

  Fact Sub_app_Tm_True :
      ⟦θ ▹ t__True⟧ = t__True.
  Proof. crush. Qed.

  Fact Sub_app_Tm_False :
      ⟦θ ▹ t__False⟧ = t__False.
  Proof. crush. Qed.

  Fact Sub_app_Tm_App : forall t1 t2,
      ⟦θ ▹ t__App t1 t2⟧ = t__App ⟦θ ▹ t1⟧ ⟦θ ▹ t2⟧.
  Proof. introv. induction θ; cbn; crush. Qed.

  Fact Sub_app_Tm_TApp : forall t τ,
      ⟦θ ▹ t__TApp t τ⟧ = t__TApp ⟦θ ▹ t⟧ ⟦θ ▹ τ⟧.
  Proof. introv. induction θ; cbn; crush. Qed.

  Fact Sub_app_Tm_Lam : forall (τ:T) (t:Tm),
      ⟦θ ▹ t__Lam τ t⟧ = t__Lam ⟦θ ▹ τ⟧ ⟦θ ▹ t⟧.
  Proof. induction θ; crush. dist. crush. Qed.

  Fact Sub_app_Tm_TLam : forall (t:Tm),
      ⟦θ ▹ t__TLam t⟧ = t__TLam ⟦θ ▹ t⟧.
  Proof. induction θ; crush. dist. crush. Qed.

  Lemma Sub_app_Tm_open_Tm_wrt_Tm : forall (tm1 tm2:Tm),
      ⟦θ ▹ open_Tm_wrt_Tm tm1 tm2⟧ = open_Tm_wrt_Tm ⟦θ ▹ tm1⟧ ⟦θ ▹ tm2⟧.
  Proof. introv. ind_Sub θ; crush. cbn. crush. Qed.
End Sub_app_Tm_simpl.
#[export] Hint Rewrite Sub_app_Tm_Tvar_b Sub_app_Tm_Tvar_f Sub_app_Tm_Unit : core.
#[export] Hint Rewrite Sub_app_Tm_True Sub_app_Tm_False : core.
#[export] Hint Rewrite Sub_app_Tm_App Sub_app_Tm_TApp Sub_app_Tm_Lam Sub_app_Tm_TLam : core.
#[export] Hint Rewrite Sub_app_Tm_open_Tm_wrt_Tm : core.

(*** Lc_sub *)
Lemma Sub_wf_lc : forall θ ψ,
    ψ ⊢θ θ
  -> lc(θ).
Proof. intros. do 2 unfolds. intros. forwards: H. eassumption. crush. Qed.
#[export] Hint Resolve Sub_wf_lc : core.


Fact lc_Sub_empty :
    lc([]:Sub).
Proof. do 2 unfolds. simpl+. crush. Qed.
#[export] Hint Resolve lc_Sub_empty : core.

Lemma lc_Sub_app : forall θ1 θ2,
    lc(θ1)
  /\ lc(θ2)
  <-> lc(θ1 ++ θ2).
Proof.
  intros. unfold lc in *. unfold lcable_Sub in *.
  split.
  - intros. destruct H. simpl+ in H0. destr_union.
    apply H. crush.
    apply H1. crush.
  - intros. split; intros; apply H; simpl+; fsetdec'.
Qed.

Fact lc_Sub_app_l : forall θ1 θ2,
    lc(θ1 ++ θ2)
  -> lc(θ1).
Proof. apply lc_Sub_app. Qed.
Fact lc_Sub_app_r : forall θ1 θ2,
    lc(θ1 ++ θ2)
  -> lc(θ2).
Proof. apply lc_Sub_app. Qed.
Fact lc_Sub_cons_destr_l : forall θ α τ,
    lc((τ, α) :: θ)
  -> lc(τ).
Proof.
  intros. unfold lc in *. unfold lcable_Sub in *.
  intros. apply H. simpl+. clfsetdec'.
Qed.
Fact lc_Sub_cons_destr_r : forall θ τα,
    lc(τα :: θ)
  -> lc(θ).
Proof.
  intros. unfold lc in *. unfold lcable_Sub in *.
  intros. apply H. simpl+. fsetdec'.
Qed.
#[export] Hint Resolve lc_Sub_app_l lc_Sub_app_r lc_Sub_cons_destr_l lc_Sub_cons_destr_r : core.

Corollary lc_Sub_cons : forall θ τ α,
    lc(θ)
  -> lc(τ)
  -> lc((τ, α) :: θ).
Proof.
  intros. norm. apply lc_Sub_app. split. 2:assumption.
  unfolds. unfolds. intros. simpl+ in H1. T_facts.simpl_singleton_in H1. crush.
Qed.

(*** Sub_app notin *)

(* Ltac unfold_SetInterface := repeat *)
(*   ( unfold SIn             || unfold SInable_inst *)
(*   || unfold Ssingleton      || unfold Ssingletonable_inst *)
(*   || unfold Sdisjoint       || unfold Sdisjointable_inst *)
(*   ). *)
(* Tactic Notation "unfold_SetInterface" "in" hyp(H) := repeat *)
(*   ( unfold SIn        in H || unfold SInable_inst        in H *)
(*   || unfold Ssingleton in H || unfold Ssingletonable_inst in H *)
(*   || unfold Sdisjoint  in H || unfold Sdisjointable_inst  in H *)
(*   ). *)
(* Tactic Notation "unfold_SetInterface" "in" "*" := repeat *)
(*   ( unfold SIn        in * || unfold SInable_inst        in * *)
(*   || unfold Ssingleton in * || unfold Ssingletonable_inst in * *)
(*   || unfold Sdisjoint  in * || unfold Sdisjointable_inst  in * *)
(*   ). *)

Fact Sub_app_T_notindom : forall (θ:Sub) (τ:T),
    fv__α(τ) ∐ dom_Sub θ
  -> ⟦θ ▹ τ⟧ = τ.
Proof.
  introv DISJ. ind_Sub θ. crush. simpl+ in *. dist.
  rewrite IHθ. subst_notin. clear - DISJ. fsetdec+.
Qed.
#[export] Hint Resolve Sub_app_T_notindom : core.
Fact Sub_app_Sc_notindom : forall (θ:Sub) (σ:Sc),
    fv__α(σ) ∐ dom_Sub θ
  -> ⟦θ ▹ σ⟧ = σ.
Proof.
  introv DISJ. induction σ; simpl+.
  fequal. auto. crush.
Qed.
#[export] Hint Resolve Sub_app_Sc_notindom : core.
Fact Sub_app_Tm_notindom : forall (θ:Sub) (t:Tm),
    fv__α(t) ∐ dom_Sub θ
  -> ⟦θ ▹ t⟧ = t.
Proof.
  intros θ t DISJ. induction t. 1,2,3,4,5:crush. all:simpl+ in *.
  - specializes IHt1. fsetdec+.
    specializes IHt2. fsetdec+.
    crush.
  - specializes IHt. fsetdec+.
    rewrite Sub_app_T_notindom. 2:fsetdec+.
    crush.
  - specializes IHt. fsetdec+.
    rewrite Sub_app_T_notindom. 2:fsetdec+.
    crush.
  - specializes IHt. fsetdec+.
    crush.
Qed.
#[export] Hint Resolve Sub_app_Tm_notindom : core.

Ltac Sub_notin' :=
  match goal with
    | [ |- context[Sub_app ?x ?θ] ]  =>
        match type of x with
        | Sc => rewrite Sub_app_Sc_notindom
        | T  => rewrite Sub_app_T_notindom
        | Tm => rewrite Sub_app_Tm_notindom
        end; try reflexivity
  end.
Ltac Sub_notin := Sub_notin'; try solve [fsetdec+|crush].

(*** Freevars *)
Fact Sub_app_Sc_fsk : forall (θ:Sub) (σ:Sc),
    fv__α(⟦θ ▹ σ⟧) ⊆ (fv__α(σ) ∖ (dom_Sub θ)) ∪ skvars_codom_Sub θ.
Proof.
  introv. ind_Sub θ. simpl+. crush. simpl+ in *. dist.
  rewrite fsk_Sc_subst_skvar_Sc_upper. rewrite IHθ. fsetdec.
Qed.


Fact Sub_app_Sc_fsk' : forall (θ:Sub) (σ:Sc),
    fv__α(⟦θ ▹ σ⟧) ⊆ fv__α(σ) ∪ skvars_codom_Sub θ.
Proof. introv. rewrite Sub_app_Sc_fsk. fsetdec+. Qed.

Fact Sub_app_T_fsk : forall (θ:Sub) (τ:T),
    fv__α(⟦θ ▹ τ⟧) ⊆ (fv__α(τ) ∖ (dom_Sub θ)) ∪ skvars_codom_Sub θ.
Proof.
  introv. ind_Sub θ. simpl+. crush. simpl+ in *. dist.
  rewrite fsk_T_subst_skvar_T_upper. rewrite IHθ. fsetdec+.
Qed.

Fact Sub_app_T_fsk' : forall (θ:Sub) (τ:T),
    fv__α(⟦θ ▹ τ⟧) ⊆ fv__α(τ) ∪ skvars_codom_Sub θ.
Proof. introv. rewrite Sub_app_T_fsk. fsetdec+. Qed.

Fact Sub_app_Tm_fsk : forall (θ:Sub) (t:Tm),
    fv__α(⟦θ ▹ t⟧) ⊆ (fv__α(t) ∖ (dom_Sub θ)) ∪ skvars_codom_Sub θ.
Proof.
  introv. ind_Sub θ. simpl+. crush. simpl+ in *. dist.
  rewrite fsk_Tm_subst_skvar_Tm_upper. rewrite IHθ. fsetdec+.
Qed.

Fact Sub_app_Tm_fsk' : forall (θ:Sub) (t:Tm),
    fv__α(⟦θ ▹ t⟧) ⊆ fv__α(t) ∪ skvars_codom_Sub θ.
Proof. introv. rewrite Sub_app_Tm_fsk. fsetdec+. Qed.

(*** Subst comm *)
Lemma Sub_app_Tm_subst_tvar_Tm : forall (θ:Sub) (t__in t:Tm) (x:tvar),
    fv__α(t__in) ∐ dom_Sub θ
  -> {t__in ≔__x x}⟦θ ▹ t⟧ = ⟦θ ▹ {t__in ≔__x x} t⟧.
Proof.
  introv (* NICD *) DISJ.  ind_Sub θ. crush. dist. rewrite <- IHθ.
  - rewrite subst_tvar_Tm_subst_skvar_Tm.
    + fequals.
    + simpl+ in DISJ. clear - DISJ. fsetdec+.
  - simpl+ in DISJ. disj_sub.
Qed.

Lemma Sub_app_Tm_subst_tvar_Tm' : forall (θ:Sub) (t__in t:Tm) (x:tvar),
    {⟦θ ▹ t__in⟧ ≔__x x}⟦θ ▹ t⟧ = ⟦θ ▹ {t__in ≔__x x} t⟧.
Proof.
  introv (* NICD DISJ*). ind_Sub θ. crush. dist. rewrite <- IHθ.
  rewrite subst_tvar_Tm_subst_skvar_Tm'. reflexivity.
Qed.

Lemma Sub_app_Sc_subst_skvar_Sc : forall τ α (θ:Sub) (σ:Sc),
    α ∉ skvars_codom_Sub θ
  -> (fv__α(τ) ∪ {{α}}) ∐ dom_Sub θ
  -> {τ ≔ α}⟦θ ▹ σ⟧ = ⟦θ ▹ {τ ≔ α} σ⟧.
Proof.
  introv NICD DISJ. ind_Sub θ. crush. dist. rewrite <- IHθ.
  - rewrite subst_skvar_Sc_subst_skvar_Sc.
    + fequals. apply subst_skvar_T_notin. simpl+ in NICD. fsetdec.
    + simpl+ in DISJ. clear - DISJ. fsetdec+.
    + simpl+ in DISJ. intro. subst. eapply (in_disj α). eassumption. all:clfsetdec.
  - simpl+ in NICD. fsetdec.
  - simpl+ in DISJ. disj_sub.
Qed.

Lemma subst_skvar_T_Sub_app_T : forall α (τ1 τ2:T) θ,
    α ∉ dom_Sub θ ∪ skvars_codom_Sub θ
  -> fv__α(τ1) ∐ dom_Sub θ
  -> {τ1 ≔ α}⟦θ ▹ τ2⟧ = ⟦θ ▹ {τ1 ≔ α}τ2⟧.
Proof.
  introv NI DISJ. ind_Sub θ. crush. simpl+ in *. dist.
  rewrite <- IHθ. 2:fsetdec. 2:disj_sub.
  rewrite subst_skvar_T_subst_skvar_T. 2:in_disj. 2:fsetdec.
  fequals. subst_notin.
Qed.

Lemma subst_skvar_Tm_Sub_app_Tm : forall α (τ:T) (t:Tm) θ,
    α ∉ dom_Sub θ ∪ skvars_codom_Sub θ
  -> fv__α(τ) ∐ dom_Sub θ
  -> {τ ≔ α}⟦θ ▹ t⟧ = ⟦θ ▹ {τ ≔ α}t⟧.
Proof.
  introv NI DISJ. ind_Sub θ. crush. simpl+ in *. dist.
  rewrite <- IHθ. 2:fsetdec. 2:disj_sub.
  rewrite subst_skvar_Tm_subst_skvar_Tm. 2:in_disj. 2:fsetdec.
  fequals. subst_notin.
Qed.

(*** Open comm *)
Lemma Sub_app_Sc_open_Sc_wrt_T_rec : forall (θ:Sub) σ τ n,
    lc(θ)
  -> ⟦θ ▹ open_Sc_wrt_T_rec n τ σ⟧ = open_Sc_wrt_T_rec n ⟦θ ▹ τ⟧ ⟦θ ▹ σ⟧.
Proof.
  introv LC. ind_Sub θ; simpl+ in *. crush.
  forwards: IHθ. eauto.
  assert (lc(τ0)). eauto.
  dist. crush.
Qed.

Lemma Sub_app_Sc_open_Sc_wrt_T : forall (θ:Sub) σ τ,
    lc(θ)
  -> ⟦θ ▹ open_Sc_wrt_T σ τ⟧ = open_Sc_wrt_T ⟦θ ▹ σ⟧ ⟦θ ▹ τ⟧.
Proof. intros. unfold open_Sc_wrt_T. auto using Sub_app_Sc_open_Sc_wrt_T_rec. Qed.

Lemma Sub_app_open_Tm_wrt_T : forall θ t τ,
    lc(θ)
  -> ⟦θ ▹ open_Tm_wrt_T t τ⟧ = open_Tm_wrt_T ⟦θ ▹ t⟧ ⟦θ ▹ τ⟧.
Proof.
  introv LC. ind_Sub θ; simpl+ in *. crush.
  forwards: IHθ. eauto.
  assert (lc(τ0)). eauto.
  dist. crush.
Qed.

Lemma Sub_app_open_Tm_wrt_T_notindom : forall θ t τ,
    lc(θ)
  -> dom_Sub θ ∐ fv__α(τ)
  -> ⟦θ ▹ open_Tm_wrt_T t τ⟧ = open_Tm_wrt_T ⟦θ ▹ t⟧ τ.
Proof.
  introv LC DISJ. ind_Sub θ. crush.
  simpl+. rewrite IHθ. 2:eauto. 2:disj_sub.
  rewrite subst_skvar_Tm_open_Tm_wrt_T. 2:apply LC; simpl+; clfsetdec.
  fequals. apply subst_skvar_T_notin. simpl+ in DISJ. in_disj.
Qed.

Lemma Sub_app_T_open_T_wrt_T_rec : forall n θ τ1 τ2,
    lc(θ)
  -> ⟦θ ▹ open_T_wrt_T_rec n τ2 τ1⟧ = open_T_wrt_T_rec n ⟦θ ▹ τ2⟧ ⟦θ ▹ τ1⟧.
Proof.
  introv LC. ind_Sub θ. crush.
  dist. rewrite IHθ. rewrite subst_skvar_T_open_T_wrt_T_rec. crush. eauto. eauto.
Qed.

Lemma subst_skvar_T_Sub_app_T_open_T_wrt_T_rec : forall θ τ τ__in α n,
    lc(θ)
  -> lc(⟦θ ▹ τ__in⟧)
  -> α ∉ dom_Sub θ
  -> α ∉ fv__α(τ)
  -> α ∉ skvars_codom_Sub θ
  -> ⟦θ ▹ open_T_wrt_T_rec n τ__in τ⟧ = {⟦θ ▹ τ__in⟧ ≔ α}⟦θ ▹ open_T_wrt_T_rec n (T__Var_f α) τ⟧.
Proof.
  introv LC1 LC2 NI1 NI2 NI3. setoid_rewrite Sub_app_T_open_T_wrt_T_rec at 2. 2:assumption.
  rewrite (Sub_app_T_notindom θ (T__Var_f α)). 2:simpl+; fsetdec.
  rewrite subst_skvar_T_open_T_wrt_T_rec. 2:assumption. simpl+. if_taut.
  subst_notin'. 2:rewrite Sub_app_T_fsk'; fsetdec.
  apply Sub_app_T_open_T_wrt_T_rec. assumption.
Qed.


(*** Lc Sub_app *)
Lemma Sub_app_T_lc : forall (θ:Sub) (τ:T),
    lc(τ)
  -> lc(θ)
  -> lc(⟦θ ▹ τ⟧).
Proof. intros. ind_Sub θ. crush. dist. eauto using lc_substskvar_T. Qed.

(*** Folding/unsimpl *)
Fact fold_Sub_app_Sc_mono : forall (θ:Sub) (τ:T),
    S__T ⟦θ ▹ τ⟧ = ⟦θ ▹ S__T τ⟧.
Proof. reflexivity. Qed.

(*** Tactics *)
Lemma Sub_app_T_ska_decide : forall (θ:Sub) (α:skvar),
    α ∉ dom_Sub θ
  \/ exists (τ:T), (τ, α) ∈τx bindings_Sub θ.
Proof.
  introv. ind_Sub θ. eauto.
  destr_eq α α0. right. exists τ. fsetdec+.
  destr_in IHθ. left. simpl+ in *. fsetdec+.
  simpl+. right. exists τ0. fsetdec'+.
Qed.

Ltac do_sub_skvar_decide θ α :=
      let H := fresh "H" in
      forwards H: Sub_app_T_ska_decide θ α
      ; destruct H as [?NIS|[?τ ?IS]].

Ltac sub_decide :=
    match goal with
  | [ H : context[Sub_app_T (T__Var_f ?α) ?θ] |- _ ] =>
      do_sub_skvar_decide θ α
  | [ |- context[Sub_app_T (T__Var_f ?α) ?θ] ] =>
      do_sub_skvar_decide θ α
  | [ H : context[⟦?θ ▹ T__Var_f ?α⟧] |- _ ] =>
      do_sub_skvar_decide θ α
  | [ |- context[⟦?θ ▹ T__Var_f ?α⟧] ] =>
      do_sub_skvar_decide θ α
  end.

(*** Membership *)
Lemma dom_Sub_bindings_Sub : forall (α:skvar) (θ:Sub),
    α ∈ dom_Sub θ
  -> exists τ, (τ, α) ∈τx bindings_Sub θ.
Proof.
  introv IN. ind_Sub θ. crush+.
  simpl+ in IN. destr_union.
  - exists τ. crush+.
  - forwards IH: IHθ. assumption. destr_in IH.
    exists τ0. crush.
Qed.
#[export] Hint Resolve dom_Sub_bindings_Sub : core.


(*** Sub_wf *)
Fact Sub_wf_app : forall ψ θ1 θ2,
    ψ ⊢θ θ1
  /\ ψ ⊢θ θ2
  <-> ψ ⊢θ (θ1 ++ θ2).
Proof.
  split.
  - introv [WF1 WF2] IN. simpl+ in IN. destr_union; crush.
  - introv WF. split.
    + constructor.
      apply WF. simpl+. fsetdec'.
      apply WF. simpl+. fsetdec'.
    + constructor.
      apply WF. simpl+. fsetdec'.
      apply WF. simpl+. fsetdec'.
Qed.
Corollary Sub_wf_app__l : forall ψ θ1 θ2,
    ψ ⊢θ (θ1 ++ θ2)
  -> ψ ⊢θ θ1.
Proof. apply Sub_wf_app. Qed.
Corollary Sub_wf_app__r : forall ψ θ1 θ2,
    ψ ⊢θ (θ1 ++ θ2)
  -> ψ ⊢θ θ1.
Proof. apply Sub_wf_app. Qed.
Corollary Sub_wf_cons_destr : forall ψ θ s,
    ψ ⊢θ (s :: θ)
  -> ψ ⊢θ θ.
Proof. intros. norm in H. apply Sub_wf_app in H. crush. Qed.
#[export] Hint Resolve Sub_wf_app__l Sub_wf_app__r Sub_wf_cons_destr : core.
Corollary Sub_wf_app__constr : forall ψ θ1 θ2,
    ψ ⊢θ θ1
  -> ψ ⊢θ θ2
  -> ψ ⊢θ (θ1 ++ θ2).
Proof. intros. forwards>: (Sub_wf_app ψ θ1 θ2). split; eassumption. crush. Qed.


Corollary Sub_wf_cons : forall ψ θ τ α,
    ψ ⊢θ θ
  -> ψ ⊢wfτ τ
  -> ψ ⊢θ (τ, α) :: θ.
Proof.
  introv WFS WFT. norm. apply Sub_wf_app. split. 2:assumption. unfolds.
  intros. simpl+ in H. applys_eq WFT. crush.
Qed.

Fact Sub_wf_nil : forall ψ,
    ψ ⊢θ [].
Proof. constructor; crush+. Qed.
#[export] Hint Resolve Sub_wf_nil : core.

Fact Sub_wf_codom : forall ψ θ,
    ψ ⊢θ θ
  -> skvars_codom_Sub θ ⊆ E_A_skvars ψ.
Proof.
  introv WF. ind_Sub θ. crush.
  introv IN. simpl+ in IN. destr_union.
  assert (ψ ⊢wfτ τ). apply WF. clfsetdec+.
  unfold WfT in *. jauto.
  apply IHθ. eauto. crush.
Qed.

(*** Sub_to_A *)
Fact varl_Sub_to_A_dom : forall (θ:Sub),
    varl (Sub_to_A θ) = dom_Sub θ.
Proof. ind_Sub θ; crush. Qed.
#[export] Hint Rewrite varl_Sub_to_A_dom : core.

(*** Sub_app_E *)

Definition Sub_app_E : E -> Sub -> E := fold_right (uncurry subst_skvar_binding_E).
#[export] Instance Sub_appable_E : Sub_appable E := { Sub_app := Sub_app_E }.

Lemma Sub_app_E_app_sub : forall (ψ:E) (θ1 θ2:Sub),
    ⟦θ1 ++ θ2 ▹ ψ⟧ = ⟦θ1 ▹ ⟦θ2 ▹ ψ⟧⟧.
Proof. introv. ind_Sub θ1; crush; dist; crush. Qed.
#[export] Hint Rewrite Sub_app_E_app_sub : sub_dist.

Lemma Sub_app_E_app_E : forall (ψ1 ψ2:E) (θ:Sub),
    ⟦θ ▹ ψ1 +++ ψ2⟧ = ⟦θ ▹ ψ1⟧ +++ ⟦θ ▹ ψ2⟧.
Proof. introv. ind_Sub θ; crush. dist. rewrite IHθ. dist. crush. Qed.
#[export] Hint Rewrite Sub_app_E_app_E : sub_dist.

Lemma Sub_app_E_notindom : forall (ψ:E) (θ:Sub),
      E_skvars ψ ∐ dom_Sub θ
    -> ⟦θ ▹ ψ⟧ = ψ.
Proof.
  introv DISJ. ind_Sub θ. crush.
  simpl+. rewrite IHθ. 2:simpl+ in DISJ; disj_sub.
  apply subst_skvar_binding_E_notin. simpl+ in DISJ. in_disj.
Qed.

Lemma Sub_app_E_nil : forall θ,
    ⟦θ ▹ •⟧ = •.
Proof. introv. ind_Sub θ; crush. dist. crush. Qed.
#[export] Hint Rewrite Sub_app_E_nil : core.

Lemma Sub_app_E_consx : forall (ψ:E) x σ θ,
    ⟦θ ▹ ψ ::x x :- σ⟧ = ⟦θ ▹ ψ⟧ ::x x :- ⟦θ ▹ σ⟧.
Proof. introv. ind_Sub θ; crush. dist. rewrite IHθ. crush. Qed.
#[export] Hint Rewrite Sub_app_E_consx : sub_dist.

Fact bindings_Sub_dom_Sub : forall τ α θ,
    (τ, α) ∈τx bindings_Sub θ
  -> τ ∈τ codom_Sub θ
  /\ α ∈ dom_Sub θ.
Proof.
  intros. ind_Sub θ. crush. simpl+ in H. destr_union. inverts H. simpl+. split; fsetdec'.
  specializes IHθ. eassumption. destruct IHθ. simpl+. split; fsetdec'.
Qed.
Corollary bindings_Sub_dom_Sub1 : forall τ α θ,
    (τ, α) ∈τx bindings_Sub θ
  -> τ ∈τ codom_Sub θ.
Proof. intros. eapply bindings_Sub_dom_Sub. eassumption. Qed.
Corollary bindings_Sub_dom_Sub2 : forall τ α θ,
    (τ, α) ∈τx bindings_Sub θ
  -> α ∈ dom_Sub θ.
Proof. intros. eapply bindings_Sub_dom_Sub. eassumption. Qed.
#[export] Hint Resolve bindings_Sub_dom_Sub1 bindings_Sub_dom_Sub2 : core.

(*** Sub rewriting *)
(** uni_Sub_nd *)
Definition uni_Sub_nd (θ:Sub) := NoDup (Sub_to_A θ).

(* construction *)
Fact uni_Sub_nd_nil : uni_Sub_nd [].
Proof. unfolds. crush. constructor. Qed.
#[export] Hint Resolve uni_Sub_nd_nil : core.

Fact uni_Sub_nd_cons : forall τ α θ,
    uni_Sub_nd θ
  -> α ∉ dom_Sub θ
  -> uni_Sub_nd ((τ, α) :: θ).
Proof. introv P NID. unfolds. simpl+. constructor. apply notin_varl_notin_a. crush. crush. Qed.

(* destruction *)
Fact uni_Sub_nd_app : forall θ1 θ2,
    uni_Sub_nd (θ1 ++ θ2)
  -> uni_Sub_nd θ1
  /\ uni_Sub_nd θ2.
Proof.
  intros. unfold uni_Sub_nd in *. unfold Sub_to_A in H. simpl+ in H.
  split; eauto using NoDup_app_remove_l, NoDup_app_remove_r.
Qed.
Corollary uni_Sub_nd_app1 : forall θ1 θ2,
    uni_Sub_nd (θ1 ++ θ2)
  -> uni_Sub_nd θ1.
Proof. intros. apply uni_Sub_nd_app in H. jauto. Qed.
Corollary uni_Sub_nd_app2 : forall θ1 θ2,
    uni_Sub_nd (θ1 ++ θ2)
  -> uni_Sub_nd θ2.
Proof. intros. apply uni_Sub_nd_app in H. jauto. Qed.
#[export] Hint Resolve uni_Sub_nd_app1 uni_Sub_nd_app2 : core.

Fact uni_Sub_nd_cons_destr : forall τ α θ,
    uni_Sub_nd ((τ, α) :: θ)
  -> uni_Sub_nd θ
  /\ α ∉ dom_Sub θ.
Proof. intros. inverts H. splits. assumption. eapply notin_a_notin_varl in H2. crush. Qed.
Corollary uni_Sub_nd_cons_destr1 : forall τ α θ,
    uni_Sub_nd ((τ, α) :: θ)
  -> uni_Sub_nd θ.
Proof. intros. eapply uni_Sub_nd_cons_destr. eassumption. Qed.
Corollary uni_Sub_nd_cons_destr2 : forall τ α θ,
    uni_Sub_nd ((τ, α) :: θ)
  -> α ∉ dom_Sub θ.
Proof. intros. eapply uni_Sub_nd_cons_destr. eassumption. Qed.
#[export] Hint Resolve uni_Sub_nd_cons_destr1 uni_Sub_nd_cons_destr2 : core.

(** uni_Sub *)
Definition uni_Sub (θ:Sub) := forall τ1 τ2 α, (τ1, α) ∈τx bindings_Sub θ -> (τ2, α) ∈τx bindings_Sub θ -> τ1 = τ2.

(* construction *)
Lemma uni_Sub_nd_uni_Sub : forall θ, uni_Sub_nd θ -> uni_Sub θ.
Proof.
  intros. ind_Sub θ. unfolds. intros. crush. unfolds. intros. simpl+ in H0. destr_union; simpl+ in H1; destr_union.
  - inverts H0. inverts H1. crush.
  - inverts H0. false. inverts H. apply H3. apply bindings_Sub_dom_Sub2 in H1. apply in_varl_in_a. crush.
  - inverts H1. false. inverts H. apply H3. apply bindings_Sub_dom_Sub2 in H0. apply in_varl_in_a. crush.
  - eapply IHθ; eauto.
Qed.
#[export] Hint Resolve uni_Sub_nd_uni_Sub : core.

Fact uni_Sub_cons : forall τ α θ,
    uni_Sub θ
  -> (forall τ', (τ', α) ∈τx bindings_Sub θ -> τ = τ')
  -> uni_Sub ((τ, α) :: θ).
Proof.
  introv P IN. unfolds. intros. simpl+ in H. destr_union; simpl+ in H0; destr_union.
  - crush.
  - inverts H. specializes IN. eassumption. crush.
  - inverts H0. specializes IN. eassumption. crush.
  - eauto.
Qed.

Fact uni_Sub_cons' : forall τ α θ,
    uni_Sub θ
  -> α ∉ dom_Sub θ
  -> uni_Sub ((τ, α) :: θ).
Abort.

(* deconstruction *)
Fact uni_Sub_app : forall θ1 θ2,
    uni_Sub (θ1 ++ θ2)
  -> uni_Sub θ1
  /\ uni_Sub θ2.
Proof.
  unfold uni_Sub. split; intros; applys H α; simpl+; fsetdec'.
Qed.
Corollary uni_Sub_app1 : forall θ1 θ2,
    uni_Sub (θ1 ++ θ2)
  -> uni_Sub θ1.
Proof. intros. apply uni_Sub_app in H. jauto. Qed.
Corollary uni_Sub_app2 : forall θ1 θ2,
    uni_Sub (θ1 ++ θ2)
  -> uni_Sub θ2.
Proof. intros. apply uni_Sub_app in H. jauto. Qed.
#[export] Hint Resolve uni_Sub_app1 uni_Sub_app2 : core.

Fact uni_Sub_cons_destr : forall τ α θ,
    uni_Sub ((τ, α) :: θ)
  -> uni_Sub θ.
Proof. intros. norm in H. eauto. Qed.
#[export] Hint Resolve uni_Sub_cons : core.

(** dom/codom disj *)
Definition dom_codom_disj_Sub (θ:Sub) := dom_Sub θ ∐ skvars_codom_Sub θ.

(* constuction *)
Fact dom_codom_disj_Sub_nil : dom_codom_disj_Sub [].
Proof. unfolds. crush. Qed.
#[export] Hint Resolve dom_codom_disj_Sub_nil : core.

Fact dom_codom_disj_Sub_cons : forall τ α θ,
    dom_codom_disj_Sub θ
  -> α ∉ skvars_codom_Sub θ
  -> α ∉ fv__α(τ)
  -> dom_Sub θ ∐ fv__α(τ)
  -> dom_codom_disj_Sub ((τ, α) :: θ).
Proof.
  introv P NICD NIT DISJ. simpl+.
  unfolds. simpl+. disj_union; disj_union'.
  - simpl+. fsetdec.
  - simpl+. fsetdec.
  - simpl+. eassumption.
  - eassumption.
Qed.

(* deconstruction *)
Fact dom_codom_disj_Sub_app : forall θ1 θ2,
    dom_codom_disj_Sub (θ1 ++ θ2)
  -> dom_codom_disj_Sub θ1
  /\ dom_codom_disj_Sub θ2.
Proof.
  unfold dom_codom_disj_Sub. split; intros; disj_sub.
Qed.
Corollary dom_codom_disj_Sub_app1 : forall θ1 θ2,
    dom_codom_disj_Sub (θ1 ++ θ2)
  -> dom_codom_disj_Sub θ1.
Proof. intros. apply dom_codom_disj_Sub_app in H. jauto. Qed.
Corollary dom_codom_disj_Sub_app2 : forall θ1 θ2,
    dom_codom_disj_Sub (θ1 ++ θ2)
  -> dom_codom_disj_Sub θ2.
Proof. intros. apply dom_codom_disj_Sub_app in H. jauto. Qed.
#[export] Hint Resolve dom_codom_disj_Sub_app1 dom_codom_disj_Sub_app2 : core.

Fact dom_codom_disj_Sub_cons_destr : forall τ α θ,
    dom_codom_disj_Sub ((τ, α) :: θ)
  -> dom_codom_disj_Sub θ
  /\ α ∉ fv__α(τ)
  /\ α ∉ skvars_codom_Sub θ
  /\ fv__α(τ) ∐ dom_Sub θ.
Proof.
  unfold dom_codom_disj_Sub. intros. simpl+ in H. splits. disj_sub.
  unfold not. intro. applys in_disj α H; simpl; fsetdec.
  unfold not. intro. applys in_disj α H; simpl; fsetdec.
  symmetry. disj_sub.
Qed.
Corollary dom_codom_disj_Sub_cons_destr1 : forall τ α θ,
    dom_codom_disj_Sub ((τ, α) :: θ)
  -> dom_codom_disj_Sub θ.
Proof. intros. apply dom_codom_disj_Sub_cons_destr in H. jauto. Qed.
Corollary dom_codom_disj_Sub_cons_destr2 : forall τ α θ,
    dom_codom_disj_Sub ((τ, α) :: θ)
  -> α ∉ fv__α(τ).
Proof. intros. apply dom_codom_disj_Sub_cons_destr in H. jauto. Qed.
Corollary dom_codom_disj_Sub_cons_destr3 : forall τ α θ,
    dom_codom_disj_Sub ((τ, α) :: θ)
  -> α ∉ skvars_codom_Sub θ.
Proof. intros. apply dom_codom_disj_Sub_cons_destr in H. jauto. Qed.
Corollary dom_codom_disj_Sub_cons_destr4 : forall τ α θ,
    dom_codom_disj_Sub ((τ, α) :: θ)
  -> fv__α(τ) ∐ dom_Sub θ.
Proof. intros. apply dom_codom_disj_Sub_cons_destr in H. jauto. Qed.
#[export] Hint Resolve dom_codom_disj_Sub_cons_destr1 dom_codom_disj_Sub_cons_destr2 dom_codom_disj_Sub_cons_destr3 dom_codom_disj_Sub_cons_destr4 : core.

(** P_Sub *)
Definition P_Sub (θ:Sub) := uni_Sub θ /\ dom_codom_disj_Sub θ.

(* constructing *)
Fact P_Sub_nil : P_Sub [].
Proof. unfolds. crush. Qed.
#[export] Hint Resolve P_Sub_nil : core.

Fact P_Sub_cons : forall τ α θ,
    P_Sub θ
  -> α ∉ dom_Sub θ
  -> α ∉ skvars_codom_Sub θ
  -> α ∉ fv__α(τ)
  -> dom_Sub θ ∐ fv__α(τ)
  -> P_Sub ((τ, α) :: θ).
Abort.
(* Proof. *)
(*   introv [?P ?P] NID NICD NIT DISJ. unfolds. *)
(*   split. eapply uni_Sub_nd_uni_Sub. eapply uni_Sub_nd_cons. eauto. *)
(*   split; eauto using uni_Sub_nd_cons. *)
(* Qed. *)


Fact P_Sub_uni : forall θ, P_Sub θ -> uni_Sub θ.
Proof. intros. unfolds in H. crush. Qed.
Fact P_Sub_dom_codom : forall θ, P_Sub θ -> dom_codom_disj_Sub θ. Proof. intros. unfolds in H. crush. Qed.

Definition bindings_Sub_eq (θ1 θ2:Sub) : Prop := bindings_Sub θ1 ≡τx bindings_Sub θ2.

Definition P_Sub_eq : Sub -> Sub -> Prop := fun θ1 θ2 => P_Sub θ1 /\ P_Sub θ2 /\ bindings_Sub_eq θ1 θ2.
Notation  "θ1 ≡θ θ2"  := (P_Sub_eq θ1 θ2) (at level 70).

Fact P_Sub_eq_P1 : forall θ1 θ2, θ1 ≡θ θ2 -> P_Sub θ1. intros. unfolds. crush. Qed.
Fact P_Sub_eq_P2 : forall θ1 θ2, θ1 ≡θ θ2 -> P_Sub θ2. intros. unfolds. crush. Qed.
Fact P_Sub_eq_bindings : forall θ1 θ2, θ1 ≡θ θ2 -> bindings_Sub θ1 ≡τx bindings_Sub θ2. intros. unfolds. crush. Qed.
#[export] Hint Resolve P_Sub_eq_P1 P_Sub_eq_P2 : core.



(* cons *)


(* Lemma P_Sub_eq_lookup : forall θ τ1 τ2 α, *)
(*     P_Sub θ *)
(*   -> (τ1, α) ∈τx bindings_Sub θ *)
(*   -> (τ2, α) ∈τx bindings_Sub θ *)
(*   -> τ1 = τ2. *)
(* Proof. *)
(*   intro θ. ind_Sub θ; introv [UNI _] IN1 IN2. crush. *)
(*   simpl+ in IN1. destr_union; simpl+ in IN2; destr_union. *)
(*   - inverts H. inverts H0. crush. *)
(*   - false. inverts H. inverts UNI. apply H2. eapply bindings_Sub_dom_Sub2 in H0. apply in_varl_in_a. crush. *)
(*   - false. inverts H0. inverts UNI. apply H2. eapply bindings_Sub_dom_Sub2 in H. apply in_varl_in_a. crush. *)
(*   - eapply IHθ. admit. eassumption. eassumption. *)
(* Admitted. *)

Fact codom_Sub_skvars_codom_Sub : forall τ θ,
    τ ∈τ codom_Sub θ
  -> fv__α(τ) ⊆ skvars_codom_Sub θ.
Proof. intros. ind_Sub θ. crush. simpl+ in *. destr_union. fsetdec. rewrite IHθ. fsetdec. crush. Qed.

Lemma P_Sub_app : forall τ α θ,
    P_Sub θ
  -> (τ, α) ∈τx bindings_Sub θ
  -> ⟦θ ▹ T__Var_f α⟧ = τ.
Proof.
  introv P IN. ind_Sub θ. crush.
  do_sub_skvar_decide θ α.
  - dist. Sub_notin'. 2:simpl+; fsetdec.
    simpl+ in IN. destr_union. inverts H. simpl+. if_taut.
    eapply bindings_Sub_dom_Sub in H. crush.
  - forwards: in_disj2 α0. symmetry. eapply P_Sub_dom_codom. eassumption. simpl+. fsetdec.
    dist. forwards: proj1 P. specializes H0 τ τ1 α. specializes H0.  eassumption. simpl+. crush.
    subst. specializes IHθ. admit. eassumption. rewrite IHθ.
    subst_notin'. simpl+ in H. erewrite (codom_Sub_skvars_codom_Sub _ θ). fsetdec.
    eapply bindings_Sub_dom_Sub. crush.
Admitted.

Lemma bindings_Sub_eq_dom_Sub_eq : forall θ1 θ2,
    bindings_Sub θ1 ≡τx bindings_Sub θ2
  -> dom_Sub θ1 ≡ dom_Sub θ2.
Proof.
  introv EQ. unfolds in EQ. unfolds. split; intros.
  - forwards [τ IN]: dom_Sub_bindings_Sub. eassumption.
    eapply bindings_Sub_dom_Sub2. apply EQ. eauto.
  - forwards [τ IN]: dom_Sub_bindings_Sub. eassumption.
    eapply bindings_Sub_dom_Sub2. apply EQ. eauto.
Qed.

#[export] Instance bindings_Sub_eq_dom_Sub_proper : Proper (bindings_Sub_eq ==> Equal) dom_Sub.
Proof. autounfold. intros. eauto using bindings_Sub_eq_dom_Sub_eq. Qed.

Lemma P_Sub_eq_dom_Sub_eq : forall θ1 θ2,
    θ1 ≡θ θ2
  -> dom_Sub θ1 ≡ dom_Sub θ2.
Proof.
  intros. destruct H as [_ [_ EQ]].
  eauto using bindings_Sub_eq_dom_Sub_eq.
Qed.

#[export] Instance P_Sub_eq_dom_Sub_eq_proper : Proper (P_Sub_eq ==> Equal) dom_Sub.
Proof. autounfold. eauto using P_Sub_eq_dom_Sub_eq. Qed.

Lemma P_Sub_eq_app_T_rewr : forall θ1 θ2 (τ:T),
    θ1 ≡θ θ2
  -> ⟦θ1 ▹ τ⟧ = ⟦θ2 ▹ τ⟧.
Proof.
  introv EQ. induction τ; simpl. 1,3,4,5:crush.
  sub_decide. Sub_notin. Sub_notin'. rewrite <- EQ. simpl+. fsetdec.
  forwards: P_Sub_app τ α θ1. jauto. eassumption.
  forwards: P_Sub_app τ α θ2. jauto. erewrite P_Sub_eq_bindings. eassumption. admit. crush.
Admitted.

Lemma P_Sub_eq_app_Sc_rewr : forall θ1 θ2 (σ:Sc),
    θ1 ≡θ θ2
  -> ⟦θ1 ▹ σ⟧ = ⟦θ2 ▹ σ⟧.
Proof.
  intros. induction σ; simpl+; fequals. auto using P_Sub_eq_app_T_rewr.
Qed.

Lemma P_Sub_eq_app_Tm_rewr : forall θ1 θ2 (t:Tm),
    θ1 ≡θ θ2
  -> ⟦θ1 ▹ t⟧ = ⟦θ2 ▹ t⟧.
Proof.
  intros. induction t0; simpl+. 1,2,3,4,5,6,9:now crush.
  forwards: P_Sub_eq_app_T_rewr. eassumption. crush.
  forwards: P_Sub_eq_app_T_rewr. eassumption. crush.
Qed.

#[export] Instance uni_Sub_bindings_Sub_eq_proper : Proper (bindings_Sub_eq ==> iff) uni_Sub.
Admitted.


(* Lemma dom_Sub_bindings_Sub : forall (α:skvar) (θ:Sub), *)
(*     α ∈ dom_Sub θ *)
(*   -> exists τ, (τ, α) ∈τx bindings_Sub θ. *)

#[export] Instance bindings_Sub_eq_skvars_codom_Sub_proper : Proper (bindings_Sub_eq ==> Equal) skvars_codom_Sub.
Proof. autounfold. intros. unfolds. split; intros. Admitted.


#[export] Instance dom_codom_disj_Sub_bindings_Sub_eq_proper : Proper (bindings_Sub_eq ==> impl) dom_codom_disj_Sub.
Proof.
  autounfold. intros. unfold dom_codom_disj_Sub in *. eapply atoms_facts.disjoint_equal_proper. 3:eassumption.
  rewrite <- H. reflexivity.
  rewrite <- H. reflexivity.
Qed.

#[export] Instance P_Sub_bindings_Sub_eq_proper : Proper (bindings_Sub_eq ==> impl) P_Sub.
Proof. autounfold. intros. unfold P_Sub in *. split; rewrite <- H; jauto. Qed.

(* #[export] Instance bla_proper : Proper (bindings_Sub_eq ==> bindings_Sub_eq ==> iff) P_Sub_eq. *)
(* Proof. autounfold. split; intros. unfolds. *)

(** bindings_Sub_sub *)
Definition bindings_Sub_sub (θ1 θ2:Sub) : Prop := bindings_Sub θ1 ⊆τx bindings_Sub θ2.

Definition P_Sub_sub : Sub -> Sub -> Prop := fun θ1 θ2 => P_Sub θ1 /\ P_Sub θ2 /\ bindings_Sub_sub θ1 θ2.
Notation  "θ1 ⊆θ θ2"  := (P_Sub_sub θ1 θ2) (at level 70).

Fact P_Sub_sub_P1 : forall θ1 θ2, θ1 ⊆θ θ2 -> P_Sub θ1. intros. unfolds. crush. Qed.
Fact P_Sub_sub_P2 : forall θ1 θ2, θ1 ⊆θ θ2 -> P_Sub θ2. intros. unfolds. crush. Qed.
Fact P_Sub_sub_bindings : forall θ1 θ2, θ1 ⊆θ θ2 -> bindings_Sub θ1 ⊆τx bindings_Sub θ2. intros. unfolds. crush. Qed.
#[export] Hint Resolve P_Sub_sub_P1 P_Sub_sub_P2 : core.

Fact full_Sub_T_Fun1 : forall θ τ1 τ2,
    full_Sub_T θ (T__Fun τ1 τ2)
  -> full_Sub_T θ τ1.
Proof. unfold full_Sub_T. simpl+. intros. fsetdec. Qed.
Fact full_Sub_T_Fun2 : forall θ τ1 τ2,
    full_Sub_T θ (T__Fun τ1 τ2)
  -> full_Sub_T θ τ2.
Proof. unfold full_Sub_T. simpl+. intros. fsetdec. Qed.
#[export] Hint Resolve full_Sub_T_Fun1 full_Sub_T_Fun2 : core.

Fact full_Sub_Tm_App1 : forall θ t1 t2,
    full_Sub_Tm θ (t__App t1 t2)
  -> full_Sub_Tm θ t1.
Proof. unfold full_Sub_Tm. simpl+. intros. fsetdec. Qed.
Fact full_Sub_Tm_App2 : forall θ t1 t2,
    full_Sub_Tm θ (t__App t1 t2)
  -> full_Sub_Tm θ t2.
Proof. unfold full_Sub_Tm. simpl+. intros. fsetdec. Qed.
#[export] Hint Resolve full_Sub_Tm_App1 full_Sub_Tm_App2 : core.

Fact full_Sub_Tm_TApp1 : forall θ t1 τ2,
    full_Sub_Tm θ (t__TApp t1 τ2)
  -> full_Sub_Tm θ t1.
Proof. unfold full_Sub_Tm. simpl+. intros. fsetdec. Qed.
Fact full_Sub_Tm_TApp2 : forall θ t1 τ2,
    full_Sub_Tm θ (t__TApp t1 τ2)
  -> full_Sub_T  θ τ2.
Proof. unfold full_Sub_Tm. unfold full_Sub_T. simpl+. intros. fsetdec. Qed.
#[export] Hint Resolve full_Sub_Tm_TApp1 full_Sub_Tm_TApp2 : core.

Fact full_Sub_Tm_Lam1 : forall θ τ1 t2,
    full_Sub_Tm θ (t__Lam τ1 t2)
  -> full_Sub_T  θ τ1.
Proof. unfold full_Sub_Tm. unfold full_Sub_T. simpl+. intros. fsetdec. Qed.
Fact full_Sub_Tm_Lam2 : forall θ τ1 t2,
    full_Sub_Tm θ (t__Lam τ1 t2)
  -> full_Sub_Tm θ t2.
Proof. unfold full_Sub_Tm. simpl+. intros. fsetdec. Qed.
#[export] Hint Resolve full_Sub_Tm_Lam1 full_Sub_Tm_Lam2 : core.

Fact full_Sub_Sc_Forall : forall θ σ,
    full_Sub_Sc θ (S__Forall σ)
  -> full_Sub_Sc θ σ.
Proof. unfold full_Sub_Sc. simpl+. crush. Qed.
#[export] Hint Rewrite full_Sub_Sc_Forall : core.

Lemma P_Sub_sub_app_T_rewr : forall θ1 θ2 (τ:T),
    full_Sub_T θ1 τ
  -> θ1 ⊆θ θ2
  -> ⟦θ1 ▹ τ⟧ = ⟦θ2 ▹ τ⟧.
Proof.
  introv FS EQ. induction τ; simpl. 1,3,4:crush.
  - sub_decide. specializes FS α. specializes FS. simpl+. fsetdec. fsetdec.
    forwards: P_Sub_app τ α θ1. eauto. eassumption.
    forwards: P_Sub_app τ α θ2. eauto. erewrite <- P_Sub_sub_bindings. eassumption. eassumption. crush.
  - specializes IHτ1. eauto. specializes IHτ2. eauto. crush.
Qed.

Lemma P_Sub_sub_app_Sc_rewr : forall θ1 θ2 (σ:Sc),
    full_Sub_Sc θ1 σ
  -> θ1 ⊆θ θ2
  -> ⟦θ1 ▹ σ⟧ = ⟦θ2 ▹ σ⟧.
Proof.
  intros. induction σ; simpl+; fequals. auto using P_Sub_sub_app_T_rewr. crush.
Qed.

Lemma P_Sub_sub_app_Tm_rewr : forall θ1 θ2 (t:Tm),
    full_Sub_Tm θ1 t
  -> θ1 ⊆θ θ2
  -> ⟦θ1 ▹ t⟧ = ⟦θ2 ▹ t⟧.
Proof.
  intros. induction t0; simpl+. 1,2,3,4,5,9:now crush. all:simpl+ in *.
  - specializes IHt0_1. eauto. specializes IHt0_2. eauto. crush.
  - forwards: P_Sub_sub_app_T_rewr. eauto. eassumption. specializes IHt0. eauto. crush.
  - forwards: P_Sub_sub_app_T_rewr. eauto. eassumption. specializes IHt0. eauto. crush.
Qed.

(*** Alg/Dec *)

(** props *)
Fact algorithmic_neq_declarative : forall (α:var),
    alg α
  -> dec α
  -> False.
Proof. introv ALG DEC. crush. Qed.

(** alg_to_dec *)
Definition alg_to_dec (θ:Sub) := alg_L (dom_Sub θ) /\ dec_L (skvars_codom_Sub θ).

Fact alg_to_dec_dom_codom_disj_Sub : forall θ,
    alg_to_dec θ
  -> dom_codom_disj_Sub θ.
Proof. intros. apply L_alg_dec_disj; crush. Qed.

Lemma alg_to_dec_app : forall θ1 θ2,
    alg_to_dec θ1
  -> alg_to_dec θ2
  -> alg_to_dec (θ1 ++ θ2).
Proof. unfold alg_to_dec; intros. simpl+. destruct H. destruct H0. split; eauto. Qed.
