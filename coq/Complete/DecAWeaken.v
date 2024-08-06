Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.
Require Import Defs.HdmLems.

(* Require Import Defs.E. *)
Require Import Defs.ERels.
Require Import Defs.List.
Require Import Defs.FrA.
Require Import Defs.OpenClose.
Require Import Defs.Sub.
Require Import Defs.Subst.
Require Import Defs.Rename.
(* Require Import Defs.WfSTt. *)

Require Import Defs.DecA.

Require Import Semantics.EquivRel.

(*** ERels *)

(*** Nominal weakening *)
(** Resulting in the same output *)
Lemma SubSumpTmA_E_A_sk_sub : forall ψ1 ψ2 t1 σ t2 τ a,
    SubSumpTmA ψ2 t1 σ t2 a τ
  -> ψ2 ⊆ψα ψ1
  -> E_sk_sub ψ1 ψ2
  -> SubSumpTmA ψ1 t1 σ t2 a τ.
Proof.
  introv SS SUB1 SUB2. gen ψ1. induction SS; intros. econstructor. FrA_L_sub.
  unfolds in SUB1. unfolds in SUB2.
  econstructor. FrA_L_sub. wfdec. eapply IHSS. reldec. reldec.
Qed.

Lemma DecA_weaken : forall ψ1 ψ2 e τ a t,
      ψ2 ⊢d' e ▸ ⟨a⟩ τ ⤳ t
    -> ψ2 ⊆ψα ψ1
    -> E_sk_sub ψ1 ψ2
    -> ψ1 =ψx ψ2
    -> ψ1 ⊢d' e ▸ ⟨a⟩ τ ⤳ t.
Proof.
  introv DECA SUB1 SUB2 EQ. unfolds in SUB1. unfolds in SUB2. unfolds in EQ. gen ψ1. induction DECA; intros.
  - econstructor. erewrite E_lookup_E_x_list_eq. eassumption. eassumption.
    eauto using SubSumpTmA_E_A_sk_sub.
  - econstructor. FrA_L_sub.
  - applys DecA__Abs L. eapply WfT_E_A_sk_sub. eassumption. reldec.
    introx. eapply H. fsetdec. reldec. reldec. crush.
    FrA_L_sub.
  - econstructor. eauto. eapply IHDECA2. reldec. reldec. crush.
  - applys DecA__Let L. eauto.
    introx. eapply H. fsetdec. reldec. reldec. crush.
Qed.

Corollary DecA_remove_obj : forall ψ t1 a1 σ e a2 τ t2,
    ψ ::o ⦇t1 ▸ ⟨a1⟩ σ⦈ ⊢d' e ▸ ⟨a2⟩ τ ⤳ t2
  -> ψ                  ⊢d' e ▸ ⟨a2⟩ τ ⤳ t2.
Proof. intros. applys DecA_weaken H; reldec. Qed.

(*** Renamable *)
Class Renamable (X : Type) := Rename_app : X -> Rename -> X.
Notation  "⟦ θ ↤ x ⟧"  := (Rename_app x θ) (at level 05, format "⟦ θ  ↤  x ⟧") : type_scope.

(** Rename_A *)
Definition Rename_A  : A -> Rename -> A := (fold_right (fun p a => {fst p ↤ snd p}a)).
(* Lemma Rename_A_rewr : forall a__in θ, Rename_A a__in θ = fold_right (fun p ψ => {fst p ↤ snd p}ψ) a__in θ. reflexivity. Qed. *)

#[export] Instance Renamable_A : Renamable A := { Rename_app := Rename_A }.

Lemma Rename_A_app1 : forall θ1 θ2 (a:A),
    ⟦(θ1 ++ θ2) ↤ a⟧ = ⟦θ1 ↤ ⟦θ2 ↤ a⟧⟧.
Proof.
  intro. ind_Rn θ1; intros. crush. simpl+.
  rewrite IHθ1. crush.
Qed.
#[export] Hint Rewrite Rename_A_app1 : sub_dist.

Lemma rename_skvar_A_app : forall α β (a1 a2:A),
    {β ↤ α}(a1 ++ a2) = ({β ↤ α}a1) ++ ({β ↤ α}a2).
Proof. intros. induction a2; simpl+; crush. Qed.

Lemma Rename_A_app2 : forall θ (a1 a2:A),
    ⟦θ ↤ (a1 ++ a2)⟧ = ⟦θ ↤ a1⟧ ++ ⟦θ ↤ a2⟧.
Proof.
  intro. ind_Rn θ; intros. crush. simpl+.
  rewrite IHθ. rewrite rename_skvar_A_app. crush.
Qed.
#[export] Hint Rewrite Rename_A_app2 : sub_dist.

(** Rename_E *)
Definition Rename_E : E -> Rename -> E := (fold_right (fun p ψ => {fst p ↤ snd p}ψ)).

#[export] Instance Renamable_E : Renamable E := { Rename_app := Rename_E }.


(* Lemma Rename_E_rewr : forall θ ψ__in, Rename_E θ ψ__in = fold_right (fun p ψ => {fst p ↤ snd p}ψ) ψ__in θ. reflexivity. Qed. *)

(* Lemma SubSumpTmRename : forall θ σ ψ t1 t2 a τ, *)
(*     SubSumpTm (ψ ::a a) t1 σ t2 τ *)
(*   -> SubSumpTm (Rename_E θ (ψ ::a a)) ⟦(Rename_lift θ) ▹ t1⟧ ⟦(Rename_lift θ) ▹ σ⟧ ⟦(Rename_lift θ) ▹ t2⟧ ⟦(Rename_lift θ) ▹ τ⟧. *)
(* Proof. *)
(*   intro θ. ind_Sub θ; introv SS. *)
(*   - simpl+. eassumption. *)
(*   - simpl+. dist. eapply SubSumpTm_rename_skvar_E. eauto. *)
(* Qed. *)

Lemma dom_Sub_Rename_lift : forall θ,
    dom_Sub (Rename_lift θ) ≡ varl (Rename_dom_list θ).
Proof. intros. ind_Sub θ; simpl+; fsetdec. Qed.
Lemma codom_Sub_Rename_lift : forall θ,
    skvars_codom_Sub (Rename_lift θ) ≡ varl (Rename_codom_list θ).
Proof. intros. ind_Sub θ; simpl+; fsetdec. Qed.
#[export] Hint Rewrite dom_Sub_Rename_lift codom_Sub_Rename_lift : core.

Lemma Rename_E_app1 : forall θ1 θ2 (ψ:E),
    ⟦(θ1 ++ θ2) ↤ ψ⟧ = ⟦θ1 ↤ ⟦θ2 ↤ ψ⟧⟧.
Proof.
  intro. ind_Rn θ1; intros. crush. simpl+.
  rewrite IHθ1. crush.
Qed.
#[export] Hint Rewrite Rename_E_app1 : sub_dist.

Lemma Rename_E_app2 : forall θ (ψ1 ψ2:E),
    ⟦θ ↤ (ψ1 +++ ψ2)⟧ = ⟦θ ↤ ψ1⟧ +++ ⟦θ ↤ ψ2⟧.
Proof.
  intro. ind_Rn θ; intros. crush. simpl+.
  rewrite IHθ. rewrite rename_skvar_E_app. crush.
Qed.
#[export] Hint Rewrite Rename_E_app2 : sub_dist.

Lemma Rename_E_onea : forall θ a,
    ⟦θ ↤ <a>a⟧ = <⟦θ ↤ a⟧>a.
Proof.
  intros. ind_Rn θ. crush. simpl+. rewrite IHθ. crush.
Qed.
#[export] Hint Rewrite Rename_E_onea : core.

Lemma Rename_E_consa : forall θ ψ a,
    ⟦θ ↤ (ψ ::a a)⟧ = ⟦θ ↤ ψ⟧ ::a ⟦θ ↤ a⟧.
Proof.
  intros. norm. rewrite Rename_E_app2. simpl+. crush.
Qed.
#[export] Hint Rewrite Rename_E_consa : sub_dist.

Lemma Rename_E_onex : forall θ x σ,
    ⟦θ ↤ <x :- σ>x⟧ = <x :- ⟦Rename_lift θ ▹ σ⟧>x.
Proof.
  intros. ind_Rn θ. crush. simpl+. rewrite IHθ. dist. crush.
Qed.
#[export] Hint Rewrite Rename_E_onex : core.

Lemma Rename_E_consx : forall θ ψ x σ,
    ⟦θ ↤ (ψ ::x x :- σ)⟧ = ⟦θ ↤ ψ⟧ ::x x :- ⟦Rename_lift θ ▹ σ⟧.
Proof.
  intros. norm. rewrite Rename_E_app2. simpl+. crush.
Qed.
#[export] Hint Rewrite Rename_E_consx : sub_dist.

(*** Rename skvar *)
(** Single *)
Lemma DecA_subst_skvar : forall α ψ e a τ t,
    ψ ⊢d' e ▸ ⟨a⟩ τ ⤳ t
  -> exists L, forall β, β ∉ L
  -> ({β ↤ α} ψ) ⊢d' e ▸ ⟨{β ↤ α}a⟩ {T__Var_f β ≔ α} τ ⤳ {T__Var_f β ≔ α} t.
Admitted.

Lemma rename_FrA : forall α β a ψ,
    a ### E_skvars ψ
  -> β ∉ E_skvars ψ ∪ varl a
  -> ({β ↤ α} a) ### E_skvars ({β ↤ α} ψ).
Proof.
  introv FR NI. ind_a a. crush.
  simpl+. eapply FrA_cons. split.
  eapply IHa. eapply FrA_cons. eassumption. simpl+ in NI. fsetdec.
  unfolds rename_var. if_dec.
  - rewrite rename_skvar_E_notin.
    2:eapply FrA_props2 in FR; simpl+ in FR; in_disj.
    rewrite rename_skvar_A_notin.
    2:eapply FrA_props1 in FR; simpl+ in FR; inverts FR; eauto.
    simpl+ in NI. fsetdec.
  - rewrite varl_rename_skvar_A_upper. rewrite E_skvars_rename_skvar_E_upper.
    destruct FR. simpl+ in *.
    eapply notin_union_iff; eapply notin_union_iff. in_disj. fsetdec.
    inverts H. crush. fsetdec.
Qed.

(** Rename *)
Lemma E_skvars_Rename_E_upper : forall θ ψ,
    E_skvars (⟦θ ↤ ψ⟧) ⊆ E_skvars ψ ∪ varl (Rename_codom_list θ).
Proof. introv. ind_Rn θ. crush. simpl+. rewrite E_skvars_rename_skvar_E_upper. fsetdec. Qed.

Lemma varl_Rename_A_upper : forall θ a,
    varl (⟦θ ↤ a⟧) ⊆ varl a ∪ varl (Rename_codom_list θ).
Proof. introv. ind_Rn θ. crush. simpl+. rewrite varl_rename_skvar_A_upper. fsetdec. Qed.

Lemma Rename_FrA : forall θ a ψ,
    a ### E_skvars ψ
  -> (Rename_codom_list θ) ### (E_skvars ψ ∪ varl a)
  -> ⟦θ ↤ a⟧ ### E_skvars ⟦θ ↤ ψ⟧.
Proof.
  introv FR1 FR2. ind_Rn θ. crush.
  simpl+. eapply rename_FrA. eapply IHθ. eapply FrA_cons. eassumption.
  simpl+ in FR2. eapply FrA_cons2 in FR2.
  rewrite E_skvars_Rename_E_upper. rewrite varl_Rename_A_upper. fsetdec.
Qed.

Lemma DecA_Rename : forall ψ e a τ t,
    ψ ⊢d' e ▸ ⟨a⟩ τ ⤳ t
  (* -> exists L, forall θ,  ⟦θ ↤ a⟧ ### L *)
  (* -> forall θ, ⟦θ ↤ a⟧ ### E_skvars ⟦θ ↤ ψ⟧ *)
  -> forall θ, Rename_codom_list θ ### (E_skvars ψ ∪ varl a)
  -> ⟦θ ↤ ψ⟧ ⊢d' e ▸ ⟨⟦θ ↤ a⟧⟩ ⟦(Rename_lift θ) ▹ τ⟧ ⤳ ⟦(Rename_lift θ) ▹ t⟧.
Proof.
  introv DEC FR. induction DEC.
  - econstructor. applys_eq IN. admit. admit.
  - simpl+. econstructor. eauto using Rename_FrA.
Admitted.

(*** Rename *)
Fact fresh_rename : forall a L,
    exists θ,
      a = (Rename_dom_list θ)
    /\ ⟦θ ↤ a⟧ ### L.
Admitted.

Fact fresh_rename' : forall a L,
    exists θ,
      a = (Rename_dom_list θ)
    /\ (Rename_codom_list θ) ### L.
Admitted.

Fact Rename_A_full : forall θ,
    ⟦θ ↤ Rename_dom_list θ⟧ = Rename_codom_list θ.
Admitted.
#[export] Hint Rewrite Rename_A_full : core.

(*** Renamed weakening *)
Lemma DecA_weaken' : forall L ψ1 ψ2 e τ a t,
      ψ2 ⊢d' e ▸ ⟨a⟩ τ ⤳ t
    -> ψ2 ⊆ψα ψ1
    -> ψ1 =ψx ψ2
    (* -> wf(ψ2) *)
    -> exists (θ:Rename),
        Rename_dom_list θ = a
      /\ (Rename_codom_list θ) ### (varl a ∪ L)
      /\ ψ1 ⊢d' e ▸ ⟨⟦θ ↤ a⟧⟩ ⟦(Rename_lift θ) ▹ τ⟧ ⤳ ⟦(Rename_lift θ) ▹ t⟧.
Proof.
  introv DEC SUB1 SUB2. unfolds in SUB1. unfolds in SUB2. forwards E: DecA_lc DEC. gen ψ1 ψ2 τ a t0.
  induction E; intros; inverts DEC.
  - forwards [θ [EQ__dom EQ__codom]]: fresh_rename' a (E_skvars ψ1 ∪ varl a ∪ L).
    exists θ. splits. crush. subst. FrA_L_sub. econstructor. applys_eq IN. crush.
    admit.

  - forwards [θ [EQ__dom EQ__codom]]: fresh_rename' a (E_skvars ψ1 ∪ varl a ∪ L).
    exists θ. splits. crush. subst. FrA_L_sub. simpl+. econstructor. subst. simpl+. FrA_L_sub.

  - admit.

  - forwards [θ1 [EQ__dom1 EQ__codom1]]: fresh_rename' a1 (((varl a1 ∪ E_skvars ψ2) ∪ fsk_T τ1) ∪ varl a2).
    freshx L0. specializes DEC0 x. specializes DEC0. fsetdec.
    specializes H0 (ψ1 ::a Rename_codom_list θ1 ::x x :- S__T ⟦Rename_lift θ1 ▹ τ1⟧) (ψ2 ::a Rename_codom_list θ1 ::x x :- S__T ⟦Rename_lift θ1 ▹ τ1⟧).
      specializes H0. reldec. simpl+. clear - SUB2. crush.
      forwards: DecA_Rename θ1. eassumption. applys FrA_L_sub. eassumption. simpl+. crush.
      dist in H0. applys_eq H0. fequals. fequals. admit. admit.
    destruct H0 as [θ2 [EQ__dom [EQ__codom DECA']]].
    (**)
    exists (θ2 ++ θ1). splits. 1,2:admit. dist. applys DecA__Abs empty. admit.
    introy. asserts_rewrite (y = x). admit.
    applys_eq DECA'. fequals. fequals. admit. fequals. admit. simpl+. reflexivity. admit.
Admitted.

Corollary DecA_add_obj : forall ψ t1 a1 σ e a2 τ t2,
    ψ                  ⊢d' e ▸ ⟨a2⟩ τ ⤳ t2
  -> exists a2' τ' t2',
      ψ ::o ⦇t1 ▸ ⟨a1⟩ σ⦈ ⊢d' e ▸ ⟨a2'⟩ τ' ⤳ t2'
    /\ (∀ a2'⬪ S__T τ') = (∀ a2⬪ S__T τ)
    /\ (Λ a2'⬪ t2') = (Λ a2⬪ t2).
Proof.
  introv DEC.
  forwards [θ [?EQ [?EQ DEC']]]: DecA_weaken' (fv__α(S__T τ) ∪ fv__α(t2)) (ψ ::o ⦇t1 ▸ ⟨a1⟩ σ⦈) DEC; try reldec.
  forwards: Rename_gen_T θ (S__T τ). subst. FrA_L_sub.
  forwards: Rename_gen_Tm θ t2. subst. FrA_L_sub.
  exists. splits. eassumption. crush. crush.
Qed.

(*** E_x_ss *)
(* Definition E_x_list := E_fold [] const (fun acc x σ => (x, σ) :: acc) const3. *)

(* Definition E_x_list_eq : relation E := fun ψ1 ψ2 => E_x_list ψ1 = E_x_list ψ2. *)
Axiom E_x_ss : relation E.
Notation  "ψ1 ⊆ψx ψ2"  := (E_x_ss ψ1 ψ2) (at level 70).
#[export] Hint Unfold E_x_ss : defs rels.


(*** Renamed weakening *)
(* Lemma DecA_weaken' : forall ψ1 ψ2 e τ a t, *)
(*       ψ2 ⊢d' e ▸ ⟨a⟩ τ ⤳ t *)
(*     -> ψ2 ⊆ψα ψ1 *)
(*     -> ψ1 ⊆ψx ψ2 *)
(*     (* -> wf(ψ2) *) *)
(*     -> exists (θ:Rename) a' t', *)
(*         a = (Rename_dom_list θ) *)
(*       /\ a' = (Rename_dom_list θ) *)
(*       /\ ψ1 ⊢d' e ▸ ⟨a'⟩ ⟦(Rename_lift θ) ▹ τ⟧ ⤳ t' *)
(*       /\ ψ1 ⊢t≈ (Λ a⬪ t) ≈ (Λ a'⬪ t') ▸ (∀ a⬪ S__T τ). *)
(* crush. *)
