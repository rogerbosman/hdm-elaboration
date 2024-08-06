Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.
Require Import Defs.HdmLems.

Require Import Defs.Lc.
Require Import Defs.List.
Require Export Defs.Freevars.
Require Export Defs.Subst.

Require Export Defs.WfSTt.
(* Require Export Defs.Sub. *)

(*** Def *)
Class Subx_appable (X : Type) := Subx_app : X -> Subx -> X.
Notation  "⟦ θ ▹__x x ⟧"  := (Subx_app x θ) (at level 05, format "⟦ θ  ▹__x  x ⟧") : type_scope.

Definition Subx_app_Tm : Tm -> Subx -> Tm := fold_right (uncurry subst__x).
#[export] Instance Subx_appable_Tm : Subx_appable Tm := { Subx_app := Subx_app_Tm }.

(*** Tactics 1 *)
Ltac ind_Subx θ := induction θ as [|[?t ?x] ?θ].
Ltac ind_Subx_rev θ := induction θ as [|[?t ?x] ?θ] using rev_ind.

(*** Definitions *)
(* Definition full_Subx (θ:Subx) (τ:T) := fv__α(τ) ⊆ dom_Subx θ. *)
(* #[export] Hint Unfold full_Subx : defs. *)

(* Definition wf_Subx (ψ:E) (θ:Subx) := forall (τ:T), τ ∈τ (codom_Subx θ) -> WfT ψ τ. *)
(* Notation "ψ ⊢θ θ" := (wf_Subx ψ θ) (at level 70). *)
(* #[export] Hint Unfold wf_Subx : defs. *)

(* Notation Subx_to_A θ := (map snd θ). *)

(*** Subx_app_dist *)
(** Subx distribution *)
(* T *)
(* Theorem Subx_app_T_cons : forall (τ1 τ2:T) (α:skvar) (θ:Subx), *)
(*     ⟦(τ1, α) :: θ ▹__x τ2⟧ = {τ1 ≔ α} ⟦θ ▹__x τ2⟧. *)
(* Proof. reflexivity. Qed. *)
(* #[export] Hint Rewrite Subx_app_T_cons : sub_dist. *)

(* Theorem Subx_app_T_app : forall (τ:T) (θ1 θ2:Subx), *)
(*     ⟦θ1 ++ θ2 ▹__x τ⟧ = ⟦θ1 ▹__x ⟦θ2 ▹__x τ⟧⟧. *)
(* Proof. introv. ind_Subx θ1; crush; dist; crush. Qed. *)
(* #[export] Hint Rewrite Subx_app_T_app : sub_dist. *)

(* (* Sc *) *)
(* Fact Subx_app_Sc_cons : forall (σ:Sc) (τ:T) (α:skvar) (θ:Subx), *)
(*     ⟦(τ, α) :: θ ▹__x σ⟧ = {τ ≔ α} ⟦θ ▹__x σ⟧. *)
(* Proof. introv. induction σ; cbn; crush. Qed. *)
(* #[export] Hint Rewrite Subx_app_Sc_cons : sub_dist. *)

(* Fact Subx_app_Sc_app : forall (σ:Sc) (θ1 θ2:Subx), *)
(*     ⟦θ1 ++ θ2 ▹__x σ⟧ = ⟦θ1 ▹__x ⟦θ2 ▹__x σ⟧⟧. *)
(* Proof. introv. ind_Subx θ1; crush; dist; crush. induction σ; cbn; crush. Qed. *)
(* #[export] Hint Rewrite Subx_app_Sc_app : sub_dist. *)

(* t *)
Theorem Subx_app_t_cons : forall (t t':Tm) (x:var) (θ:Subx),
    ⟦(t, x) :: θ ▹__x t'⟧ = {t ≔__x x} ⟦θ ▹__x t'⟧.
Proof. reflexivity. Qed.
#[export] Hint Rewrite Subx_app_t_cons : sub_dist.

Theorem Subx_app_t_app : forall (t:Tm) (θ1 θ2:Subx),
    ⟦θ1 ++ θ2 ▹__x t⟧ = ⟦θ1 ▹__x ⟦θ2 ▹__x t⟧⟧.
Proof. introv. ind_Subx θ1; crush; dist; crush. Qed.
#[export] Hint Rewrite Subx_app_t_app : sub_dist.

(*** Notin *)
Fact Subx_app_Tm_notindom : forall (θ:Subx) (t:Tm),
    fv__x(t) ∐ dom_Subx θ
  -> ⟦θ ▹__x t⟧ = t.
Proof.
  introv DISJ. ind_Subx θ. crush. dist. rewrite IHθ. 2:disj_sub.
  apply subst_tvar_Tm_notin. in_disj.
Qed.

Ltac Subx_notin' :=
  match goal with
    | [ |- context[Subx_app ?x ?θ] ]  =>
        match type of x with
        (* | Sc => rewrite Sub_app_Sc_notindom *)
        (* | T  => rewrite Sub_app_T_notindom *)
        | Tm => rewrite Subx_app_Tm_notindom
        end; try reflexivity
  end.
Ltac Subx_notin := Subx_notin'; try solve [fsetdec+|crush].

(*** lcx *)
Lemma lcx_Subx_empty :
    lc__x(([]:Subx)).
Proof. do 2 unfolds. introv IN. simpl+ in IN. crush. Qed.
#[export] Hint Resolve lcx_Subx_empty : core.

Lemma lc_Subx_app : forall (θ1 θ2:Subx),
    lc__x(θ1)
  /\ lc__x(θ2)
  <-> lc__x(θ1 ++ θ2).
Proof.
  intros. unfold lc__x in *. unfold lcable_Subx in *.
  split.
  - intros. destruct H. simpl+ in H0. destr_union.
    apply H. crush.
    apply H1. crush.
  - intros. split; intros; apply H; simpl+; fsetdec'.
Qed.

Fact lc_Subx_app_l : forall (θ1 θ2:Subx),
    lc__x(θ1 ++ θ2)
  -> lc__x(θ1).
Proof. apply lc_Subx_app. Qed.
Fact lc_Subx_app_r : forall (θ1 θ2:Subx),
    lc__x(θ1 ++ θ2)
  -> lc__x(θ2).
Proof. apply lc_Subx_app. Qed.
Fact lc_Subx_cons_destr_l : forall (θ:Subx) α t,
    lc__x((t, α) :: θ)
  -> lc(t).
Proof.
  intros. unfold lc__x in *. unfold lcable_Subx in *.
  intros. apply H. simpl+. clfsetdec'.
Qed.
Fact lc_Subx_cons_destr_r : forall θ τα,
    lc__x(τα :: θ)
  -> lc__x(θ).
Proof.
  intros. unfold lc__x in *. unfold lcable_Subx in *.
  intros. apply H. simpl+. fsetdec'.
Qed.
#[export] Hint Rewrite lc_Subx_app : core.
#[export] Hint Resolve lc_Subx_app_l lc_Subx_app_r lc_Subx_cons_destr_l lc_Subx_cons_destr_r : core.

(*** Subx_app_simpl *)
(** Subx_app_T *)
(* Section Subx_app_T_simpl. *)
(*   Variable (θ:Subx). *)
(*   Lemma Subx_app_T_id : forall (τ:T), *)
(*       (forall (τ':T) (α:skvar), { τ' ≔ α } τ = τ) *)
(*     -> ⟦θ ▹__x τ⟧ = τ. *)
(*   Proof. introv. induction θ; crush. dist. crush. Qed. *)
(*   #[local] Hint Rewrite Subx_app_T_id : core. *)

(*   Fact Subx_app_T_Skvar_b : forall (n:nat), *)
(*       ⟦θ ▹__x T__Var_b n⟧ = T__Var_b n. *)
(*   Proof. crush. Qed. *)

(*   Fact Subx_app_T_Unit : *)
(*       ⟦θ ▹__x T__Unit⟧ = T__Unit. *)
(*   Proof. crush. Qed. *)

(*   Fact Subx_app_T_Fun : forall (τ1 τ2:T), *)
(*       ⟦θ ▹__x T__Fun τ1 τ2⟧ = T__Fun ⟦θ ▹__x τ1⟧ ⟦θ ▹__x τ2⟧. *)
(*   Proof. induction θ; crush. dist. crush. Qed. *)

(*   Fact Subx_app_T_nil : forall (τ:T), *)
(*       ⟦[] ▹__x τ⟧ = τ. *)
(*   Proof. crush. Qed. *)
(* End Subx_app_T_simpl. *)
(* #[export] Hint Rewrite Subx_app_T_Skvar_b Subx_app_T_Unit Subx_app_T_Fun : core. *)
(* #[export] Hint Rewrite Subx_app_T_nil : core. *)

(** Subx_app_Sc *)
(* Section Subx_app_Sc_simpl. *)
(*   Variable (θ:Subx). *)
(*   Fact Subx_app_Sc_nil : forall (σ:Sc), *)
(*     ⟦[] ▹__x σ⟧ = σ. *)
(*   Proof. induction σ; cbn; crush. Qed. *)
(* End Subx_app_Sc_simpl. *)
(* #[export] Hint Rewrite Subx_app_Sc_nil : core. *)

(** Subx_app_Tm *)
Section Subx_app_Tm_simpl.
  Variable (θ:Subx).
  Lemma Subx_app_Tm_id : forall (t:Tm),
      (forall (t':Tm) (x:var), { t' ≔__x x } t = t)
    -> ⟦θ ▹__x t⟧ = t.
  Proof. introv. induction θ; cbn; crush. Qed.
  #[local] Hint Resolve Subx_app_Tm_id : core.

  Fact Subx_app_Tm_Tvar_b : forall (n:nat),
      ⟦θ ▹__x t__Var_b n⟧ = t__Var_b n.
  Proof. crush. Qed.

  (* Fact Subx_app_Tm_Tvar_f : forall (x:var), *)
  (*     ⟦θ ▹__x t__Var_f x⟧ = t__Var_f x. *)
  (* Proof. crush. Qed. *)

  Fact Subx_app_Tm_Unit :
      ⟦θ ▹__x t__Unit⟧ = t__Unit.
  Proof. crush. Qed.

  Fact Subx_app_Tm_True :
      ⟦θ ▹__x t__True⟧ = t__True.
  Proof. crush. Qed.

  Fact Subx_app_Tm_False :
      ⟦θ ▹__x t__False⟧ = t__False.
  Proof. crush. Qed.

  Fact Subx_app_Tm_App : forall t1 t2,
      ⟦θ ▹__x t__App t1 t2⟧ = t__App ⟦θ ▹__x t1⟧ ⟦θ ▹__x t2⟧.
  Proof. introv. induction θ; cbn; crush. Qed.

  Fact Subx_app_Tm_TApp : forall t τ,
      ⟦θ ▹__x t__TApp t τ⟧ = t__TApp ⟦θ ▹__x t⟧ τ.
  Proof. introv. induction θ; cbn; crush. Qed.

  Fact Subx_app_Tm_Lam : forall (τ:T) (t:Tm),
      ⟦θ ▹__x t__Lam τ t⟧ = t__Lam τ ⟦θ ▹__x t⟧.
  Proof. induction θ; crush. dist. crush. Qed.

  Fact Subx_app_Tm_TLam : forall (t:Tm),
      ⟦θ ▹__x t__TLam t⟧ = t__TLam ⟦θ ▹__x t⟧.
  Proof. induction θ; crush. dist. crush. Qed.

End Subx_app_Tm_simpl.
#[export] Hint Rewrite Subx_app_Tm_Tvar_b (* Subx_app_Tm_Tvar_f *) Subx_app_Tm_Unit : core.
#[export] Hint Rewrite Subx_app_Tm_True Subx_app_Tm_False : core.
#[export] Hint Rewrite Subx_app_Tm_App Subx_app_Tm_TApp Subx_app_Tm_Lam Subx_app_Tm_TLam : core.
(* #[export] Hint Rewrite Subx_app_Tm_open_Tm_wrt_Tm : core. *)


(*** open comm *)
 Lemma Subx_app_open_Tm_wrt_T : forall θ t τ,
    lc__x(θ)
  -> ⟦θ ▹__x open_Tm_wrt_T t τ⟧ = open_Tm_wrt_T ⟦θ ▹__x t⟧ τ.
Proof.
  introv LC. ind_Subx θ. crush.
  simpl+. rewrite IHθ. rewrite subst_tvar_Tm_open_Tm_wrt_T. reflexivity.
  apply LC. simpl+. fsetdec'. eauto.
Qed.

Lemma Subx_app_open_Tm_wrt_Tm : forall θ t1 t2,
    lc__x(θ)
  -> dom_Subx θ ∐ fv__x(t2)
  -> ⟦θ ▹__x open_Tm_wrt_Tm t1 t2⟧ = open_Tm_wrt_Tm ⟦θ ▹__x t1⟧ t2.
Proof.
  introv LC DISJ. ind_Subx θ. crush. simpl+.
  rewrite IHθ. 2:eauto. 2:disj_sub.
  rewrite subst_tvar_Tm_open_Tm_wrt_Tm. 2:apply LC; simpl+; clfsetdec.
  fequals. apply subst_tvar_Tm_notin. simpl+ in DISJ. in_disj.
Qed.
