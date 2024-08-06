Set Warnings "-notation-overridden".
Require Import Preamble.

Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.

Definition is_val (t:Tm) : Prop :=
  match t with
  ( t__Var_b _
  | t__Var_f _
  | t__Unit
  | t__True
  | t__False
  | t__Lam _ _
  | t__TLam _) => True
  | _ => False
  end.

Inductive EC : Set :=
  (* [] *)
  | EC__Hole
  (* EC t *)
  | EC__AppL (ec:EC) (t:Tm)
  (* v EC *)
  | EC__AppR (v:Tm) (_:is_val v) (ec:EC)
  (* EC [τ] *)
  | EC__TApp (ec:EC) (τ:T).

Fixpoint fill_EC (ec:EC) (t:Tm) : Tm :=
  match ec with
    (* [] *)
    | EC__Hole => t
    (* EC t *)
    | (EC__AppL ec t') => t__App (fill_EC ec t) t'
    (* v EC *)
    | (EC__AppR v _ ec) => t__App v (fill_EC ec t)
    (* EC [τ] *)
    | (EC__TApp ec τ) => t__TApp (fill_EC ec t) τ
    end.

Inductive t_ss_opsem : relation Tm :=
  | t_ss__App : forall (τ:T) (t:Tm) (v:Tm) (_:is_val v),
      t_ss_opsem (t__App (t__Lam τ t) v) (open_Tm_wrt_Tm t v)
  | t_ss__TApp : forall (t:Tm) (τ:T),
      t_ss_opsem (t__TApp (t__TLam t) τ) (open_Tm_wrt_T t τ)
  | t_ss__EC : forall (ec:EC) (t t':Tm),
      t_ss_opsem t t'
    -> t_ss_opsem (fill_EC ec t) (fill_EC ec t').
#[export] Hint Constructors t_ss_opsem : core.

Notation  "t ↦ t'" := (t_ss_opsem t t') (at level 70) : type_scope.

Notation t_cl_opsem := (clos_refl_trans_1n Tm t_ss_opsem).
#[export] Hint Constructors clos_refl_trans_1n : core.
Notation  "t ↦* t'" := (t_cl_opsem t t') (at level 70) : type_scope.

Notation t_cl_rev_opsem := (clos_refl_trans_n1 Tm t_ss_opsem).
#[export] Hint Constructors clos_refl_trans_n1 : core.
Notation  "t ↦*' t'" := (t_cl_rev_opsem t t') (at level 70) : type_scope.

Lemma t_cl_opsem_t_cl_rev_opsem : forall t t',
    t ↦*  t'
  <-> t ↦*' t'.
Proof.
  intros. split; intros.
  apply clos_rt_rtn1_iff. apply clos_rt_rt1n_iff. assumption.
  apply clos_rt_rt1n_iff. apply clos_rt_rtn1_iff. assumption.
Qed.

Fact t_cl_opsem_refl  : Reflexive t_cl_opsem.
  autounfold. intro x. crush. Qed.
Fact t_cl_opsem_trans : Transitive t_cl_opsem.
  autounfold. introv STEP1. induction STEP1; eauto. Qed.

#[export] Instance Preorder_t_cl_opsem : PreOrder t_cl_opsem :=
  { PreOrder_Reflexive  := t_cl_opsem_refl
  ; PreOrder_Transitive := t_cl_opsem_trans
  }.

(*** Lemmas *)
Fact t_ss__EC_refl_trans : forall EC t' t,
    t ↦* t'
  -> (fill_EC EC t) ↦* (fill_EC EC t').
Proof. introv SS. induction SS; eauto. Qed.

Fact make_EC_t__AppL : forall t1 t2,
    fill_EC (EC__AppL EC__Hole t2) t1 = t__App t1 t2.
Proof. intros. crush. Qed.

Fact make_EC_t__AppR : forall v1 (iv:is_val v1) t2,
    fill_EC (EC__AppR v1 iv EC__Hole) t2 = t__App v1 t2.
Proof. intros. crush. Qed.

Fact make_EC_t__TApp : forall t τ,
    fill_EC (EC__TApp EC__Hole τ) t = t__TApp t τ.
Proof. intros. crush. Qed.


(** Alt opsem *)
Inductive t_ss'_opsem : relation Tm :=
  | t_ss'__App : forall (τ:T) (t:Tm) (v:Tm) (_:is_val v),
      t_ss'_opsem (t__App (t__Lam τ t) v) (open_Tm_wrt_Tm t v)
  | t_ss'__TApp : forall (t:Tm) (τ:T),
      t_ss'_opsem (t__TApp (t__TLam t) τ) (open_Tm_wrt_T t τ)
  | t_ss'_cong__AppL : forall (t1 t1' t2:Tm),
      t_ss'_opsem t1 t1'
    -> t_ss'_opsem (t__App t1 t2) (t__App t1' t2)
  | t_ss'_cong__AppR : forall (v t2 t2':Tm) (_:is_val v),
      t_ss'_opsem t2 t2'
    -> t_ss'_opsem (t__App v t2) (t__App v t2')
  | t_ss'_cong__TApp : forall (t t':Tm) (τ:T),
      t_ss'_opsem t t'
    -> t_ss'_opsem (t__TApp t τ) (t__TApp t' τ).
#[export] Hint Constructors t_ss'_opsem : core.

Notation  "t ⇾ t'" := (t_ss'_opsem t t') (at level 70) : type_scope.

Lemma t_ss_t_ss'_opsem : forall t t',
    t ↦ t'
  <-> t ⇾ t'.
Proof.
  split.
  - intro OP; induction OP; eauto.
    induction ec; simpl+; eauto.
  - intro OP; induction OP; eauto.
    + applys_eq (t_ss__EC (EC__AppL EC__Hole t2)). eassumption.
    + applys_eq (t_ss__EC (EC__AppR v H EC__Hole)). eassumption.
    + applys_eq (t_ss__EC (EC__TApp EC__Hole τ)). eassumption.
Qed.

Lemma val_does_not_step : forall v t,
    is_val v
  -> v ↦ t
  -> False.
Proof.
  introv IV STEP. induction STEP. inverts IV. inverts IV.
  destruct ec; simpl+ in IV. crush. crush. crush. crush.
Qed.

Lemma val_does_not_step' : forall v t,
    is_val v
  -> v ⇾ t
  -> False.
Proof. introv IV OP. inverts OP; inverts IV. Qed.

Lemma t_ss'_deterministic : forall t t1,
    t ⇾ t1
  -> forall t2, t ⇾ t2
  -> t1 = t2.
Proof.
  introv OP1. induction OP1.
  - introv OP2. inverts OP2. crush. inverts H3.
    false. eauto using val_does_not_step'.
  - introv OP2. inverts OP2. crush. inverts H2.
  - introv OP2. inverts OP2. inverts OP1.
    specializes IHOP1 H2. crush.
    false. eauto using val_does_not_step'.
  - introv OP2. inverts OP2.
    false. eauto using val_does_not_step'.
    false. eauto using val_does_not_step'.
    specializes IHOP1 H4. crush.
  - introv OP2. inverts OP2. inverts OP1.
    specializes IHOP1 H2. crush.
Qed.

Lemma t_ss_deterministic : forall t t1 t2,
    t ↦ t1
  -> t ↦ t2
  -> t1 = t2.
Proof. intros. eapply t_ss'_deterministic; eapply t_ss_t_ss'_opsem; eassumption. Qed.


Lemma t_cl_deterministic : forall t v1 v2,
    t ↦* v1
  -> t ↦* v2
  -> is_val v1
  -> is_val v2
  -> v1 = v2.
Proof.
  introv OP1. gen v2. induction OP1; introv OP2 IV1 IV2; inverts OP2.
  - crush.
  - false. eauto using val_does_not_step.
  - false. eauto using val_does_not_step.
  - forwards EQ: t_ss_deterministic H H0. subst. eauto.
Qed.
