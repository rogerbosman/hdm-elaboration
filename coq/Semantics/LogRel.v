Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.
Require Import Defs.HdmLems.

Require Import Defs.E.
Require Import Defs.ELookup.
Require Import Defs.ERels.
Require Import Defs.Foralls.
Require Import Defs.List.
Require Import Defs.TmTy.
Require Import Defs.WfSTt.
Require Import Defs.Sub.
Require Import Defs.Subx.

Require Export Semantics.ClosedVals.
Require Export Semantics.gammaDef.
Require Export Semantics.Opsem.
Require Export Semantics.rhoDef.

From Equations Require Import Equations.

Import Coq.Relations.Relation_Definitions.

(*** Rel *)
Definition Rel (R:𝓡) (τ1 τ2:T) : Prop :=
  forall (v1 v2:Tm), R v1 v2 -> • ⊢t v1 ▸ (S__T τ1) /\ • ⊢t v2 ▸ (S__T τ2).

Definition in_Rel (p:T * T * 𝓡) : Prop :=
  let '((τ1,τ2),R) := p in Rel R τ1 τ2.
Definition mk_in_Rel [R:𝓡] [τ1 τ2:T] (rel:Rel R τ1 τ2) : in_Rel (τ1, τ2, R).
  crush. Defined.

(*** rho_elem_valid *)
#[derive(equations=no)] Equations rho_elem_valid (p:rho_elem) : Prop :=
  rho_elem_valid (τ1, τ2, R) := • ⊢wfτ τ1 /\ • ⊢wfτ τ2 /\ Rel R τ1 τ2.

Fact rho_elem_valid1 : forall τ1 τ2 R,
    rho_elem_valid (τ1, τ2, R)
  -> • ⊢wfτ τ1.
Proof. intros. unfolds. crush. Qed.
Fact rho_elem_valid2 : forall τ1 τ2 R,
    rho_elem_valid (τ1, τ2, R)
  -> • ⊢wfτ τ2.
Proof. intros. unfolds. crush. Qed.
Fact rho_elem_valid3 : forall τ1 τ2 R,
    rho_elem_valid (τ1, τ2, R)
  -> Rel R τ1 τ2.
Proof. intros. unfolds. crush. Qed.
#[export] Hint Resolve rho_elem_valid1 rho_elem_valid2 rho_elem_valid3 : core.


(*** Main logical relation *)
(** logrel_val *)

(** We distribute closed_vals in every case because we have to pattern match
immediately, I wish Equations had something like case such that we can go
logrel_val = closed_vals /\ case σ of, there are some things that kinda look
like this but it is weird with equalities, perhaps fixed by the convoy
pattern?*)
Equations logrel_val (σ:Sc) (ρ:rho) (t1 t2:Tm) : Prop by wf σ foralls_or_subterm :=
  logrel_val (S__Forall σ) ρ v1 v2 :=
      closed_vals (S__Forall σ) ρ v1 v2
    /\ exists t1 t2,
      v1 = t__TLam t1
    /\ v2 = t__TLam t2
    /\ forall τ1 τ2 R, exists L, forall α,
      α ∉ L
    -> rho_elem_valid (τ1, τ2, R)
    -> (* logrel_exp (open_Sc_wrt_T σ (T__Var_f α)) (((τ1, τ2, R), α) :: ρ) (open_Tm_wrt_T t1 τ1) (open_Tm_wrt_T t2 τ2) *)
      (** Inline def of logrel_exp because we cannot do mutual well-founded recursion (or can we? let me know!) *)
        • ⊢t open_Tm_wrt_T t1 τ1 ▸ ⟦(τ1, α) :: π1 ρ ▹ open_Sc_wrt_T σ (T__Var_f α)⟧
      /\ • ⊢t open_Tm_wrt_T t2 τ2 ▸ ⟦(τ2, α) :: π2 ρ ▹ open_Sc_wrt_T σ (T__Var_f α)⟧
      /\ exists v1 v2,
            open_Tm_wrt_T t1 τ1 ↦* v1
          /\ open_Tm_wrt_T t2 τ2 ↦* v2
          /\ logrel_val (open_Sc_wrt_T σ (T__Var_f α)) (((τ1, τ2, R), α) :: ρ) v1 v2;
  logrel_val (S__T (T__Var_b _)) ρ v1 v2 := False;
  logrel_val (S__T (T__Var_f α)) ρ v1 v2 :=
      closed_vals (S__T (T__Var_f α)) ρ v1 v2
    /\ match π__R ρ α with
      | None => False
      | (Some R) => R v1 v2
      end;
  logrel_val (S__T T__Unit) ρ v1 v2 :=
      closed_vals (S__T T__Unit) ρ v1 v2
    /\ v1 = t__Unit /\ v2 = t__Unit;
  logrel_val (S__T T__Bool) ρ v1 v2 :=
      closed_vals (S__T T__Bool) ρ v1 v2
    /\ ((v1 = t__True /\ v2 = t__True)
    \/  (v1 = t__False /\ v2 = t__False));
  logrel_val (S__T (T__Fun τ τ')) ρ v1 v2 :=
      closed_vals (S__T (T__Fun τ τ')) ρ v1 v2
    /\ exists t1 t2,
      v1 = t__Lam ⟦π1 ρ ▹ τ⟧ t1
    /\ v2 = t__Lam ⟦π2 ρ ▹ τ⟧ t2
    /\ forall (v1' v2':Tm),
      logrel_val (S__T τ) ρ v1' v2'
    -> (* logrel_exp τ' ρ (open_Tm_wrt_Tm t1 v1') (open_Tm_wrt_Tm t2 v2') *)
      (** Inline def of logrel_exp because we cannot do mutual well-founded recursion (or can we? let me know!) *)
        • ⊢t (open_Tm_wrt_Tm t1 v1') ▸ S__T ⟦π1 ρ ▹ τ'⟧
      /\ • ⊢t (open_Tm_wrt_Tm t2 v2') ▸ S__T ⟦π2 ρ ▹ τ'⟧
      /\ exists v1 v2,
            open_Tm_wrt_Tm t1 v1' ↦* v1
          /\ open_Tm_wrt_Tm t2 v2' ↦* v2
          /\ logrel_val (S__T τ') ρ v1 v2.
Obligation 1. crush. Qed.
Obligation 2. crush. Qed.
Obligation 3. apply decr_foralls. rewrite foralls_open_Sc_wrt_T. crush. Qed.
Notation "⦅ v1 × v2 ⦆ ∈ '𝒱' ⟦ σ ⟧ ρ" := (logrel_val σ ρ v1 v2) (at level 70, format "⦅ v1  ×  v2 ⦆  ∈  '𝒱' ⟦ σ ⟧  ρ").


Ltac destr_logrel_val H :=
    match type of H with
      | ex (fun (_ : T) => _ )  =>
          destruct H as [?τ1 [?τ2 [?R [?ρ' [?EQ [?RV [?NID H]]]]]]]
      | ex (fun (_ : Tm) => _ )  =>
          destruct H as [?v1 [?v2 [?γ' [?EQ [?VAL [?NID H]]]]]]
    end; subst.


(** logrel_exp *)
#[derive(equations=no)] Equations logrel_exp : Sc -> rho -> Tm -> Tm -> Prop :=
  logrel_exp σ ρ t1 t2 :=
    • ⊢t t1 ▸ ⟦π1 ρ ▹ σ⟧
  /\ • ⊢t t2 ▸ ⟦π2 ρ ▹ σ⟧
  /\ exists v1 v2,
        t1 ↦* v1
      /\ t2 ↦* v2
      /\ ⦅v1 × v2⦆ ∈ 𝒱⟦σ⟧ ρ.
Notation  "⦅ t1 × t2 ⦆ ∈ 'ℰ' ⟦ σ ⟧ ρ" := (logrel_exp σ ρ t1 t2) (at level 70, format "⦅ t1  ×  t2 ⦆  ∈  'ℰ' ⟦ σ ⟧  ρ").

(*** Logrel_e *)
Definition E_length' : E -> nat :=
  E_fold
    0
    (fun n a => plus (plus (length a) n) 1)
    (const ∘ const ∘ (plus 1))
    (const ∘ const ∘ const ∘ (plus 1)).

Definition E_length'_lt (ψ1 ψ2:E) := lt (E_length' ψ1) (E_length' ψ2).

#[local] Hint Constructors Acc : core.
Lemma well_founded'_E_length'_wf : forall len, forall σ, E_length' σ <= len -> Acc E_length'_lt σ.
  unfold E_length'_lt; induction len; crush.
Defined.
Theorem well_founded_E_length'_lt : well_founded E_length'_lt.
  red; intro; eapply well_founded'_E_length'_wf; eauto.
Defined.

#[export] Instance WellFounded_E_length'_lt : WellFounded E_length'_lt := { wellfounded := well_founded_E_length'_lt }.

Equations logrel_E (ρ:rho) (γ:gamma) (ψ:E) : Prop by wf ψ E_length'_lt :=
  logrel_E ρ γ • :=
      ρ = []
    /\ γ = [];
  logrel_E ρ γ (ψ ::x x :- σ) :=
      exists v1 v2 γ',
      γ = ((v1, v2), x) :: γ'
    /\ ⦅v1 × v2⦆ ∈ 𝒱⟦σ⟧ ρ
    /\ x ∉ dom_gamma γ'
    /\ logrel_E ρ γ' ψ;
  logrel_E ρ γ (ψ ::a []) :=
      logrel_E ρ γ ψ;
  logrel_E ρ γ (ψ ::a α :: a) :=
      exists τ1 τ2 R ρ',
      ρ = ((τ1, τ2, R, α) :: ρ')
    /\ rho_elem_valid (τ1, τ2, R)
    (* /\ α ∉ skvars_codom_Sub (π1 ρ') *)
    /\ α ∉ dom_rho ρ'
    /\ logrel_E ρ' γ (ψ ::a a);
  logrel_E ρ γ (ψ ::o ⦇_ ▸ ⟨_⟩ _⦈) :=
      logrel_E ρ γ (ψ).
Next Obligation. unfolds. simpl+. crush. Qed.
Next Obligation. unfolds. simpl+. crush. Qed.
Next Obligation. unfolds. simpl+. crush. Qed.
Next Obligation. unfolds. simpl+. crush. Qed.
Notation "⦅ ρ , γ ⦆ ∈ ⦅ '𝒟' , '𝒢' ⦆ ⟦ ψ ⟧" := (logrel_E ρ γ ψ) (at level 70, format "⦅ ρ ,  γ ⦆  ∈  ⦅ '𝒟' ,  '𝒢' ⦆ ⟦ ψ ⟧" ).
(*
⦅ρ, γ⦆ ∈ ⦅𝒟, 𝒢⦆ ⟦ψ⟧
 *)

Notation logrel_rho ρ ψ := (exists γ, ⦅ρ, γ⦆ ∈ ⦅𝒟, 𝒢⦆ ⟦ψ⟧).
Notation "ρ ∈ '𝒟' ⟦ ψ ⟧" := (logrel_rho ρ ψ) (at level 70).
  (* , format "⦅ ρ ,  γ ⦆  ∈  ⦅ `𝒟` ,  '𝒢' ⦆  ⟦ ψ ⟧" ). *)

(*** Lemmas *)
Ltac simp' :=
  simp logrel_val logrel_E.
Tactic Notation "simp'" "in" hyp(H) :=
  simp logrel_val logrel_E in H.
Tactic Notation "simp'" "in" "*" :=
  simp logrel_val logrel_E in *.

(** logrel_val *)
Fact props_logrel_val : forall v1 v2 σ ρ,
    ⦅v1 × v2⦆ ∈ 𝒱⟦σ⟧ ρ
  -> closed_vals σ ρ v1 v2.
Proof.
  introv REL. destruct σ; simp' in REL.
  destruct τ; simp' in REL; crush.
  crush.
Qed.
#[export] Hint Resolve props_logrel_val : core.

Lemma logrel_val_exp : forall v1 v2 σ ρ,
    ⦅v1 × v2⦆ ∈ 𝒱⟦σ⟧ ρ
  -> ⦅v1 × v2⦆ ∈ ℰ⟦σ⟧ ρ.
Proof.
  intros. unfolds. splits. 1,2:eauto.
  exists v1 v2. crush.
Qed.

Fact props_logrel_exp : forall t1 t2 σ ρ,
    ⦅t1 × t2⦆ ∈ ℰ⟦σ⟧ ρ
  -> • ⊢t t1 ▸ ⟦π1 ρ ▹ σ⟧
  /\ • ⊢t t2 ▸ ⟦π2 ρ ▹ σ⟧.
Proof. introv REL. simpl+ in REL. crush. Qed.
Corollary props_logrel_exp1 : forall t1 t2 σ ρ,
    ⦅t1 × t2⦆ ∈ ℰ⟦σ⟧ ρ
  -> • ⊢t t1 ▸ ⟦π1 ρ ▹ σ⟧.
Proof. apply props_logrel_exp. Qed.
Corollary props_logrel_exp2 : forall t1 t2 σ ρ,
    ⦅t1 × t2⦆ ∈ ℰ⟦σ⟧ ρ
  -> • ⊢t t2 ▸ ⟦π2 ρ ▹ σ⟧.
Proof. apply props_logrel_exp. Qed.
