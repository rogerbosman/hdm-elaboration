Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.
Require Import Defs.HdmLems.

(* Require Import Defs.ELookup. *)
Require Import Defs.ERels.
Require Import Defs.Dec.
Require Import Defs.List.
Require Import Defs.FrA.
Require Import Defs.OpenClose.
(* Require Import Defs.Sub. *)
(* Require Import Defs.SubSump. *)

(*** Notation *)
Notation  "ψ ⊢d' e ▸ ⟨ a ⟩ τ ⤳ t" := (DecA ψ e a τ t) (at level 70, format "ψ  ⊢d'  e  ▸  ⟨ a ⟩  τ  ⤳  t" ) : type_scope.


Fact DecA_lc : forall ψ e a τ t,
    ψ ⊢d' e ▸ ⟨a⟩ τ ⤳ t
  -> lc(e).
Admitted.

Lemma DecA_FrA : forall ψ e a τ t,
    ψ ⊢d' e ▸ ⟨a⟩ τ ⤳ t
  -> a ### E_skvars ψ.
Admitted.
#[export] Hint Resolve DecA_FrA : core.

Lemma DecA_Freshen_A : forall ψ e a τ t,
    ψ ⊢d' e ▸ ⟨a⟩ τ ⤳ t
  -> forall L, exists a' θ,
      a' ### L
    /\ ψ ⊢d' e ▸ ⟨a'⟩ ⟦θ ▹ τ⟧ ⤳ ⟦θ ▹ t⟧
    /\ (∀ a ⬪ (S__T τ)) = (∀ a' ⬪ S__T (⟦θ ▹ τ⟧))
    /\ Λ a ⬪ t = Λ a' ⬪ ⟦θ ▹ t⟧.
Admitted.

Lemma SubSumpTmA_SubSumpTm : forall ψ t1 σ t2 a τ,
    SubSumpTmA ψ t1 σ t2 a τ
  -> SubSumpTm (ψ ::a a) t1 σ t2 τ.
Proof.
  introv SSA. induction SSA. crush. econstructor. applys WfT_E_A_sk_sub WFT. erel_fsetdec.
  applys SubSumpTm_E_A_sk_sub IHSSA. erel_fsetdec.
Qed.

Theorem DecA_Dec : forall ψ e a τ t,
    ψ ⊢d' e ▸ ⟨a⟩ τ ⤳ t
  -> ψ ::a a ⊢d e ▸ τ ⤳ t.
Proof.
  introv DEC'. forwards E: DecA_lc DEC'. gen ψ a τ t0. induction E; intros; inverts DEC'.
  - econstructor. eassumption. eauto using SubSumpTmA_SubSumpTm.
  - eauto.
  - econstructor.
    specializes IHE1 DEC1. applys Dec_weaken IHE1. erel_fsetdec. erel_crush.
    specializes IHE2 DEC2. applys Dec_weaken IHE2. erel_fsetdec. erel_crush.
  - applys Dec__Abs L. eapply WfT_E_A_sk_sub. eassumption. erel_fsetdec.
    intros x NIL__x. specializes DEC NIL__x. specializes H0 DEC.
    applys Dec_weaken H0. erel_fsetdec. erel_crush.
  - forwards [a1' [θ [FR [DEC1' [EQ1 EQ2]]]]]: DecA_Freshen_A DEC1. rewrite EQ2.
    specializes IHE DEC1'.
    applys Dec__Let L. applys Dec_weaken IHE. erel_fsetdec. erel_crush.
    intros α NIL__α. specializes DEC2 NIL__α. specializes H0 DEC2.
    applys Dec_weaken H0. erel_fsetdec. erel_crush. eassumption.
Qed.

Notation E_sk_eq := M_E_skvars.R__eq.
#[export] Hint Unfold E_sk_eq : defs rels.

Notation E_A_sk_eq := M_E_A_skvars.R__eq.
#[export] Hint Unfold E_sk_eq : defs rels.

Lemma SubSumpTmA_E_A_sk_sub : forall ψ1 ψ2 t1 σ t2 τ a,
    SubSumpTmA ψ1 t1 σ t2 a τ
  -> E_sk_eq ψ1 ψ2
  -> E_A_sk_eq ψ1 ψ2
  -> SubSumpTmA ψ2 t1 σ t2 a τ.
Proof.
  introv SSA. gen ψ2. induction SSA; introv EQ1 EQ2; unfolds in EQ1; unfolds in EQ2.
  - econstructor. applys FrA_L_sub FR. erel_fsetdec.
  - econstructor. applys FrA_L_sub FR. erel_fsetdec.
    applys WfT_E_A_sk_sub WFT. erel_fsetdec.
    applys IHSSA. erel_fsetdec. erel_fsetdec.
Qed.

Lemma SubSumpTm_SubSumpTmA : forall ψ t1 σ t2 a τ,
    SubSumpTm (ψ ::a a) t1 σ t2 τ
  -> SubSumpTmA (ψ ::a a) t1 σ t2 [] τ.
Proof.
  introv SS. induction SS. crush. applys_eq SSTA__L. instantiate (1 := []). simpl+. crush. auto.
  applys WfT_E_A_sk_sub WFT. erel_fsetdec.
  applys SubSumpTmA_E_A_sk_sub IHSS; erel_fsetdec.
Qed.

Lemma DecA_weaken : forall ψ1 ψ2 e τ a t,
      ψ1 ⊢d' e ▸ ⟨a⟩ τ ⤳ t
    -> E_sk_eq ψ1 ψ2
    -> E_A_sk_eq ψ1 ψ2
    -> ψ1 =ψx ψ2
    -> ψ2 ⊢d' e ▸ ⟨a⟩ τ ⤳ t.
Proof.
  introv DEC EQ__α1 EQ__α2 EQ__x. gen ψ2. induction DEC; intros; unfolds in EQ__α1; unfolds in EQ__α2.
  - econstructor. erewrite E_lookup_E_x_list_eq. eassumption. crush.
    applys SubSumpTmA_E_A_sk_sub SS. erel_fsetdec. erel_fsetdec.
  - econstructor. rewrite <- EQ__α1. crush.
  - econstructor. applys WfT_E_A_sk_sub WFT. erel_fsetdec.
    intros x NIL__x. eapply H. eassumption. erel_fsetdec. erel_fsetdec. erel_crush.
    rewrite <- EQ__α1. crush.
  - econstructor. eauto. eapply IHDEC2. erel_fsetdec. erel_fsetdec. erel_crush.
  - econstructor. eauto.
    intros x NIL__x. eapply H. eassumption. erel_fsetdec. erel_fsetdec. erel_crush.
Qed.

(* Lemma DecA_shift : forall ψ a1 e a2 τ t, *)
(*     ψ ::a a1 ⊢d' e ▸ ⟨a2⟩ τ ⤳ t *)
(*   -> a1 ### E_skvars ψ *)
(*   -> ψ ⊢d' e ▸ ⟨a2 ++ a1⟩ τ ⤳ t. *)
(* Proof. *)
(*   introv DEC' FR. forwards E: DecA_lc DEC'. gen ψ a1 a2 τ t0. induction E; intros; inverts DEC'. *)
(*   - admit. *)
(*   - admit. *)
(*   - admit. *)
(*   - rewrite <- app_assoc. econstructor. applys WfT_E_A_sk_sub WFT. erel_fsetdec. *)
(*     intros x NIL__x. specializes DEC NIL__x. *)
(*     applys DecA_weaken DEC. erel_fsetdec. erel_fsetdec. erel_crush. *)
(*     eapply FrA_app. eassumption. eassumption. simpl+. fsetdec. *)
(*   - econstructor. applys_eq DEC1. admit. *)
(*     intros x NIL__x. eapply H0. admit. *)
(*     specializes DEC2 NIL__x. applys DecA_weaken DEC2. erel_fsetdec. erel_fsetdec. erel_crush. *)
(* Abort. *)

(*** Problem *)
(** The problem here is that in DecA_shift we increase the amount of variables
generalized over, which means we get a more general term at least, perhaps type.
I think we may need something like this *)

Axiom Remove_A : E -> A -> E.

Lemma DecA_shift : forall ψ a1 e a2 τ t,
    ψ ⊢d' e ▸ ⟨a2⟩ τ ⤳ t
  -> (Remove_A ψ a1) ⊢d' e ▸ ⟨a2 ++ a1⟩ τ ⤳ t.
Proof.
  introv DEC. dependent induction DEC.
  - econstructor. applys_eq IN. admit. admit.
  - econstructor. admit.
  - simpl+. econstructor. admit.
    introx. applys_eq DEC. fequals. admit. eassumption. admit.
  - admit.
  -
Abort.

Lemma DecA_shift : forall ψ a1 e a2 τ t,
    ψ ⊢d' e ▸ ⟨a2⟩ τ ⤳ t
  -> exists t', (Remove_A ψ a1) ⊢d' e ▸ ⟨a2 ++ a1⟩ τ ⤳ t'.
Proof.
  introv DEC. dependent induction DEC.
  admit. admit. admit. admit.
  -
Abort.


(* Lemma DecA_shift : forall ψ a1 e a2 τ t, *)
(*     ψ ::a a1 ⊢d' e ▸ ⟨a2⟩ τ ⤳ t *)
(*   -> a1 ### E_skvars ψ *)
(*   -> exists τ' t', ψ ⊢d' e ▸ ⟨a2 ++ a1⟩ τ' ⤳ t' *)
(* (** /\ ∀ a2 ++ a1. t': Λ a2 ++ a1. τ' <= ∀ a2. t: Λ a2. τ *) *)
(*    . *)
(* Abort. *)

(* Theorem Dec_DecA : forall ψ e τ t, *)
(*     ψ ::a a ⊢d e ▸ τ ⤳ t *)
(*   -> ψ ⊢d' e ▸ ⟨[a]⟩ τ ⤳ t. *)
Theorem Dec_DecA : forall ψ e τ t,
    ψ ⊢d e ▸ τ ⤳ t
  -> ψ ⊢d' e ▸ ⟨[]⟩ τ ⤳ t.
Proof.
  introv DEC. induction DEC.
  - econstructor. eassumption. applys SubSumpTmA_E_A_sk_sub.
    applys SubSumpTm_SubSumpTmA ψ ([]:A). applys SubSumpTm_E_A_sk_sub SS.
    erel_fsetdec. erel_fsetdec. erel_fsetdec.
  - crush.
  - asserts_rewrite (([]:A) = [] ++ []). crush.
    applys DecA__Abs L. applys WfT_E_A_sk_sub WFT. erel_fsetdec.
    intros x NIL__x. specializes H NIL__x.
    applys DecA_weaken H. erel_fsetdec. erel_fsetdec. erel_crush. crush.
  - asserts_rewrite (([]:A) = [] ++ []). crush.
    econstructor. eauto. applys DecA_weaken IHDEC2. 1,2:erel_fsetdec. erel_crush.
  - econstructor.
    instantiate (1 := τ1). admit. eauto.
Abort.

Require Import Semantics.EquivRel.

Ltac freshx L := forwards [?x ?NIL__x]: atom_fresh L.
Ltac freshx' := freshx empty.
Ltac freshy L := forwards [?y ?NIL__y]: atom_fresh L.
Ltac freshy' := freshy empty.
Ltac freshz L := forwards [?z ?NIL__z]: atom_fresh L.
Ltac freshz' := freshz empty.
Ltac freshα L := forwards [?α ?NIL__α]: atom_fresh L.
Ltac freshα' := freshα empty.
Ltac freshβ L := forwards [?y ?NIL__β]: atom_fresh L.
Ltac freshβ' := freshβ empty.

Tactic Notation "specializes'" hyp(H) :=
  specializes_base H (___); specializes_base H (___).
Tactic Notation "specializes'" hyp(H) constr(A) :=
  specializes_base H A; specializes_base H (___).
Tactic Notation "specializes'" hyp(H) constr(A1) constr(A2) :=
  specializes H (>> A1 A2); specializes_base H (___).
Tactic Notation "specializes'" hyp(H) constr(A1) constr(A2) constr(A3) :=
  specializes H (>> A1 A2 A3); specializes_base H (___).
Tactic Notation "specializes'" hyp(H) constr(A1) constr(A2) constr(A3) constr(A4) :=
  specializes H (>> A1 A2 A3 A4); specializes_base H (___).
Tactic Notation "specializes'" hyp(H) constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  specializes H (>> A1 A2 A3 A4 A5); specializes_base H (___).

Theorem Dec_DecA : forall e ψ a τ t,
    ψ ::a a ⊢d e ▸ τ ⤳ t
  -> exists t', ψ ⊢d' e ▸ ⟨a⟩ τ ⤳ t'
        /\ ψ ⊢t≈ t ≈ t' ▸ S__T τ.
Proof.
  intro e. assert (E: lc(e)). admit. induction E; introv DEC; inverts DEC.
  1,2,3,4:admit.
  - assert (DEC1': (ψ ::a (a0 ++ a)) ⊢d e1 ▸ τ1 ⤳ t1). applys Dec_weaken DEC1. erel_fsetdec. erel_crush.
    specializes IHE DEC1'. destruct IHE as [t1' [DECA1 EQ1]].
    freshx L. specializes' DEC2 x. fsetdec.
    specializes' H0 x. applys Dec_weaken (ψ ::x x :- (∀ a0 ⬪ S__T τ1) ::a a) DEC2.
      erel_fsetdec. erel_fsetdec.
      destruct H0 as [t2' [DECA2 EQ2]].
    exists. splits. econstructor. eassumption. introy.
Abort.

(*** Strengthening *)
Lemma DecA_generalize_binding : forall ψ x σ1 σ2 e a τ t,
    ψ ::x x :- σ2 ⊢d' e ▸ ⟨a⟩ τ ⤳ t
  -> SubSump' ψ σ1 σ2
  -> exists a' τ' t',
      ψ ::x x :- σ1 ⊢d' e ▸ ⟨a'⟩ τ' ⤳ t'.
Admitted.
