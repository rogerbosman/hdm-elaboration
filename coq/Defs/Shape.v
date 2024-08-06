Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.

Require Import Defs.E.
Require Import Defs.List.

Inductive SameShape__τ : T -> T -> Prop :=
 | SSτ__Skvar_b : forall (n:nat),
     SameShape__τ (T__Var_b n) (T__Var_b n)
 | SSτ__Skvar_f : forall (α:skvar) (τ:T),
     SameShape__τ (T__Var_f α) τ
 | SSτ__Bool :
     SameShape__τ T__Bool T__Bool
 | SSτ__Unit :
     SameShape__τ T__Unit T__Unit
 | SSτ__Fun : forall (τ__fun1 τ__fun2:T) (τ__arg1 τ__arg2:T)
     (SS__τ1 : SameShape__τ τ__fun1 τ__fun2)
     (SS__τ2 : SameShape__τ τ__arg1 τ__arg2),
     SameShape__τ (T__Fun τ__fun1 τ__arg1) (T__Fun τ__fun2 τ__arg2).
#[export] Hint Constructors SameShape__τ : core.

Fact SSτ_refl  : Reflexive SameShape__τ.
  autounfold. intro τ. induction τ; constructor; crush. Qed.
Fact SSτ_trans : Transitive SameShape__τ.
  autounfold. intro τ1. induction τ1; intros τ2 τ3 SS1 SS2; inverts SS1; inverts SS2; crush; eauto. Qed.
#[export] Instance Preorder_SameShape__τ : PreOrder SameShape__τ :=
  { PreOrder_Reflexive  := SSτ_refl
  ; PreOrder_Transitive := SSτ_trans
  }.

Inductive SameShape__σ : Sc -> Sc -> Prop :=
  | SSσ__M : forall (τ1 τ2:T)
      (SS__τ : SameShape__τ τ1 τ2),
      SameShape__σ (S__T τ1) (S__T τ2)
  | SSσ__P : forall (σ1 σ2:Sc)
      (SS__σ : SameShape__σ σ1 σ2),
      SameShape__σ (S__Forall σ1) (S__Forall σ2).
#[export] Hint Constructors SameShape__σ : core.

Fact SSσ_refl  : Reflexive SameShape__σ.
  autounfold. intro σ. induction σ; crush. Qed.
Fact SSσ_trans : Transitive SameShape__σ.
  autounfold. intro σ1. induction σ1; intros σ2 σ3 SS1 SS2; inverts SS1; inverts SS2; crush; eauto. econstructor. crush. Qed.
#[export] Instance Preorder_SameShape__σ : PreOrder SameShape__σ :=
  { PreOrder_Reflexive  := SSσ_refl
  ; PreOrder_Transitive := SSσ_trans
  }.

Inductive SameShape__t : Tm -> Tm -> Prop :=
 | SSt__Tvar_b : forall (n : nat),
     SameShape__t (t__Var_b n) (t__Var_b n)
 | SSt__Var_f : forall (tx:tvar),
     SameShape__t (t__Var_f tx) (t__Var_f tx)
 | SSt__Unit :
     SameShape__t t__Unit t__Unit
 | SSt__True :
     SameShape__t t__True t__True
 | SSt__False :
     SameShape__t t__False t__False
 | SSt__App : forall (t__fun1 t__fun2:Tm) (t__arg1 t__arg2:Tm)
     (SS: SameShape__t t__fun1 t__fun2)
     (SS: SameShape__t t__arg1 t__arg2),
     SameShape__t (t__App t__fun1 t__arg1) (t__App t__fun2 t__arg2)
 | SSt__TApp : forall (t1 t2:Tm) (τ1 τ2:T)
     (SS: SameShape__t t1 t2)
     (SS: SameShape__τ τ1 τ2),
     SameShape__t (t__TApp t1 τ1) (t__TApp t2 τ2)
 | SSt__Lam : forall (τ1 τ2:T) (t1 t2:Tm)
     (SS: SameShape__τ τ1 τ2)
     (SS: SameShape__t t1 t2),
     SameShape__t (t__Lam τ1 t1) (t__Lam τ2 t2)
 | SSt__TLam : forall (t1 t2:Tm)
     (SS: SameShape__t t1 t2),
     SameShape__t (t__TLam t1) (t__TLam t2)
 (* | SSt__Let : forall (σ1 σ2:Sc) (t__let1 t__let2:Tm) (t__in1 t__in2:Tm) *)
 (*     (SS: SameShape__σ σ1 σ2) *)
 (*     (SS: SameShape__t t__let1 t__let2) *)
 (*     (SS: SameShape__t t__in1 t__in2), *)
 (*     SameShape__t (t__Let σ1 t__let1 t__in1) (t__Let σ2 t__let2 t__in2) *)
.
#[export] Hint Constructors SameShape__t : core.

Fact SSt_refl  : Reflexive SameShape__t.
  autounfold. intro σ. induction σ; crush. Qed.
Fact SSt_trans : Transitive SameShape__t.
  autounfold. intro t1. induction t1; intros t2 t3 SS1 SS2; inverts SS1; inverts SS2; crush; eauto; econstructor; solve [eauto|crush]. Qed.
#[export] Instance Preorder_SameShape__t : PreOrder SameShape__t :=
  { PreOrder_Reflexive  := SSt_refl
  ; PreOrder_Transitive := SSt_trans
  }.

(** Lemmas *)
Lemma ftv_Tm_SameShape__t : forall t1 t2,
    SameShape__t t1 t2
  -> fv(t1) = fv(t2).
Proof. introv SSt. induction SSt; simpl+; crush. Qed.

Lemma ftv_SameShape__t : forall t1 t2,
    SameShape__t t1 t2
  -> fv__x(t1) = fv__x(t2).
Proof. introv SS. induction SS; simpl+; crush. Qed.

Inductive SameShape__A : A -> A -> Prop :=
  | SSA : forall (a1 a2:A),
      (length a1 = 0 -> length a2 = 0)
    -> SameShape__A a1 a2.
Fact SSA_refl  : Reflexive SameShape__A.
  autounfold. intros. constructor. crush. Qed.
Fact SSA_trans : Transitive SameShape__A.
  autounfold. intros. constructor. crush. inverts H. crush. inverts H0. crush. Qed.
#[export] Instance Preorder_SameShape__A : PreOrder SameShape__A :=
  { PreOrder_Reflexive  := SSA_refl
  ; PreOrder_Transitive := SSA_trans
  }.

Inductive SameShape__E : E -> E -> Prop :=
 | SSE__Nil :
     SameShape__E • •
 | SSE__A : forall (ψ1 ψ2:E) (a1 a2:A)
     (SS: SameShape__E ψ1 ψ2)
     (SS: SameShape__A a1 a2),
     SameShape__E (ψ1 ::a a1) (ψ2 ::a a2)
 | SSE__Var : forall (ψ1 ψ2:E) (x:var) (σ1 σ2:Sc)
     (SS: SameShape__E ψ1 ψ2)
     (SS: SameShape__σ σ1 σ2),
     SameShape__E (ψ1 ::x x :- σ1) (ψ2 ::x x :- σ2)
 | SSE__O : forall (ψ1 ψ2:E) (t1 t2:Tm) (a1 a2:A) (σ1 σ2:Sc)
     (SS: SameShape__E ψ1 ψ2)
     (SS: SameShape__t t1 t2)
     (SS: SameShape__A a1 a2)
     (SS: SameShape__σ σ1 σ2),
     SameShape__E (ψ1 ::o ⦇t1 ▸ ⟨a1⟩ σ1⦈) (ψ2 ::o ⦇t2 ▸ ⟨a2⟩ σ2⦈).
#[export] Hint Constructors SameShape__E : core.


Fact SSE_refl  : Reflexive SameShape__E.
  autounfold. intro σ. induction σ; crush. Qed.
Fact SSE_trans : Transitive SameShape__E.
  autounfold. intro t1. induction t1; intros t2 t3 SS1 SS2; inverts SS1; inverts SS2; crush; eauto; econstructor; solve[eauto|crush]. Qed.
#[export] Instance Preorder_SameShape__E : PreOrder SameShape__E :=
  { PreOrder_Reflexive  := SSE_refl
  ; PreOrder_Transitive := SSE_trans
  }.

Ltac inv_SSE_ :=
  match goal with
    | [ H : SameShape__E •                  _ |- _ ] => inverts H
    | [ H : SameShape__E (_ ::a _)           _ |- _ ] => inverts H
    | [ H : SameShape__E (_ ::x _ :- _ )     _ |- _ ] => inverts H
    | [ H : SameShape__E (_ ::o ⦇_ ▸ ⟨_⟩ _⦈) _ |- _ ] => inverts H

    | [ H : SameShape__E _ •                  |- _ ] => inverts H
    | [ H : SameShape__E _ (_ ::a _)           |- _ ] => inverts H
    | [ H : SameShape__E _ (_ ::x _ :- _ )     |- _ ] => inverts H
    | [ H : SameShape__E _ (_ ::o ⦇_ ▸ ⟨_⟩ _⦈) |- _ ] => inverts H
  end.
Ltac inv_SSE := repeat inv_SSE_.
(* Ltac inv_EInst' := repeat (try inv_EInst; inv_AInst). *)

Fact SSE_app : forall ψ1 ψ1' ψ2 ψ2',
    SameShape__E ψ1 ψ1'
  -> SameShape__E ψ2 ψ2'
  -> SameShape__E (ψ1 +++ ψ2) (ψ1' +++ ψ2').
Proof. introv SS1 SS2. gen ψ2'. induction ψ2; intros ψ2' SS2; inverts SS2; crush. Qed.
#[export] Hint Resolve SSE_app : core.
Fact SSE_app_proper : Proper (SameShape__E ==> SameShape__E ==> SameShape__E) E__app. autounfold. crush. Qed.

(** Lemmas *)
Lemma E_names_SameShape__E : forall ψ1 ψ2,
    SameShape__E ψ1 ψ2
  -> E_names ψ1 = E_names ψ2.
Proof.
  introv SSE. induction SSE. 1,2,3: crush.
  simpl+. rewrite IHSSE. fsetdec.
Qed.

Lemma E_O_names_SameShape__E : forall ψ1 ψ2,
    SameShape__E ψ1 ψ2
  -> E_O_names ψ1 = E_O_names ψ2.
Proof.
  introv SSE. induction SSE. 1,2,3: crush.
  simpl+. rewrite IHSSE. erewrite ftv_Tm_SameShape__t. 2:eassumption. reflexivity.
Qed.

(* Module Type E_fold_alg_alg. *)
(*   Variable S : Type. *)
(*   Variable s0 :                   S. *)
(*   Variable f__a : S -> A           -> S. *)
(*   Variable f__x : S -> var -> Sc    -> S. *)
(*   Variable f__o : S -> Tm -> A -> Sc -> S. *)
(* End E_fold_alg_alg. *)

(* Module E_fold_with_laws (alg : E_fold_alg_alg). *)
(*   Definition E_fold : E -> alg.S := HdmDefs.E_fold alg.s0 alg.f__a alg.f__x alg.f__o. *)

(*   Fact E_fold_app := forall ψ1 ψ2, E__fold (ψ1 +++ ψ2) = E__fold (ψ1 +++ ψ2) *)
(* End E_fold_with_laws. *)

(* Module alg_length__E <: E_fold_alg_alg. *)
(*   Definition S  := nat. *)
(*   Definition s0 := 0. *)
(*   Definition f__a : S -> A           -> S := (const ∘ (plus 1)). *)
(*   Definition f__x : S -> var -> Sc    -> S := (const ∘ const ∘ (plus 1)). *)
(*   Definition f__o : S -> Tm -> A -> Sc -> S := (const ∘ const ∘ const ∘ (plus 1)). *)
(* End alg_length__E. *)

(* Module Export M_length__E := E_fold_with_laws alg_length__E. *)
(* Notation E_length := M_length__E.E_fold. *)

(*** E_length *)
Definition E_length : E -> nat :=
  E_fold
    0
    (const ∘ (plus 1))
    (const ∘ const ∘ (plus 1))
    (const ∘ const ∘ const ∘ (plus 1)).

Fact E_length_app : forall ψ1 ψ2,
    E_length (ψ1 +++ ψ2) = (E_length ψ1 + E_length ψ2)%nat.
Proof. intros ψ1 ψ2. induction ψ2; simpl+; crush. Qed.
#[export] Hint Rewrite E_length_app : core.

Notation SameLength__E ψ1 ψ2 := (E_length ψ1 = E_length ψ2).

Fact SSE_length : forall ψ1 ψ2,
    SameShape__E ψ1 ψ2
  -> SameLength__E ψ1 ψ2.
Proof. induction 1; crush. Qed.

Fact SameLength_app : forall ψ1 ψ2,
    SameLength__E (ψ1 +++ ψ2) ψ1
  -> ψ2 = •.
Proof. intros. destruct ψ2; crush. Qed.

(*** Insert_ANil_at*)

Inductive Insert_ANil_at : nat -> E -> E -> Prop :=
  | Here : forall ψ,
      Insert_ANil_at (E_length ψ) ψ (ψ ::a [])
  | There__A : forall n ψ ψ' a,
      Insert_ANil_at n ψ ψ'
    -> Insert_ANil_at n (ψ ::a a) (ψ' ::a a)
  | There__Var : forall n ψ ψ' x σ,
      Insert_ANil_at n ψ ψ'
    -> Insert_ANil_at n (ψ ::x x :- σ) (ψ' ::x x :- σ)
  | There__Obj : forall n ψ ψ' t a σ,
      Insert_ANil_at n ψ ψ'
    -> Insert_ANil_at n (ψ ::o ⦇ t ▸ ⟨ a ⟩ σ ⦈) (ψ' ::o ⦇ t ▸ ⟨ a ⟩ σ ⦈).
#[export] Hint Constructors Insert_ANil_at : core.

Fact Insert_ANil_at_create : forall n ψ,
    n <= E_length ψ
  -> exists ψ', Insert_ANil_at n ψ ψ'.
Proof.
  introv LEQ. induction ψ; simpl+ in LEQ.
  - destruct n. exists. applys_eq Here. crush. crush.
  - apply le_lt_eq_dec in LEQ. destruct LEQ.
    + forwards [ψ' IA]: IHψ. crush.
      exists. eauto.
    + exists. applys_eq Here. crush.
  - apply le_lt_eq_dec in LEQ. destruct LEQ.
    + forwards [ψ' IA]: IHψ. crush.
      exists. eauto.
    + exists. applys_eq Here. crush.
  - apply le_lt_eq_dec in LEQ. destruct LEQ.
    + forwards [ψ' IA]: IHψ. crush.
      exists. eauto.
    + exists. applys_eq Here. crush.
Qed.

Fact Insert_ANil_at_smaller : forall n ψ1 ψ2,
    Insert_ANil_at n ψ1 ψ2
  -> n <= E_length ψ1.
Proof. introv IN. induction IN; crush. Qed.

Fact Insert_ANil_at_length : forall ψ1 ψ2,
    Insert_ANil_at (E_length ψ1) ψ1 ψ2
  -> ψ2 = ψ1 ::a [].
Proof. introv IA. inverts IA; try (apply Insert_ANil_at_smaller in H; simpl+ in H); crush. Qed.

Fact Insert_ANil_at_app_destr : forall ψ1 ψ2 ψ3,
    Insert_ANil_at (E_length ψ1) (ψ1 +++ ψ2) ψ3
  -> ψ3 = ((ψ1 ::a []) +++ ψ2).
Proof.
  introv IA. gen ψ3. induction ψ2; intros; simpl+ in IA.
  - simpl+. eauto using Insert_ANil_at_length.
  - inverts IA. simpl+ in H0. crush.
    simpl+. fequals. eauto.
  - inverts IA. simpl+ in H0. crush.
    simpl+. fequals. eauto.
  - inverts IA. simpl+ in H0. crush.
    simpl+. fequals. eauto.
Qed.

Fact Insert_ANil_at_destr : forall n ψ1 ψ2,
    Insert_ANil_at n ψ1 ψ2
  -> exists ψ2' ψ2'',
    ψ2 = (ψ2' ::a []) +++ ψ2''
  /\ ψ1 = ψ2' +++ ψ2''.
Proof.
  introv IA. induction IA. exists ψ •. crush.
  - destruct IHIA as [ψ2' [ψ2'' [EQ1 EQ2]]]. subst.
    exists. splits. norm. rewrite <- E_app_assoc. reflexivity. crush.
  - destruct IHIA as [ψ2' [ψ2'' [EQ1 EQ2]]]. subst.
    exists. splits. norm. rewrite <- E_app_assoc. reflexivity. crush.
  - destruct IHIA as [ψ2' [ψ2'' [EQ1 EQ2]]]. subst.
    exists. splits. norm. rewrite <- E_app_assoc. reflexivity. crush.
Qed.


(* Fact Insert_ANil_at_app : forall ψ2 ψ1 ψ3, *)
(*     Insert_ANil_at (E_length ψ1) (ψ1 +++ ψ2) ψ3 *)
(*   -> exists ψ3', ψ3 = (ψ3' ::a []) +++ ψ2. *)
(* Proof. *)
(*   intro ψ2. induction ψ2; introv IA. *)
(*   - simpl+ in IA. forwards: Insert_ANil_at_length. eassumption. subst. exists. crush. *)
(*   - inverts IA. simpl+ in H0. crush. *)
(*     forwards [ψ3' EQ]: IHψ2. eassumption. subst. *)
(*     exists. crush. *)
(*   - inverts IA. simpl+ in H0. crush. *)
(*     forwards [ψ3' EQ]: IHψ2. eassumption. subst. *)
(*     exists. crush. *)
(*   - inverts IA. simpl+ in H0. crush. *)
(*     forwards [ψ3' EQ]: IHψ2. eassumption. subst. *)
(*     exists. crush. *)
(* Qed. *)
