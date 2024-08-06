Set Warnings "-notation-overridden".
Require Import Preamble.
Require Import Defs.HdmLems.

Require Import Defs.TmTy.

Require Import Semantics.TmTyAlt.

Inductive Cont : Set :=
  (* [] *)
  | Hole
  (* \(x:τ). C *)
  | C__Lam (x:var) (τ:T) (C:Cont)
  (* C t *)
  | C__AppL (C:Cont) (t:Tm)
  (* t C *)
  | C__AppR (t:Tm) (C:Cont)
  (* \\α. C *)
  | C__TLam (α:skvar) (C:Cont)
  (* C [τ] *)
  | C__TApp (C:Cont) (τ:T).

Fixpoint fill_Cont (C:Cont) (t:Tm) : Tm :=
  match C with
  | Hole => t
  | (C__Lam x τ C)   => t__Lam τ (close_Tm_wrt_Tm x (fill_Cont C t))
  | (C__AppL C t') => t__App (fill_Cont C t) t'
  | (C__AppR t' C) => t__App t' (fill_Cont C t)
  | (C__TLam α C)    => t__TLam (close_Tm_wrt_T α (fill_Cont C t))
  | (C__TApp C τ)  => t__TApp (fill_Cont C t) τ
  end.

Inductive CTy : Cont -> E -> Sc -> E -> Sc -> Prop :=
  | CTy__Hole : forall (C:Cont) (ψ:E) (σ:Sc),
      CTy Hole ψ σ ψ σ
  | CTy__Abs : forall (C:Cont) (ψ__in:E) (σ__in:Sc) (ψ:E) (τ1:T) (τ2:T) (tx:var) (** essentially TmTy__Abs *)
      (WFT:  (WfT ψ τ1))
      (CT: CTy C ψ__in σ__in (E__Var ψ tx (S__T τ1)) (S__T τ2)),
      CTy (C__Lam tx τ1 C) ψ__in σ__in ψ (S__T (T__Fun τ1 τ2))
  | CTy__AppL : forall (C:Cont) (ψ__in:E) (σ__in:Sc) (ψ:E) (t2:Tm) (τ1 τ2:T) (** essentially TmTy__App *)
      (CT1: CTy C ψ__in σ__in ψ (S__T (T__Fun τ1 τ2)))
      (TMTY2: TmTy ψ t2 (S__T τ1)),
      CTy (C__AppL C t2) ψ__in σ__in ψ (S__T τ2)
  | CTy__AppR : forall (C:Cont) (ψ__in:E) (σ__in:Sc) (ψ:E) (t1:Tm) (τ2 τ1:T) (** essentially TmTy__App *)
      (TYTY1: TmTy ψ t1 (S__T (T__Fun τ1 τ2)))
      (CT2: CTy C ψ__in σ__in ψ (S__T τ1)),
      CTy (C__AppR t1 C) ψ__in σ__in ψ (S__T τ2)
 | CTy__TAbs : forall (C:Cont) (ψ__in:E) (σ__in:Sc) (L:vars) (ψ:E) (t:Tm) (σ:Sc) (α:skvar)
     (CT:  CTy C ψ__in σ__in (E__A ψ  (  α  :: nil ) )  σ ),
     CTy (C__TLam α C) ψ__in σ__in ψ (S__Forall (close_Sc_wrt_T α σ))
  | CTy__TApp : forall (C:Cont) (ψ__in:E) (σ__in:Sc) (ψ:E) (τ:T) (σ:Sc) (** essentially TmTy__TApp *)
      (WFT: (WfT  ψ τ ))
      (CT: CTy C ψ__in σ__in ψ (S__Forall σ)),
      CTy (C__TApp C τ) ψ__in σ__in ψ (open_Sc_wrt_T σ τ).

Notation  "C ▸ ( ψ ⊢c σ ) ⟹ ( ψ' ⊢c σ' )" := (CTy C ψ σ ψ' σ') (at level 70, format "C  ▸  ( ψ  ⊢c  σ )  ⟹  ( ψ'  ⊢c  σ' )", only printing) : type_scope.

Lemma fill_CTy : forall C ψ__in σ__in ψ σ t,
    CTy C ψ__in σ__in ψ σ
  -> ψ__in ⊢t t ▸ σ__in
  -> ψ ⊢t (fill_Cont C t) ▸ σ.
Proof.
  introv CTY TMTY. induction CTY; simpl+.
  - crush.
  - econstructor. eassumption. intros.
    forwards: IHCTY. eassumption.
    (** this doesn't work, we need an existential typing for terms *)
Abort.

Lemma fill_CTy : forall C ψ__in σ__in ψ σ t,
    CTy C ψ__in σ__in ψ σ
  -> ψ__in ⊢t t ▸ σ__in
  -> ψ ⊢t (fill_Cont C t) ▸ σ.
Proof.
  introv CTY TMTY. rewrite <- TmTy'_iff_TmTy. induction CTY; simpl+; eauto using TmTyTmTy'.
Qed.

(* Inductive Cont' : Set := *)
(*   (* [] *) *)
(*   | Hole' *)
(*   (* \(x:τ). C *) *)
(*   | C__Lam' (τ:T) (C:Cont'). *)

(* Fixpoint fill_Cont' (C:Cont') (t:Tm) : Tm := *)
(*   match C with *)
(*   | Hole' => t *)
(*   | (C__Lam' τ C)   => t__Lam τ (fill_Cont' C t) *)
(*   end. *)

(* Inductive CTy' : Cont -> E -> Sc -> E -> Sc -> Prop := *)
(*   | CTy__Abs : forall (C:Cont') (ψ__in:E) (σ__in:Sc) (L:vars) (ψ:E) (τ1:T) (τ2:T) (tx:var) (** essentially TmTy__Abs *) *)
(*       (WFT:  (WfT ψ τ1)) *)
(*       (CT: CTy' C ψ__in σ__in (E__Var ψ tx (S__T τ1)) (S__T τ2)), *)
(*       CTy (C__Lam τ1 C) ψ__in σ__in ψ (S__T (T__Fun τ1 τ2)). *)
