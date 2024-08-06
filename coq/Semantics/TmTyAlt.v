Set Warnings "-notation-overridden".
Require Import Preamble.
Require Import Defs.HdmLems.

Inductive TmTy' : E -> Tm -> Sc -> Prop :=    (* defn TmTy *)
 | TmTy__Var' : forall (ψ:E) (tx:tvar) (σ:Sc)
     (IN:  (E_lookup  ψ   tx  = Some  σ  ) ),
     TmTy' ψ (t__Var_f tx) σ
 | TmTy__Unit' : forall (ψ:E),
     TmTy' ψ t__Unit (S__T T__Unit)
 | TmTy__True' : forall (ψ:E),
     TmTy' ψ t__True (S__T T__Bool)
 | TmTy__False' : forall (ψ:E),
     TmTy' ψ t__False (S__T T__Bool)
 | TmTy__Abs' : forall (ψ:E) (τ1:T) (t:Tm) (τ2:T) (tx:tvar)
     (WFT:  (WfT  ψ   τ1 ) )
     (TMTY:  TmTy' (E__Var ψ tx (S__T τ1)) t (S__T τ2)),
     TmTy' ψ (t__Lam τ1 (close_Tm_wrt_Tm tx t)) (S__T (T__Fun τ1 τ2))
 | TmTy__App' : forall (ψ:E) (t1 t2:Tm) (τ2 τ1:T)
     (TYTY1: TmTy' ψ t1 (S__T (T__Fun τ1 τ2)))
     (TMTY2: TmTy' ψ t2 (S__T τ1)),
     TmTy' ψ (t__App t1 t2) (S__T τ2)
 | TmTy__TAbs' : forall (ψ:E) (t:Tm) (σ:Sc) (α:skvar)
     (TYTY:  TmTy' (E__A ψ  (  α  :: nil ) )  t  σ ),
     TmTy' ψ (t__TLam (close_Tm_wrt_T α t)) (S__Forall (close_Sc_wrt_T α σ))
 | TmTy__TApp' : forall (ψ:E) (t:Tm) (τ:T) (σ:Sc)
     (WFT:  (WfT  ψ   τ ) )
     (TMTY: TmTy' ψ t (S__Forall σ)),
     TmTy' ψ (t__TApp t τ)  ( open_Sc_wrt_T  σ   τ  ) .

#[export] Hint Constructors TmTy' : core.

Lemma TmTy'_iff_TmTy : forall ψ t σ,
    TmTy' ψ t σ
  <-> TmTy  ψ t σ.
(* Proof. *)
(*   split; introv TMTY. *)
(*   - induction TMTY. 1,2,3,4,6,8:eauto. *)
(*     + applys TmTy__Abs empty. eassumption. intros. *)
(*       rewrite <- subst_tvar_Tm_spec. *)
(*       admit. *)
(*     + applys TmTy__TAbs empty. intros. *)
(*       rewrite <- subst_skvar_Tm_spec. *)
(*       rewrite <- subst_skvar_Sc_spec. *)
(*       admit. *)
(*   - induction TMTY. 1,2,3,4,6,8:eauto. *)
(*     + forwards [x NIL__x]: atom_fresh (L ∪ fv__x(t0)). specializes H x. specializes H. fsetdec. *)
(*       applys_eq TmTy__Abs'. 3:apply H. 2:eassumption. *)
(*       rewrite close_Tm_wrt_Tm_open_Tm_wrt_Tm. reflexivity. fsetdec. *)
(*     + forwards [x NIL__x]: atom_fresh (L ∪ fv__α(t0) ∪ fv__α(σ)). specializes H x. specializes H. fsetdec. *)
(*       applys_eq TmTy__TAbs'. 3:apply H. *)
(*       rewrite close_Tm_wrt_T_open_Tm_wrt_T. reflexivity. fsetdec. *)
(*       rewrite close_Sc_wrt_T_open_Sc_wrt_T. reflexivity. fsetdec. *)
Admitted.

Corollary TmTy'TmTy : forall ψ t σ,
    TmTy' ψ t σ
  -> TmTy  ψ t σ.
Proof. apply TmTy'_iff_TmTy. Qed.
Corollary TmTyTmTy' : forall ψ t σ,
    TmTy  ψ t σ
  -> TmTy' ψ t σ.
Proof. apply TmTy'_iff_TmTy. Qed.
