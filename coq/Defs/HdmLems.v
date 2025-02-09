Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

(** Roger: changed CoqLNOutput.hs to include -notation-overridden
 and put before HdmDefs import *)

Local Set Warnings "-non-recursive,-deprecated-tactic,-notation-overridden,-intuition-auto-with-star". 

Require Import Metalib.Metatheory.
Require Import Metalib.LibLNgen.

Require Import Defs.HdmLemsDeps.
Require Export Defs.HdmLemsOrig.
Require Import Defs.HdmLemsSubst.

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)


(* *********************************************************************** *)
(*defs removed*)
(** * Theorems about [size] *)

(*ltac removed*)

(*hidden lems removed*)

Lemma size_Ex_min :
forall e1, 1 <= size_Ex e1.
Proof.
unfold_singletons; exact size_Ex_min.
Qed.

#[export] Hint Resolve size_Ex_min : lngen.

(*hidden lems removed*)

Lemma size_T_min :
forall T1, 1 <= size_T T1.
Proof.
unfold_singletons; exact size_T_min.
Qed.

#[export] Hint Resolve size_T_min : lngen.

(*hidden lems removed*)

Lemma size_Sc_min :
forall Sc1, 1 <= size_Sc Sc1.
Proof.
unfold_singletons; exact size_Sc_min.
Qed.

#[export] Hint Resolve size_Sc_min : lngen.

(*hidden lems removed*)

Lemma size_Tm_min :
forall t1, 1 <= size_Tm t1.
Proof.
unfold_singletons; exact size_Tm_min.
Qed.

#[export] Hint Resolve size_Tm_min : lngen.

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

Lemma size_Ex_close_Ex_wrt_Ex :
forall e1 x1,
  size_Ex (close_Ex_wrt_Ex x1 e1) = size_Ex e1.
Proof.
unfold_singletons; exact size_Ex_close_Ex_wrt_Ex.
Qed.

#[export] Hint Resolve size_Ex_close_Ex_wrt_Ex : lngen.
#[export] Hint Rewrite size_Ex_close_Ex_wrt_Ex using solve [auto] : lngen.

Lemma size_T_close_T_wrt_T :
forall T1 β1,
  size_T (close_T_wrt_T β1 T1) = size_T T1.
Proof.
unfold_singletons; exact size_T_close_T_wrt_T.
Qed.

#[export] Hint Resolve size_T_close_T_wrt_T : lngen.
#[export] Hint Rewrite size_T_close_T_wrt_T using solve [auto] : lngen.

Lemma size_Sc_close_Sc_wrt_T :
forall Sc1 β1,
  size_Sc (close_Sc_wrt_T β1 Sc1) = size_Sc Sc1.
Proof.
unfold_singletons; exact size_Sc_close_Sc_wrt_T.
Qed.

#[export] Hint Resolve size_Sc_close_Sc_wrt_T : lngen.
#[export] Hint Rewrite size_Sc_close_Sc_wrt_T using solve [auto] : lngen.

Lemma size_Tm_close_Tm_wrt_T :
forall t1 β1,
  size_Tm (close_Tm_wrt_T β1 t1) = size_Tm t1.
Proof.
unfold_singletons; exact size_Tm_close_Tm_wrt_T.
Qed.

#[export] Hint Resolve size_Tm_close_Tm_wrt_T : lngen.
#[export] Hint Rewrite size_Tm_close_Tm_wrt_T using solve [auto] : lngen.

Lemma size_Tm_close_Tm_wrt_Tm :
forall t1 tx1,
  size_Tm (close_Tm_wrt_Tm tx1 t1) = size_Tm t1.
Proof.
unfold_singletons; exact size_Tm_close_Tm_wrt_Tm.
Qed.

#[export] Hint Resolve size_Tm_close_Tm_wrt_Tm : lngen.
#[export] Hint Rewrite size_Tm_close_Tm_wrt_Tm using solve [auto] : lngen.

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

Lemma size_Ex_open_Ex_wrt_Ex :
forall e1 e2,
  size_Ex e1 <= size_Ex (open_Ex_wrt_Ex e1 e2).
Proof.
unfold_singletons; exact size_Ex_open_Ex_wrt_Ex.
Qed.

#[export] Hint Resolve size_Ex_open_Ex_wrt_Ex : lngen.

Lemma size_T_open_T_wrt_T :
forall T1 T2,
  size_T T1 <= size_T (open_T_wrt_T T1 T2).
Proof.
unfold_singletons; exact size_T_open_T_wrt_T.
Qed.

#[export] Hint Resolve size_T_open_T_wrt_T : lngen.

Lemma size_Sc_open_Sc_wrt_T :
forall Sc1 T1,
  size_Sc Sc1 <= size_Sc (open_Sc_wrt_T Sc1 T1).
Proof.
unfold_singletons; exact size_Sc_open_Sc_wrt_T.
Qed.

#[export] Hint Resolve size_Sc_open_Sc_wrt_T : lngen.

Lemma size_Tm_open_Tm_wrt_T :
forall t1 T1,
  size_Tm t1 <= size_Tm (open_Tm_wrt_T t1 T1).
Proof.
unfold_singletons; exact size_Tm_open_Tm_wrt_T.
Qed.

#[export] Hint Resolve size_Tm_open_Tm_wrt_T : lngen.

Lemma size_Tm_open_Tm_wrt_Tm :
forall t1 t2,
  size_Tm t1 <= size_Tm (open_Tm_wrt_Tm t1 t2).
Proof.
unfold_singletons; exact size_Tm_open_Tm_wrt_Tm.
Qed.

#[export] Hint Resolve size_Tm_open_Tm_wrt_Tm : lngen.

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

Lemma size_Ex_open_Ex_wrt_Ex_var :
forall e1 x1,
  size_Ex (open_Ex_wrt_Ex e1 (e__Var_f x1)) = size_Ex e1.
Proof.
unfold_singletons; exact size_Ex_open_Ex_wrt_Ex_var.
Qed.

#[export] Hint Resolve size_Ex_open_Ex_wrt_Ex_var : lngen.
#[export] Hint Rewrite size_Ex_open_Ex_wrt_Ex_var using solve [auto] : lngen.

Lemma size_T_open_T_wrt_T_var :
forall T1 β1,
  size_T (open_T_wrt_T T1 (T__Var_f β1)) = size_T T1.
Proof.
unfold_singletons; exact size_T_open_T_wrt_T_var.
Qed.

#[export] Hint Resolve size_T_open_T_wrt_T_var : lngen.
#[export] Hint Rewrite size_T_open_T_wrt_T_var using solve [auto] : lngen.

Lemma size_Sc_open_Sc_wrt_T_var :
forall Sc1 β1,
  size_Sc (open_Sc_wrt_T Sc1 (T__Var_f β1)) = size_Sc Sc1.
Proof.
unfold_singletons; exact size_Sc_open_Sc_wrt_T_var.
Qed.

#[export] Hint Resolve size_Sc_open_Sc_wrt_T_var : lngen.
#[export] Hint Rewrite size_Sc_open_Sc_wrt_T_var using solve [auto] : lngen.

Lemma size_Tm_open_Tm_wrt_T_var :
forall t1 β1,
  size_Tm (open_Tm_wrt_T t1 (T__Var_f β1)) = size_Tm t1.
Proof.
unfold_singletons; exact size_Tm_open_Tm_wrt_T_var.
Qed.

#[export] Hint Resolve size_Tm_open_Tm_wrt_T_var : lngen.
#[export] Hint Rewrite size_Tm_open_Tm_wrt_T_var using solve [auto] : lngen.

Lemma size_Tm_open_Tm_wrt_Tm_var :
forall t1 tx1,
  size_Tm (open_Tm_wrt_Tm t1 (t__Var_f tx1)) = size_Tm t1.
Proof.
unfold_singletons; exact size_Tm_open_Tm_wrt_Tm_var.
Qed.

#[export] Hint Resolve size_Tm_open_Tm_wrt_Tm_var : lngen.
#[export] Hint Rewrite size_Tm_open_Tm_wrt_Tm_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

(*ltac removed*)

(*hidden lems removed*)

Lemma degree_Ex_wrt_Ex_S :
forall n1 e1,
  degree_Ex_wrt_Ex n1 e1 ->
  degree_Ex_wrt_Ex (S n1) e1.
Proof.
unfold_singletons; exact degree_Ex_wrt_Ex_S.
Qed.

#[export] Hint Resolve degree_Ex_wrt_Ex_S : lngen.

(*hidden lems removed*)

Lemma degree_T_wrt_T_S :
forall n1 T1,
  degree_T_wrt_T n1 T1 ->
  degree_T_wrt_T (S n1) T1.
Proof.
unfold_singletons; exact degree_T_wrt_T_S.
Qed.

#[export] Hint Resolve degree_T_wrt_T_S : lngen.

(*hidden lems removed*)

Lemma degree_Sc_wrt_T_S :
forall n1 Sc1,
  degree_Sc_wrt_T n1 Sc1 ->
  degree_Sc_wrt_T (S n1) Sc1.
Proof.
unfold_singletons; exact degree_Sc_wrt_T_S.
Qed.

#[export] Hint Resolve degree_Sc_wrt_T_S : lngen.

(*hidden lems removed*)

Lemma degree_Tm_wrt_T_S :
forall n1 t1,
  degree_Tm_wrt_T n1 t1 ->
  degree_Tm_wrt_T (S n1) t1.
Proof.
unfold_singletons; exact degree_Tm_wrt_T_S.
Qed.

#[export] Hint Resolve degree_Tm_wrt_T_S : lngen.

(*hidden lems removed*)

Lemma degree_Tm_wrt_Tm_S :
forall n1 t1,
  degree_Tm_wrt_Tm n1 t1 ->
  degree_Tm_wrt_Tm (S n1) t1.
Proof.
unfold_singletons; exact degree_Tm_wrt_Tm_S.
Qed.

#[export] Hint Resolve degree_Tm_wrt_Tm_S : lngen.

Lemma degree_Ex_wrt_Ex_O :
forall n1 e1,
  degree_Ex_wrt_Ex O e1 ->
  degree_Ex_wrt_Ex n1 e1.
Proof.
unfold_singletons; exact degree_Ex_wrt_Ex_O.
Qed.

#[export] Hint Resolve degree_Ex_wrt_Ex_O : lngen.

Lemma degree_T_wrt_T_O :
forall n1 T1,
  degree_T_wrt_T O T1 ->
  degree_T_wrt_T n1 T1.
Proof.
unfold_singletons; exact degree_T_wrt_T_O.
Qed.

#[export] Hint Resolve degree_T_wrt_T_O : lngen.

Lemma degree_Sc_wrt_T_O :
forall n1 Sc1,
  degree_Sc_wrt_T O Sc1 ->
  degree_Sc_wrt_T n1 Sc1.
Proof.
unfold_singletons; exact degree_Sc_wrt_T_O.
Qed.

#[export] Hint Resolve degree_Sc_wrt_T_O : lngen.

Lemma degree_Tm_wrt_T_O :
forall n1 t1,
  degree_Tm_wrt_T O t1 ->
  degree_Tm_wrt_T n1 t1.
Proof.
unfold_singletons; exact degree_Tm_wrt_T_O.
Qed.

#[export] Hint Resolve degree_Tm_wrt_T_O : lngen.

Lemma degree_Tm_wrt_Tm_O :
forall n1 t1,
  degree_Tm_wrt_Tm O t1 ->
  degree_Tm_wrt_Tm n1 t1.
Proof.
unfold_singletons; exact degree_Tm_wrt_Tm_O.
Qed.

#[export] Hint Resolve degree_Tm_wrt_Tm_O : lngen.

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

Lemma degree_Ex_wrt_Ex_close_Ex_wrt_Ex :
forall e1 x1,
  degree_Ex_wrt_Ex 0 e1 ->
  degree_Ex_wrt_Ex 1 (close_Ex_wrt_Ex x1 e1).
Proof.
unfold_singletons; exact degree_Ex_wrt_Ex_close_Ex_wrt_Ex.
Qed.

#[export] Hint Resolve degree_Ex_wrt_Ex_close_Ex_wrt_Ex : lngen.

Lemma degree_T_wrt_T_close_T_wrt_T :
forall T1 β1,
  degree_T_wrt_T 0 T1 ->
  degree_T_wrt_T 1 (close_T_wrt_T β1 T1).
Proof.
unfold_singletons; exact degree_T_wrt_T_close_T_wrt_T.
Qed.

#[export] Hint Resolve degree_T_wrt_T_close_T_wrt_T : lngen.

Lemma degree_Sc_wrt_T_close_Sc_wrt_T :
forall Sc1 β1,
  degree_Sc_wrt_T 0 Sc1 ->
  degree_Sc_wrt_T 1 (close_Sc_wrt_T β1 Sc1).
Proof.
unfold_singletons; exact degree_Sc_wrt_T_close_Sc_wrt_T.
Qed.

#[export] Hint Resolve degree_Sc_wrt_T_close_Sc_wrt_T : lngen.

Lemma degree_Tm_wrt_T_close_Tm_wrt_T :
forall t1 β1,
  degree_Tm_wrt_T 0 t1 ->
  degree_Tm_wrt_T 1 (close_Tm_wrt_T β1 t1).
Proof.
unfold_singletons; exact degree_Tm_wrt_T_close_Tm_wrt_T.
Qed.

#[export] Hint Resolve degree_Tm_wrt_T_close_Tm_wrt_T : lngen.

Lemma degree_Tm_wrt_T_close_Tm_wrt_Tm :
forall t1 tx1 n1,
  degree_Tm_wrt_T n1 t1 ->
  degree_Tm_wrt_T n1 (close_Tm_wrt_Tm tx1 t1).
Proof.
unfold_singletons; exact degree_Tm_wrt_T_close_Tm_wrt_Tm.
Qed.

#[export] Hint Resolve degree_Tm_wrt_T_close_Tm_wrt_Tm : lngen.

Lemma degree_Tm_wrt_Tm_close_Tm_wrt_T :
forall t1 β1 n1,
  degree_Tm_wrt_Tm n1 t1 ->
  degree_Tm_wrt_Tm n1 (close_Tm_wrt_T β1 t1).
Proof.
unfold_singletons; exact degree_Tm_wrt_Tm_close_Tm_wrt_T.
Qed.

#[export] Hint Resolve degree_Tm_wrt_Tm_close_Tm_wrt_T : lngen.

Lemma degree_Tm_wrt_Tm_close_Tm_wrt_Tm :
forall t1 tx1,
  degree_Tm_wrt_Tm 0 t1 ->
  degree_Tm_wrt_Tm 1 (close_Tm_wrt_Tm tx1 t1).
Proof.
unfold_singletons; exact degree_Tm_wrt_Tm_close_Tm_wrt_Tm.
Qed.

#[export] Hint Resolve degree_Tm_wrt_Tm_close_Tm_wrt_Tm : lngen.

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

Lemma degree_Ex_wrt_Ex_close_Ex_wrt_Ex_inv :
forall e1 x1,
  degree_Ex_wrt_Ex 1 (close_Ex_wrt_Ex x1 e1) ->
  degree_Ex_wrt_Ex 0 e1.
Proof.
unfold_singletons; exact degree_Ex_wrt_Ex_close_Ex_wrt_Ex_inv.
Qed.

#[export] Hint Immediate degree_Ex_wrt_Ex_close_Ex_wrt_Ex_inv : lngen.

Lemma degree_T_wrt_T_close_T_wrt_T_inv :
forall T1 β1,
  degree_T_wrt_T 1 (close_T_wrt_T β1 T1) ->
  degree_T_wrt_T 0 T1.
Proof.
unfold_singletons; exact degree_T_wrt_T_close_T_wrt_T_inv.
Qed.

#[export] Hint Immediate degree_T_wrt_T_close_T_wrt_T_inv : lngen.

Lemma degree_Sc_wrt_T_close_Sc_wrt_T_inv :
forall Sc1 β1,
  degree_Sc_wrt_T 1 (close_Sc_wrt_T β1 Sc1) ->
  degree_Sc_wrt_T 0 Sc1.
Proof.
unfold_singletons; exact degree_Sc_wrt_T_close_Sc_wrt_T_inv.
Qed.

#[export] Hint Immediate degree_Sc_wrt_T_close_Sc_wrt_T_inv : lngen.

Lemma degree_Tm_wrt_T_close_Tm_wrt_T_inv :
forall t1 β1,
  degree_Tm_wrt_T 1 (close_Tm_wrt_T β1 t1) ->
  degree_Tm_wrt_T 0 t1.
Proof.
unfold_singletons; exact degree_Tm_wrt_T_close_Tm_wrt_T_inv.
Qed.

#[export] Hint Immediate degree_Tm_wrt_T_close_Tm_wrt_T_inv : lngen.

Lemma degree_Tm_wrt_T_close_Tm_wrt_Tm_inv :
forall t1 tx1 n1,
  degree_Tm_wrt_T n1 (close_Tm_wrt_Tm tx1 t1) ->
  degree_Tm_wrt_T n1 t1.
Proof.
unfold_singletons; exact degree_Tm_wrt_T_close_Tm_wrt_Tm_inv.
Qed.

#[export] Hint Immediate degree_Tm_wrt_T_close_Tm_wrt_Tm_inv : lngen.

Lemma degree_Tm_wrt_Tm_close_Tm_wrt_T_inv :
forall t1 β1 n1,
  degree_Tm_wrt_Tm n1 (close_Tm_wrt_T β1 t1) ->
  degree_Tm_wrt_Tm n1 t1.
Proof.
unfold_singletons; exact degree_Tm_wrt_Tm_close_Tm_wrt_T_inv.
Qed.

#[export] Hint Immediate degree_Tm_wrt_Tm_close_Tm_wrt_T_inv : lngen.

Lemma degree_Tm_wrt_Tm_close_Tm_wrt_Tm_inv :
forall t1 tx1,
  degree_Tm_wrt_Tm 1 (close_Tm_wrt_Tm tx1 t1) ->
  degree_Tm_wrt_Tm 0 t1.
Proof.
unfold_singletons; exact degree_Tm_wrt_Tm_close_Tm_wrt_Tm_inv.
Qed.

#[export] Hint Immediate degree_Tm_wrt_Tm_close_Tm_wrt_Tm_inv : lngen.

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

Lemma degree_Ex_wrt_Ex_open_Ex_wrt_Ex :
forall e1 e2,
  degree_Ex_wrt_Ex 1 e1 ->
  degree_Ex_wrt_Ex 0 e2 ->
  degree_Ex_wrt_Ex 0 (open_Ex_wrt_Ex e1 e2).
Proof.
unfold_singletons; exact degree_Ex_wrt_Ex_open_Ex_wrt_Ex.
Qed.

#[export] Hint Resolve degree_Ex_wrt_Ex_open_Ex_wrt_Ex : lngen.

Lemma degree_T_wrt_T_open_T_wrt_T :
forall T1 T2,
  degree_T_wrt_T 1 T1 ->
  degree_T_wrt_T 0 T2 ->
  degree_T_wrt_T 0 (open_T_wrt_T T1 T2).
Proof.
unfold_singletons; exact degree_T_wrt_T_open_T_wrt_T.
Qed.

#[export] Hint Resolve degree_T_wrt_T_open_T_wrt_T : lngen.

Lemma degree_Sc_wrt_T_open_Sc_wrt_T :
forall Sc1 T1,
  degree_Sc_wrt_T 1 Sc1 ->
  degree_T_wrt_T 0 T1 ->
  degree_Sc_wrt_T 0 (open_Sc_wrt_T Sc1 T1).
Proof.
unfold_singletons; exact degree_Sc_wrt_T_open_Sc_wrt_T.
Qed.

#[export] Hint Resolve degree_Sc_wrt_T_open_Sc_wrt_T : lngen.

Lemma degree_Tm_wrt_T_open_Tm_wrt_T :
forall t1 T1,
  degree_Tm_wrt_T 1 t1 ->
  degree_T_wrt_T 0 T1 ->
  degree_Tm_wrt_T 0 (open_Tm_wrt_T t1 T1).
Proof.
unfold_singletons; exact degree_Tm_wrt_T_open_Tm_wrt_T.
Qed.

#[export] Hint Resolve degree_Tm_wrt_T_open_Tm_wrt_T : lngen.

Lemma degree_Tm_wrt_T_open_Tm_wrt_Tm :
forall t1 t2 n1,
  degree_Tm_wrt_T n1 t1 ->
  degree_Tm_wrt_T n1 t2 ->
  degree_Tm_wrt_T n1 (open_Tm_wrt_Tm t1 t2).
Proof.
unfold_singletons; exact degree_Tm_wrt_T_open_Tm_wrt_Tm.
Qed.

#[export] Hint Resolve degree_Tm_wrt_T_open_Tm_wrt_Tm : lngen.

Lemma degree_Tm_wrt_Tm_open_Tm_wrt_T :
forall t1 T1 n1,
  degree_Tm_wrt_Tm n1 t1 ->
  degree_Tm_wrt_Tm n1 (open_Tm_wrt_T t1 T1).
Proof.
unfold_singletons; exact degree_Tm_wrt_Tm_open_Tm_wrt_T.
Qed.

#[export] Hint Resolve degree_Tm_wrt_Tm_open_Tm_wrt_T : lngen.

Lemma degree_Tm_wrt_Tm_open_Tm_wrt_Tm :
forall t1 t2,
  degree_Tm_wrt_Tm 1 t1 ->
  degree_Tm_wrt_Tm 0 t2 ->
  degree_Tm_wrt_Tm 0 (open_Tm_wrt_Tm t1 t2).
Proof.
unfold_singletons; exact degree_Tm_wrt_Tm_open_Tm_wrt_Tm.
Qed.

#[export] Hint Resolve degree_Tm_wrt_Tm_open_Tm_wrt_Tm : lngen.

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

Lemma degree_Ex_wrt_Ex_open_Ex_wrt_Ex_inv :
forall e1 e2,
  degree_Ex_wrt_Ex 0 (open_Ex_wrt_Ex e1 e2) ->
  degree_Ex_wrt_Ex 1 e1.
Proof.
unfold_singletons; exact degree_Ex_wrt_Ex_open_Ex_wrt_Ex_inv.
Qed.

#[export] Hint Immediate degree_Ex_wrt_Ex_open_Ex_wrt_Ex_inv : lngen.

Lemma degree_T_wrt_T_open_T_wrt_T_inv :
forall T1 T2,
  degree_T_wrt_T 0 (open_T_wrt_T T1 T2) ->
  degree_T_wrt_T 1 T1.
Proof.
unfold_singletons; exact degree_T_wrt_T_open_T_wrt_T_inv.
Qed.

#[export] Hint Immediate degree_T_wrt_T_open_T_wrt_T_inv : lngen.

Lemma degree_Sc_wrt_T_open_Sc_wrt_T_inv :
forall Sc1 T1,
  degree_Sc_wrt_T 0 (open_Sc_wrt_T Sc1 T1) ->
  degree_Sc_wrt_T 1 Sc1.
Proof.
unfold_singletons; exact degree_Sc_wrt_T_open_Sc_wrt_T_inv.
Qed.

#[export] Hint Immediate degree_Sc_wrt_T_open_Sc_wrt_T_inv : lngen.

Lemma degree_Tm_wrt_T_open_Tm_wrt_T_inv :
forall t1 T1,
  degree_Tm_wrt_T 0 (open_Tm_wrt_T t1 T1) ->
  degree_Tm_wrt_T 1 t1.
Proof.
unfold_singletons; exact degree_Tm_wrt_T_open_Tm_wrt_T_inv.
Qed.

#[export] Hint Immediate degree_Tm_wrt_T_open_Tm_wrt_T_inv : lngen.

Lemma degree_Tm_wrt_T_open_Tm_wrt_Tm_inv :
forall t1 t2 n1,
  degree_Tm_wrt_T n1 (open_Tm_wrt_Tm t1 t2) ->
  degree_Tm_wrt_T n1 t1.
Proof.
unfold_singletons; exact degree_Tm_wrt_T_open_Tm_wrt_Tm_inv.
Qed.

#[export] Hint Immediate degree_Tm_wrt_T_open_Tm_wrt_Tm_inv : lngen.

Lemma degree_Tm_wrt_Tm_open_Tm_wrt_T_inv :
forall t1 T1 n1,
  degree_Tm_wrt_Tm n1 (open_Tm_wrt_T t1 T1) ->
  degree_Tm_wrt_Tm n1 t1.
Proof.
unfold_singletons; exact degree_Tm_wrt_Tm_open_Tm_wrt_T_inv.
Qed.

#[export] Hint Immediate degree_Tm_wrt_Tm_open_Tm_wrt_T_inv : lngen.

Lemma degree_Tm_wrt_Tm_open_Tm_wrt_Tm_inv :
forall t1 t2,
  degree_Tm_wrt_Tm 0 (open_Tm_wrt_Tm t1 t2) ->
  degree_Tm_wrt_Tm 1 t1.
Proof.
unfold_singletons; exact degree_Tm_wrt_Tm_open_Tm_wrt_Tm_inv.
Qed.

#[export] Hint Immediate degree_Tm_wrt_Tm_open_Tm_wrt_Tm_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

(*ltac removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

Lemma close_Ex_wrt_Ex_inj :
forall e1 e2 x1,
  close_Ex_wrt_Ex x1 e1 = close_Ex_wrt_Ex x1 e2 ->
  e1 = e2.
Proof.
unfold_singletons; exact close_Ex_wrt_Ex_inj.
Qed.

#[export] Hint Immediate close_Ex_wrt_Ex_inj : lngen.

Lemma close_T_wrt_T_inj :
forall T1 T2 β1,
  close_T_wrt_T β1 T1 = close_T_wrt_T β1 T2 ->
  T1 = T2.
Proof.
unfold_singletons; exact close_T_wrt_T_inj.
Qed.

#[export] Hint Immediate close_T_wrt_T_inj : lngen.

Lemma close_Sc_wrt_T_inj :
forall Sc1 Sc2 β1,
  close_Sc_wrt_T β1 Sc1 = close_Sc_wrt_T β1 Sc2 ->
  Sc1 = Sc2.
Proof.
unfold_singletons; exact close_Sc_wrt_T_inj.
Qed.

#[export] Hint Immediate close_Sc_wrt_T_inj : lngen.

Lemma close_Tm_wrt_T_inj :
forall t1 t2 β1,
  close_Tm_wrt_T β1 t1 = close_Tm_wrt_T β1 t2 ->
  t1 = t2.
Proof.
unfold_singletons; exact close_Tm_wrt_T_inj.
Qed.

#[export] Hint Immediate close_Tm_wrt_T_inj : lngen.

Lemma close_Tm_wrt_Tm_inj :
forall t1 t2 tx1,
  close_Tm_wrt_Tm tx1 t1 = close_Tm_wrt_Tm tx1 t2 ->
  t1 = t2.
Proof.
unfold_singletons; exact close_Tm_wrt_Tm_inj.
Qed.

#[export] Hint Immediate close_Tm_wrt_Tm_inj : lngen.

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

Lemma close_Ex_wrt_Ex_open_Ex_wrt_Ex :
forall e1 x1,
  x1 ∉ fv_Ex e1 ->
  close_Ex_wrt_Ex x1 (open_Ex_wrt_Ex e1 (e__Var_f x1)) = e1.
Proof.
unfold_singletons; exact close_Ex_wrt_Ex_open_Ex_wrt_Ex.
Qed.

#[export] Hint Resolve close_Ex_wrt_Ex_open_Ex_wrt_Ex : lngen.
#[export] Hint Rewrite close_Ex_wrt_Ex_open_Ex_wrt_Ex using solve [auto] : lngen.

Lemma close_T_wrt_T_open_T_wrt_T :
forall T1 β1,
  β1 ∉ fsk T1 ->
  close_T_wrt_T β1 (open_T_wrt_T T1 (T__Var_f β1)) = T1.
Proof.
unfold_singletons; exact close_T_wrt_T_open_T_wrt_T.
Qed.

#[export] Hint Resolve close_T_wrt_T_open_T_wrt_T : lngen.
#[export] Hint Rewrite close_T_wrt_T_open_T_wrt_T using solve [auto] : lngen.

Lemma close_Sc_wrt_T_open_Sc_wrt_T :
forall Sc1 β1,
  β1 ∉ fsk Sc1 ->
  close_Sc_wrt_T β1 (open_Sc_wrt_T Sc1 (T__Var_f β1)) = Sc1.
Proof.
unfold_singletons; exact close_Sc_wrt_T_open_Sc_wrt_T.
Qed.

#[export] Hint Resolve close_Sc_wrt_T_open_Sc_wrt_T : lngen.
#[export] Hint Rewrite close_Sc_wrt_T_open_Sc_wrt_T using solve [auto] : lngen.

Lemma close_Tm_wrt_T_open_Tm_wrt_T :
forall t1 β1,
  β1 ∉ fsk t1 ->
  close_Tm_wrt_T β1 (open_Tm_wrt_T t1 (T__Var_f β1)) = t1.
Proof.
unfold_singletons; exact close_Tm_wrt_T_open_Tm_wrt_T.
Qed.

#[export] Hint Resolve close_Tm_wrt_T_open_Tm_wrt_T : lngen.
#[export] Hint Rewrite close_Tm_wrt_T_open_Tm_wrt_T using solve [auto] : lngen.

Lemma close_Tm_wrt_Tm_open_Tm_wrt_Tm :
forall t1 tx1,
  tx1 ∉ fv t1 ->
  close_Tm_wrt_Tm tx1 (open_Tm_wrt_Tm t1 (t__Var_f tx1)) = t1.
Proof.
unfold_singletons; exact close_Tm_wrt_Tm_open_Tm_wrt_Tm.
Qed.

#[export] Hint Resolve close_Tm_wrt_Tm_open_Tm_wrt_Tm : lngen.
#[export] Hint Rewrite close_Tm_wrt_Tm_open_Tm_wrt_Tm using solve [auto] : lngen.

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

Lemma open_Ex_wrt_Ex_close_Ex_wrt_Ex :
forall e1 x1,
  open_Ex_wrt_Ex (close_Ex_wrt_Ex x1 e1) (e__Var_f x1) = e1.
Proof.
unfold_singletons; exact open_Ex_wrt_Ex_close_Ex_wrt_Ex.
Qed.

#[export] Hint Resolve open_Ex_wrt_Ex_close_Ex_wrt_Ex : lngen.
#[export] Hint Rewrite open_Ex_wrt_Ex_close_Ex_wrt_Ex using solve [auto] : lngen.

Lemma open_T_wrt_T_close_T_wrt_T :
forall T1 β1,
  open_T_wrt_T (close_T_wrt_T β1 T1) (T__Var_f β1) = T1.
Proof.
unfold_singletons; exact open_T_wrt_T_close_T_wrt_T.
Qed.

#[export] Hint Resolve open_T_wrt_T_close_T_wrt_T : lngen.
#[export] Hint Rewrite open_T_wrt_T_close_T_wrt_T using solve [auto] : lngen.

Lemma open_Sc_wrt_T_close_Sc_wrt_T :
forall Sc1 β1,
  open_Sc_wrt_T (close_Sc_wrt_T β1 Sc1) (T__Var_f β1) = Sc1.
Proof.
unfold_singletons; exact open_Sc_wrt_T_close_Sc_wrt_T.
Qed.

#[export] Hint Resolve open_Sc_wrt_T_close_Sc_wrt_T : lngen.
#[export] Hint Rewrite open_Sc_wrt_T_close_Sc_wrt_T using solve [auto] : lngen.

Lemma open_Tm_wrt_T_close_Tm_wrt_T :
forall t1 β1,
  open_Tm_wrt_T (close_Tm_wrt_T β1 t1) (T__Var_f β1) = t1.
Proof.
unfold_singletons; exact open_Tm_wrt_T_close_Tm_wrt_T.
Qed.

#[export] Hint Resolve open_Tm_wrt_T_close_Tm_wrt_T : lngen.
#[export] Hint Rewrite open_Tm_wrt_T_close_Tm_wrt_T using solve [auto] : lngen.

Lemma open_Tm_wrt_Tm_close_Tm_wrt_Tm :
forall t1 tx1,
  open_Tm_wrt_Tm (close_Tm_wrt_Tm tx1 t1) (t__Var_f tx1) = t1.
Proof.
unfold_singletons; exact open_Tm_wrt_Tm_close_Tm_wrt_Tm.
Qed.

#[export] Hint Resolve open_Tm_wrt_Tm_close_Tm_wrt_Tm : lngen.
#[export] Hint Rewrite open_Tm_wrt_Tm_close_Tm_wrt_Tm using solve [auto] : lngen.

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

Lemma open_Ex_wrt_Ex_inj :
forall e2 e1 x1,
  x1 ∉ fv_Ex e2 ->
  x1 ∉ fv_Ex e1 ->
  open_Ex_wrt_Ex e2 (e__Var_f x1) = open_Ex_wrt_Ex e1 (e__Var_f x1) ->
  e2 = e1.
Proof.
unfold_singletons; exact open_Ex_wrt_Ex_inj.
Qed.

#[export] Hint Immediate open_Ex_wrt_Ex_inj : lngen.

Lemma open_T_wrt_T_inj :
forall T2 T1 β1,
  β1 ∉ fsk T2 ->
  β1 ∉ fsk T1 ->
  open_T_wrt_T T2 (T__Var_f β1) = open_T_wrt_T T1 (T__Var_f β1) ->
  T2 = T1.
Proof.
unfold_singletons; exact open_T_wrt_T_inj.
Qed.

#[export] Hint Immediate open_T_wrt_T_inj : lngen.

Lemma open_Sc_wrt_T_inj :
forall Sc2 Sc1 β1,
  β1 ∉ fsk Sc2 ->
  β1 ∉ fsk Sc1 ->
  open_Sc_wrt_T Sc2 (T__Var_f β1) = open_Sc_wrt_T Sc1 (T__Var_f β1) ->
  Sc2 = Sc1.
Proof.
unfold_singletons; exact open_Sc_wrt_T_inj.
Qed.

#[export] Hint Immediate open_Sc_wrt_T_inj : lngen.

Lemma open_Tm_wrt_T_inj :
forall t2 t1 β1,
  β1 ∉ fsk t2 ->
  β1 ∉ fsk t1 ->
  open_Tm_wrt_T t2 (T__Var_f β1) = open_Tm_wrt_T t1 (T__Var_f β1) ->
  t2 = t1.
Proof.
unfold_singletons; exact open_Tm_wrt_T_inj.
Qed.

#[export] Hint Immediate open_Tm_wrt_T_inj : lngen.

Lemma open_Tm_wrt_Tm_inj :
forall t2 t1 tx1,
  tx1 ∉ fv t2 ->
  tx1 ∉ fv t1 ->
  open_Tm_wrt_Tm t2 (t__Var_f tx1) = open_Tm_wrt_Tm t1 (t__Var_f tx1) ->
  t2 = t1.
Proof.
unfold_singletons; exact open_Tm_wrt_Tm_inj.
Qed.

#[export] Hint Immediate open_Tm_wrt_Tm_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

(*ltac removed*)

(*hidden lems removed*)

Lemma degree_Ex_wrt_Ex_of_lc_Ex :
forall e1,
  lc e1 ->
  degree_Ex_wrt_Ex 0 e1.
Proof.
unfold_singletons; exact degree_Ex_wrt_Ex_of_lc_Ex.
Qed.

#[export] Hint Resolve degree_Ex_wrt_Ex_of_lc_Ex : lngen.

(*hidden lems removed*)

Lemma degree_T_wrt_T_of_lc_T :
forall T1,
  lc T1 ->
  degree_T_wrt_T 0 T1.
Proof.
unfold_singletons; exact degree_T_wrt_T_of_lc_T.
Qed.

#[export] Hint Resolve degree_T_wrt_T_of_lc_T : lngen.

(*hidden lems removed*)

Lemma degree_Sc_wrt_T_of_lc_Sc :
forall Sc1,
  lc Sc1 ->
  degree_Sc_wrt_T 0 Sc1.
Proof.
unfold_singletons; exact degree_Sc_wrt_T_of_lc_Sc.
Qed.

#[export] Hint Resolve degree_Sc_wrt_T_of_lc_Sc : lngen.

(*hidden lems removed*)

Lemma degree_Tm_wrt_T_of_lc_Tm :
forall t1,
  lc (X:=Tm) t1 ->
  degree_Tm_wrt_T 0 t1.
Proof.
unfold_singletons; exact degree_Tm_wrt_T_of_lc_Tm.
Qed.

#[export] Hint Resolve degree_Tm_wrt_T_of_lc_Tm : lngen.

(*hidden lems removed*)

Lemma degree_Tm_wrt_Tm_of_lc_Tm :
forall t1,
  lc (X:=Tm) t1 ->
  degree_Tm_wrt_Tm 0 t1.
Proof.
unfold_singletons; exact degree_Tm_wrt_Tm_of_lc_Tm.
Qed.

#[export] Hint Resolve degree_Tm_wrt_Tm_of_lc_Tm : lngen.

(*hidden lems removed*)

Lemma lc_Ex_of_degree :
forall e1,
  degree_Ex_wrt_Ex 0 e1 ->
  lc e1.
Proof.
unfold_singletons; exact lc_Ex_of_degree.
Qed.

#[export] Hint Resolve lc_Ex_of_degree : lngen.

(*hidden lems removed*)

Lemma lc_T_of_degree :
forall T1,
  degree_T_wrt_T 0 T1 ->
  lc T1.
Proof.
unfold_singletons; exact lc_T_of_degree.
Qed.

#[export] Hint Resolve lc_T_of_degree : lngen.

(*hidden lems removed*)

Lemma lc_Sc_of_degree :
forall Sc1,
  degree_Sc_wrt_T 0 Sc1 ->
  lc Sc1.
Proof.
unfold_singletons; exact lc_Sc_of_degree.
Qed.

#[export] Hint Resolve lc_Sc_of_degree : lngen.

(*hidden lems removed*)

Lemma lc_Tm_of_degree :
forall t1,
  degree_Tm_wrt_T 0 t1 ->
  degree_Tm_wrt_Tm 0 t1 ->
  lc (X:=Tm) t1.
Proof.
unfold_singletons; exact lc_Tm_of_degree.
Qed.

#[export] Hint Resolve lc_Tm_of_degree : lngen.

(*ltac removed*)

(*ltac removed*)

(*ltac removed*)

(*ltac removed*)

Lemma lc_e__Lam_exists :
forall x1 e1,
  lc (open_Ex_wrt_Ex e1 (e__Var_f x1)) ->
  lc (e__Lam e1).
Proof.
unfold_singletons; exact lc_e__Lam_exists.
Qed.

Lemma lc_e__Let_exists :
forall x1 e1 e2,
  lc e1 ->
  lc (open_Ex_wrt_Ex e2 (e__Var_f x1)) ->
  lc (e__Let e1 e2).
Proof.
unfold_singletons; exact lc_e__Let_exists.
Qed.

Lemma lc_S__Forall_exists :
forall α1 σ1,
  lc (open_Sc_wrt_T σ1 (T__Var_f α1)) ->
  lc (S__Forall σ1).
Proof.
unfold_singletons; exact lc_S__Forall_exists.
Qed.

Lemma lc_t__Lam_exists :
forall tx1 τ1 t1,
  lc τ1 ->
  lc (X:=Tm) (open_Tm_wrt_Tm t1 (t__Var_f tx1)) ->
  lc (X:=Tm) (t__Lam τ1 t1).
Proof.
unfold_singletons; exact lc_t__Lam_exists.
Qed.

Lemma lc_t__TLam_exists :
forall α1 t1,
  lc (X:=Tm) (open_Tm_wrt_T t1 (T__Var_f α1)) ->
  lc (X:=Tm) (t__TLam t1).
Proof.
unfold_singletons; exact lc_t__TLam_exists.
Qed.

#[export] Hint Extern 1 (lc (e__Lam _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_e__Lam_exists x1) : core.

#[export] Hint Extern 1 (lc (e__Let _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_e__Let_exists x1) : core.

#[export] Hint Extern 1 (lc (S__Forall _)) =>
  let α1 := fresh in
  pick_fresh α1;
  apply (lc_S__Forall_exists α1) : core.

#[export] Hint Extern 1 (lc (X:=Tm) (t__Lam _ _)) =>
  let tx1 := fresh in
  pick_fresh tx1;
  apply (lc_t__Lam_exists tx1) : core.

#[export] Hint Extern 1 (lc (X:=Tm) (t__TLam _)) =>
  let α1 := fresh in
  pick_fresh α1;
  apply (lc_t__TLam_exists α1) : core.

Lemma lc_body_Ex_wrt_Ex :
forall e1 e2,
  body_Ex_wrt_Ex e1 ->
  lc e2 ->
  lc (open_Ex_wrt_Ex e1 e2).
Proof.
unfold_singletons; exact lc_body_Ex_wrt_Ex.
Qed.

#[export] Hint Resolve lc_body_Ex_wrt_Ex : lngen.

Lemma lc_body_T_wrt_T :
forall T1 T2,
  body_T_wrt_T T1 ->
  lc T2 ->
  lc (open_T_wrt_T T1 T2).
Proof.
unfold_singletons; exact lc_body_T_wrt_T.
Qed.

#[export] Hint Resolve lc_body_T_wrt_T : lngen.

Lemma lc_body_Sc_wrt_T :
forall Sc1 T1,
  body_Sc_wrt_T Sc1 ->
  lc T1 ->
  lc (open_Sc_wrt_T Sc1 T1).
Proof.
unfold_singletons; exact lc_body_Sc_wrt_T.
Qed.

#[export] Hint Resolve lc_body_Sc_wrt_T : lngen.

Lemma lc_body_Tm_wrt_T :
forall t1 T1,
  body_Tm_wrt_T t1 ->
  lc T1 ->
  lc (X:=Tm) (open_Tm_wrt_T t1 T1).
Proof.
unfold_singletons; exact lc_body_Tm_wrt_T.
Qed.

#[export] Hint Resolve lc_body_Tm_wrt_T : lngen.

Lemma lc_body_Tm_wrt_Tm :
forall t1 t2,
  body_Tm_wrt_Tm t1 ->
  lc (X:=Tm) t2 ->
  lc (X:=Tm) (open_Tm_wrt_Tm t1 t2).
Proof.
unfold_singletons; exact lc_body_Tm_wrt_Tm.
Qed.

#[export] Hint Resolve lc_body_Tm_wrt_Tm : lngen.

Lemma lc_body_e__Lam_1 :
forall e1,
  lc (e__Lam e1) ->
  body_Ex_wrt_Ex e1.
Proof.
unfold_singletons; exact lc_body_e__Lam_1.
Qed.

#[export] Hint Resolve lc_body_e__Lam_1 : lngen.

Lemma lc_body_e__Let_2 :
forall e1 e2,
  lc (e__Let e1 e2) ->
  body_Ex_wrt_Ex e2.
Proof.
unfold_singletons; exact lc_body_e__Let_2.
Qed.

#[export] Hint Resolve lc_body_e__Let_2 : lngen.

Lemma lc_body_S__Forall_1 :
forall σ1,
  lc (S__Forall σ1) ->
  body_Sc_wrt_T σ1.
Proof.
unfold_singletons; exact lc_body_S__Forall_1.
Qed.

#[export] Hint Resolve lc_body_S__Forall_1 : lngen.

Lemma lc_body_t__Lam_2 :
forall τ1 t1,
  lc (X:=Tm) (t__Lam τ1 t1) ->
  body_Tm_wrt_Tm t1.
Proof.
unfold_singletons; exact lc_body_t__Lam_2.
Qed.

#[export] Hint Resolve lc_body_t__Lam_2 : lngen.

Lemma lc_body_t__TLam_1 :
forall t1,
  lc (X:=Tm) (t__TLam t1) ->
  body_Tm_wrt_T t1.
Proof.
unfold_singletons; exact lc_body_t__TLam_1.
Qed.

#[export] Hint Resolve lc_body_t__TLam_1 : lngen.

(*hidden lems removed*)

(*hidden unique removed*)

(*hidden lems removed*)

Lemma lc_Ex_of_lc_set_Ex :
forall e1, lc_set_Ex e1 -> lc e1.
Proof.
unfold_singletons; exact lc_Ex_of_lc_set_Ex.
Qed.

#[export] Hint Resolve lc_Ex_of_lc_set_Ex : lngen.

(*hidden lems removed*)

Lemma lc_T_of_lc_set_T :
forall T1, lc_set_T T1 -> lc T1.
Proof.
unfold_singletons; exact lc_T_of_lc_set_T.
Qed.

#[export] Hint Resolve lc_T_of_lc_set_T : lngen.

(*hidden lems removed*)

Lemma lc_Sc_of_lc_set_Sc :
forall Sc1, lc_set_Sc Sc1 -> lc Sc1.
Proof.
unfold_singletons; exact lc_Sc_of_lc_set_Sc.
Qed.

#[export] Hint Resolve lc_Sc_of_lc_set_Sc : lngen.

(*hidden lems removed*)

Lemma lc_Tm_of_lc_set_Tm :
forall t1, lc_set_Tm t1 -> lc (X:=Tm) t1.
Proof.
unfold_singletons; exact lc_Tm_of_lc_set_Tm.
Qed.

#[export] Hint Resolve lc_Tm_of_lc_set_Tm : lngen.

(*hidden lems removed*)

Lemma lc_set_Ex_of_lc_Ex :
forall e1,
  lc e1 ->
  lc_set_Ex e1.
Proof.
unfold_singletons; exact lc_set_Ex_of_lc_Ex.
Qed.

#[export] Hint Resolve lc_set_Ex_of_lc_Ex : lngen.

(*hidden lems removed*)

Lemma lc_set_T_of_lc_T :
forall T1,
  lc T1 ->
  lc_set_T T1.
Proof.
unfold_singletons; exact lc_set_T_of_lc_T.
Qed.

#[export] Hint Resolve lc_set_T_of_lc_T : lngen.

(*hidden lems removed*)

Lemma lc_set_Sc_of_lc_Sc :
forall Sc1,
  lc Sc1 ->
  lc_set_Sc Sc1.
Proof.
unfold_singletons; exact lc_set_Sc_of_lc_Sc.
Qed.

#[export] Hint Resolve lc_set_Sc_of_lc_Sc : lngen.

(*hidden lems removed*)

Lemma lc_set_Tm_of_lc_Tm :
forall t1,
  lc (X:=Tm) t1 ->
  lc_set_Tm t1.
Proof.
unfold_singletons; exact lc_set_Tm_of_lc_Tm.
Qed.

#[export] Hint Resolve lc_set_Tm_of_lc_Tm : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

(*ltac removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

Lemma close_Ex_wrt_Ex_lc_Ex :
forall e1 x1,
  lc e1 ->
  x1 ∉ fv_Ex e1 ->
  close_Ex_wrt_Ex x1 e1 = e1.
Proof.
unfold_singletons; exact close_Ex_wrt_Ex_lc_Ex.
Qed.

#[export] Hint Resolve close_Ex_wrt_Ex_lc_Ex : lngen.
#[export] Hint Rewrite close_Ex_wrt_Ex_lc_Ex using solve [auto] : lngen.

Lemma close_T_wrt_T_lc_T :
forall T1 β1,
  lc T1 ->
  β1 ∉ fsk T1 ->
  close_T_wrt_T β1 T1 = T1.
Proof.
unfold_singletons; exact close_T_wrt_T_lc_T.
Qed.

#[export] Hint Resolve close_T_wrt_T_lc_T : lngen.
#[export] Hint Rewrite close_T_wrt_T_lc_T using solve [auto] : lngen.

Lemma close_Sc_wrt_T_lc_Sc :
forall Sc1 β1,
  lc Sc1 ->
  β1 ∉ fsk Sc1 ->
  close_Sc_wrt_T β1 Sc1 = Sc1.
Proof.
unfold_singletons; exact close_Sc_wrt_T_lc_Sc.
Qed.

#[export] Hint Resolve close_Sc_wrt_T_lc_Sc : lngen.
#[export] Hint Rewrite close_Sc_wrt_T_lc_Sc using solve [auto] : lngen.

Lemma close_Tm_wrt_T_lc_Tm :
forall t1 β1,
  lc (X:=Tm) t1 ->
  β1 ∉ fsk t1 ->
  close_Tm_wrt_T β1 t1 = t1.
Proof.
unfold_singletons; exact close_Tm_wrt_T_lc_Tm.
Qed.

#[export] Hint Resolve close_Tm_wrt_T_lc_Tm : lngen.
#[export] Hint Rewrite close_Tm_wrt_T_lc_Tm using solve [auto] : lngen.

Lemma close_Tm_wrt_Tm_lc_Tm :
forall t1 tx1,
  lc (X:=Tm) t1 ->
  tx1 ∉ fv t1 ->
  close_Tm_wrt_Tm tx1 t1 = t1.
Proof.
unfold_singletons; exact close_Tm_wrt_Tm_lc_Tm.
Qed.

#[export] Hint Resolve close_Tm_wrt_Tm_lc_Tm : lngen.
#[export] Hint Rewrite close_Tm_wrt_Tm_lc_Tm using solve [auto] : lngen.

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

Lemma open_Ex_wrt_Ex_lc_Ex :
forall e2 e1,
  lc e2 ->
  open_Ex_wrt_Ex e2 e1 = e2.
Proof.
unfold_singletons; exact open_Ex_wrt_Ex_lc_Ex.
Qed.

#[export] Hint Resolve open_Ex_wrt_Ex_lc_Ex : lngen.
#[export] Hint Rewrite open_Ex_wrt_Ex_lc_Ex using solve [auto] : lngen.

Lemma open_T_wrt_T_lc_T :
forall T2 T1,
  lc T2 ->
  open_T_wrt_T T2 T1 = T2.
Proof.
unfold_singletons; exact open_T_wrt_T_lc_T.
Qed.

#[export] Hint Resolve open_T_wrt_T_lc_T : lngen.
#[export] Hint Rewrite open_T_wrt_T_lc_T using solve [auto] : lngen.

Lemma open_Sc_wrt_T_lc_Sc :
forall Sc1 T1,
  lc Sc1 ->
  open_Sc_wrt_T Sc1 T1 = Sc1.
Proof.
unfold_singletons; exact open_Sc_wrt_T_lc_Sc.
Qed.

#[export] Hint Resolve open_Sc_wrt_T_lc_Sc : lngen.
#[export] Hint Rewrite open_Sc_wrt_T_lc_Sc using solve [auto] : lngen.

Lemma open_Tm_wrt_T_lc_Tm :
forall t1 T1,
  lc (X:=Tm) t1 ->
  open_Tm_wrt_T t1 T1 = t1.
Proof.
unfold_singletons; exact open_Tm_wrt_T_lc_Tm.
Qed.

#[export] Hint Resolve open_Tm_wrt_T_lc_Tm : lngen.
#[export] Hint Rewrite open_Tm_wrt_T_lc_Tm using solve [auto] : lngen.

Lemma open_Tm_wrt_Tm_lc_Tm :
forall t2 t1,
  lc (X:=Tm) t2 ->
  open_Tm_wrt_Tm t2 t1 = t2.
Proof.
unfold_singletons; exact open_Tm_wrt_Tm_lc_Tm.
Qed.

#[export] Hint Resolve open_Tm_wrt_Tm_lc_Tm : lngen.
#[export] Hint Rewrite open_Tm_wrt_Tm_lc_Tm using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

(*ltac removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

Lemma fv_Ex_close_Ex_wrt_Ex :
forall e1 x1,
  fv_Ex (close_Ex_wrt_Ex x1 e1) ≡ remove x1 (fv_Ex e1).
Proof.
unfold_singletons; exact fv_Ex_close_Ex_wrt_Ex.
Qed.

#[export] Hint Resolve fv_Ex_close_Ex_wrt_Ex : lngen.
#[export] Hint Rewrite fv_Ex_close_Ex_wrt_Ex using solve [auto] : lngen.

Lemma fsk_T_close_T_wrt_T :
forall T1 β1,
  fsk (close_T_wrt_T β1 T1) ≡ remove β1 (fsk T1).
Proof.
unfold_singletons; exact fsk_T_close_T_wrt_T.
Qed.

#[export] Hint Resolve fsk_T_close_T_wrt_T : lngen.
#[export] Hint Rewrite fsk_T_close_T_wrt_T using solve [auto] : lngen.

Lemma fsk_Sc_close_Sc_wrt_T :
forall Sc1 β1,
  fsk (close_Sc_wrt_T β1 Sc1) ≡ remove β1 (fsk Sc1).
Proof.
unfold_singletons; exact fsk_Sc_close_Sc_wrt_T.
Qed.

#[export] Hint Resolve fsk_Sc_close_Sc_wrt_T : lngen.
#[export] Hint Rewrite fsk_Sc_close_Sc_wrt_T using solve [auto] : lngen.

Lemma fsk_Tm_close_Tm_wrt_T :
forall t1 β1,
  fsk (close_Tm_wrt_T β1 t1) ≡ remove β1 (fsk t1).
Proof.
unfold_singletons; exact fsk_Tm_close_Tm_wrt_T.
Qed.

#[export] Hint Resolve fsk_Tm_close_Tm_wrt_T : lngen.
#[export] Hint Rewrite fsk_Tm_close_Tm_wrt_T using solve [auto] : lngen.

Lemma fsk_Tm_close_Tm_wrt_Tm :
forall t1 tx1,
  fsk (close_Tm_wrt_Tm tx1 t1) ≡ fsk t1.
Proof.
unfold_singletons; exact fsk_Tm_close_Tm_wrt_Tm.
Qed.

#[export] Hint Resolve fsk_Tm_close_Tm_wrt_Tm : lngen.
#[export] Hint Rewrite fsk_Tm_close_Tm_wrt_Tm using solve [auto] : lngen.

Lemma ftv_Tm_close_Tm_wrt_T :
forall t1 β1,
  fv (close_Tm_wrt_T β1 t1) ≡ fv t1.
Proof.
unfold_singletons; exact ftv_Tm_close_Tm_wrt_T.
Qed.

#[export] Hint Resolve ftv_Tm_close_Tm_wrt_T : lngen.
#[export] Hint Rewrite ftv_Tm_close_Tm_wrt_T using solve [auto] : lngen.

Lemma ftv_Tm_close_Tm_wrt_Tm :
forall t1 tx1,
  fv (close_Tm_wrt_Tm tx1 t1) ≡ remove tx1 (fv t1).
Proof.
unfold_singletons; exact ftv_Tm_close_Tm_wrt_Tm.
Qed.

#[export] Hint Resolve ftv_Tm_close_Tm_wrt_Tm : lngen.
#[export] Hint Rewrite ftv_Tm_close_Tm_wrt_Tm using solve [auto] : lngen.

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

Lemma fv_Ex_open_Ex_wrt_Ex_lower :
forall e1 e2,
  fv_Ex e1 ⊆ fv_Ex (open_Ex_wrt_Ex e1 e2).
Proof.
unfold_singletons; exact fv_Ex_open_Ex_wrt_Ex_lower.
Qed.

#[export] Hint Resolve fv_Ex_open_Ex_wrt_Ex_lower : lngen.

Lemma fsk_T_open_T_wrt_T_lower :
forall T1 T2,
  fsk T1 ⊆ fsk (open_T_wrt_T T1 T2).
Proof.
unfold_singletons; exact fsk_T_open_T_wrt_T_lower.
Qed.

#[export] Hint Resolve fsk_T_open_T_wrt_T_lower : lngen.

Lemma fsk_Sc_open_Sc_wrt_T_lower :
forall Sc1 T1,
  fsk Sc1 ⊆ fsk (open_Sc_wrt_T Sc1 T1).
Proof.
unfold_singletons; exact fsk_Sc_open_Sc_wrt_T_lower.
Qed.

#[export] Hint Resolve fsk_Sc_open_Sc_wrt_T_lower : lngen.

Lemma fsk_Tm_open_Tm_wrt_T_lower :
forall t1 T1,
  fsk t1 ⊆ fsk (open_Tm_wrt_T t1 T1).
Proof.
unfold_singletons; exact fsk_Tm_open_Tm_wrt_T_lower.
Qed.

#[export] Hint Resolve fsk_Tm_open_Tm_wrt_T_lower : lngen.

Lemma fsk_Tm_open_Tm_wrt_Tm_lower :
forall t1 t2,
  fsk t1 ⊆ fsk (open_Tm_wrt_Tm t1 t2).
Proof.
unfold_singletons; exact fsk_Tm_open_Tm_wrt_Tm_lower.
Qed.

#[export] Hint Resolve fsk_Tm_open_Tm_wrt_Tm_lower : lngen.

Lemma ftv_Tm_open_Tm_wrt_T_lower :
forall t1 T1,
  fv t1 ⊆ fv (open_Tm_wrt_T t1 T1).
Proof.
unfold_singletons; exact ftv_Tm_open_Tm_wrt_T_lower.
Qed.

#[export] Hint Resolve ftv_Tm_open_Tm_wrt_T_lower : lngen.

Lemma ftv_Tm_open_Tm_wrt_Tm_lower :
forall t1 t2,
  fv t1 ⊆ fv (open_Tm_wrt_Tm t1 t2).
Proof.
unfold_singletons; exact ftv_Tm_open_Tm_wrt_Tm_lower.
Qed.

#[export] Hint Resolve ftv_Tm_open_Tm_wrt_Tm_lower : lngen.

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

Lemma fv_Ex_open_Ex_wrt_Ex_upper :
forall e1 e2,
  fv_Ex (open_Ex_wrt_Ex e1 e2) ⊆ fv_Ex e2 `union` fv_Ex e1.
Proof.
unfold_singletons; exact fv_Ex_open_Ex_wrt_Ex_upper.
Qed.

#[export] Hint Resolve fv_Ex_open_Ex_wrt_Ex_upper : lngen.

Lemma fsk_T_open_T_wrt_T_upper :
forall T1 T2,
  fsk (open_T_wrt_T T1 T2) ⊆ fsk T2 `union` fsk T1.
Proof.
unfold_singletons; exact fsk_T_open_T_wrt_T_upper.
Qed.

#[export] Hint Resolve fsk_T_open_T_wrt_T_upper : lngen.

Lemma fsk_Sc_open_Sc_wrt_T_upper :
forall Sc1 T1,
  fsk (open_Sc_wrt_T Sc1 T1) ⊆ fsk T1 `union` fsk Sc1.
Proof.
unfold_singletons; exact fsk_Sc_open_Sc_wrt_T_upper.
Qed.

#[export] Hint Resolve fsk_Sc_open_Sc_wrt_T_upper : lngen.

Lemma fsk_Tm_open_Tm_wrt_T_upper :
forall t1 T1,
  fsk (open_Tm_wrt_T t1 T1) ⊆ fsk T1 `union` fsk t1.
Proof.
unfold_singletons; exact fsk_Tm_open_Tm_wrt_T_upper.
Qed.

#[export] Hint Resolve fsk_Tm_open_Tm_wrt_T_upper : lngen.

Lemma fsk_Tm_open_Tm_wrt_Tm_upper :
forall t1 t2,
  fsk (open_Tm_wrt_Tm t1 t2) ⊆ fsk t2 `union` fsk t1.
Proof.
unfold_singletons; exact fsk_Tm_open_Tm_wrt_Tm_upper.
Qed.

#[export] Hint Resolve fsk_Tm_open_Tm_wrt_Tm_upper : lngen.

Lemma ftv_Tm_open_Tm_wrt_T_upper :
forall t1 T1,
  fv (open_Tm_wrt_T t1 T1) ⊆ fv t1.
Proof.
unfold_singletons; exact ftv_Tm_open_Tm_wrt_T_upper.
Qed.

#[export] Hint Resolve ftv_Tm_open_Tm_wrt_T_upper : lngen.

Lemma ftv_Tm_open_Tm_wrt_Tm_upper :
forall t1 t2,
  fv (open_Tm_wrt_Tm t1 t2) ⊆ fv t2 `union` fv t1.
Proof.
unfold_singletons; exact ftv_Tm_open_Tm_wrt_Tm_upper.
Qed.

#[export] Hint Resolve ftv_Tm_open_Tm_wrt_Tm_upper : lngen.

(*hidden lems removed*)

Lemma fv_Ex_subst_var_Ex_fresh :
forall e1 e2 x1,
  x1 ∉ fv_Ex e1 ->
  fv_Ex (subst__x e2 x1 e1) ≡ fv_Ex e1.
Proof.
unfold_singletons; exact fv_Ex_subst_var_Ex_fresh.
Qed.

#[export] Hint Resolve fv_Ex_subst_var_Ex_fresh : lngen.
#[export] Hint Rewrite fv_Ex_subst_var_Ex_fresh using solve [auto] : lngen.

(*hidden lems removed*)

Lemma fsk_T_subst_skvar_T_fresh :
forall T1 T2 β1,
  β1 ∉ fsk T1 ->
  fsk (subst (X:=T) T2 β1 T1) ≡ fsk T1.
Proof.
unfold_singletons; exact fsk_T_subst_skvar_T_fresh.
Qed.

#[export] Hint Resolve fsk_T_subst_skvar_T_fresh : lngen.
#[export] Hint Rewrite fsk_T_subst_skvar_T_fresh using solve [auto] : lngen.

(*hidden lems removed*)

Lemma fsk_Sc_subst_skvar_Sc_fresh :
forall Sc1 T1 β1,
  β1 ∉ fsk Sc1 ->
  fsk (subst (X:=Sc) T1 β1 Sc1) ≡ fsk Sc1.
Proof.
unfold_singletons; exact fsk_Sc_subst_skvar_Sc_fresh.
Qed.

#[export] Hint Resolve fsk_Sc_subst_skvar_Sc_fresh : lngen.
#[export] Hint Rewrite fsk_Sc_subst_skvar_Sc_fresh using solve [auto] : lngen.

(*hidden lems removed*)

Lemma fsk_Tm_subst_skvar_Tm_fresh :
forall t1 T1 β1,
  β1 ∉ fsk t1 ->
  fsk (subst (X:=Tm) T1 β1 t1) ≡ fsk t1.
Proof.
unfold_singletons; exact fsk_Tm_subst_skvar_Tm_fresh.
Qed.

#[export] Hint Resolve fsk_Tm_subst_skvar_Tm_fresh : lngen.
#[export] Hint Rewrite fsk_Tm_subst_skvar_Tm_fresh using solve [auto] : lngen.

(*hidden lems removed*)

Lemma fsk_Tm_subst_tvar_Tm_fresh :
forall t1 T1 β1,
  fv (subst (X:=Tm) T1 β1 t1) ≡ fv t1.
Proof.
unfold_singletons; exact fsk_Tm_subst_tvar_Tm_fresh.
Qed.

#[export] Hint Resolve fsk_Tm_subst_tvar_Tm_fresh : lngen.
#[export] Hint Rewrite fsk_Tm_subst_tvar_Tm_fresh using solve [auto] : lngen.

(*hidden lems removed*)

Lemma ftv_Tm_subst_tvar_Tm_fresh :
forall t1 t2 tx1,
  tx1 ∉ fv t1 ->
  fv (subst__x t2 tx1 t1) ≡ fv t1.
Proof.
unfold_singletons; exact ftv_Tm_subst_tvar_Tm_fresh.
Qed.

#[export] Hint Resolve ftv_Tm_subst_tvar_Tm_fresh : lngen.
#[export] Hint Rewrite ftv_Tm_subst_tvar_Tm_fresh using solve [auto] : lngen.

(*hidden lems removed*)

Lemma fv_Ex_subst_var_Ex_lower :
forall e1 e2 x1,
  remove x1 (fv_Ex e1) ⊆ fv_Ex (subst__x e2 x1 e1).
Proof.
unfold_singletons; exact fv_Ex_subst_var_Ex_lower.
Qed.

#[export] Hint Resolve fv_Ex_subst_var_Ex_lower : lngen.

(*hidden lems removed*)

Lemma fsk_T_subst_skvar_T_lower :
forall T1 T2 β1,
  remove β1 (fsk T1) ⊆ fsk (subst (X:=T) T2 β1 T1).
Proof.
unfold_singletons; exact fsk_T_subst_skvar_T_lower.
Qed.

#[export] Hint Resolve fsk_T_subst_skvar_T_lower : lngen.

(*hidden lems removed*)

Lemma fsk_Sc_subst_skvar_Sc_lower :
forall Sc1 T1 β1,
  remove β1 (fsk Sc1) ⊆ fsk (subst (X:=Sc) T1 β1 Sc1).
Proof.
unfold_singletons; exact fsk_Sc_subst_skvar_Sc_lower.
Qed.

#[export] Hint Resolve fsk_Sc_subst_skvar_Sc_lower : lngen.

(*hidden lems removed*)

Lemma fsk_Tm_subst_skvar_Tm_lower :
forall t1 T1 β1,
  remove β1 (fsk t1) ⊆ fsk (subst (X:=Tm) T1 β1 t1).
Proof.
unfold_singletons; exact fsk_Tm_subst_skvar_Tm_lower.
Qed.

#[export] Hint Resolve fsk_Tm_subst_skvar_Tm_lower : lngen.

(*hidden lems removed*)

Lemma fsk_Tm_subst_tvar_Tm_lower :
forall t1 t2 tx1,
  fsk t1 ⊆ fsk (subst__x t2 tx1 t1).
Proof.
unfold_singletons; exact fsk_Tm_subst_tvar_Tm_lower.
Qed.

#[export] Hint Resolve fsk_Tm_subst_tvar_Tm_lower : lngen.

(*hidden lems removed*)

Lemma ftv_Tm_subst_skvar_Tm_lower :
forall t1 T1 β1,
  fv t1 ⊆ fv (subst (X:=Tm) T1 β1 t1).
Proof.
unfold_singletons; exact ftv_Tm_subst_skvar_Tm_lower.
Qed.

#[export] Hint Resolve ftv_Tm_subst_skvar_Tm_lower : lngen.

(*hidden lems removed*)

Lemma ftv_Tm_subst_tvar_Tm_lower :
forall t1 t2 tx1,
  remove tx1 (fv t1) ⊆ fv (subst__x t2 tx1 t1).
Proof.
unfold_singletons; exact ftv_Tm_subst_tvar_Tm_lower.
Qed.

#[export] Hint Resolve ftv_Tm_subst_tvar_Tm_lower : lngen.

(*hidden lems removed*)

Lemma fv_Ex_subst_var_Ex_notin :
forall e1 e2 x1 x2,
  x2 ∉ fv_Ex e1 ->
  x2 ∉ fv_Ex e2 ->
  x2 ∉ fv_Ex (subst__x e2 x1 e1).
Proof.
unfold_singletons; exact fv_Ex_subst_var_Ex_notin.
Qed.

#[export] Hint Resolve fv_Ex_subst_var_Ex_notin : lngen.

(*hidden lems removed*)

Lemma fsk_T_subst_skvar_T_notin :
forall T1 T2 β1 β2,
  β2 ∉ fsk T1 ->
  β2 ∉ fsk T2 ->
  β2 ∉ fsk (subst (X:=T) T2 β1 T1).
Proof.
unfold_singletons; exact fsk_T_subst_skvar_T_notin.
Qed.

#[export] Hint Resolve fsk_T_subst_skvar_T_notin : lngen.

(*hidden lems removed*)

Lemma fsk_Sc_subst_skvar_Sc_notin :
forall Sc1 T1 β1 β2,
  β2 ∉ fsk Sc1 ->
  β2 ∉ fsk T1 ->
  β2 ∉ fsk (subst (X:=Sc) T1 β1 Sc1).
Proof.
unfold_singletons; exact fsk_Sc_subst_skvar_Sc_notin.
Qed.

#[export] Hint Resolve fsk_Sc_subst_skvar_Sc_notin : lngen.

(*hidden lems removed*)

Lemma fsk_Tm_subst_skvar_Tm_notin :
forall t1 T1 β1 β2,
  β2 ∉ fsk t1 ->
  β2 ∉ fsk T1 ->
  β2 ∉ fsk (subst (X:=Tm) T1 β1 t1).
Proof.
unfold_singletons; exact fsk_Tm_subst_skvar_Tm_notin.
Qed.

#[export] Hint Resolve fsk_Tm_subst_skvar_Tm_notin : lngen.

(*hidden lems removed*)

Lemma fsk_Tm_subst_tvar_Tm_notin :
forall t1 t2 tx1 β1,
  β1 ∉ fsk t1 ->
  β1 ∉ fsk t2 ->
  β1 ∉ fsk (subst__x t2 tx1 t1).
Proof.
unfold_singletons; exact fsk_Tm_subst_tvar_Tm_notin.
Qed.

#[export] Hint Resolve fsk_Tm_subst_tvar_Tm_notin : lngen.

(*hidden lems removed*)

Lemma ftv_Tm_subst_skvar_Tm_notin :
forall t1 T1 β1 tx1,
  tx1 ∉ fv t1 ->
  tx1 ∉ fv (subst (X:=Tm) T1 β1 t1).
Proof.
unfold_singletons; exact ftv_Tm_subst_skvar_Tm_notin.
Qed.

#[export] Hint Resolve ftv_Tm_subst_skvar_Tm_notin : lngen.

(*hidden lems removed*)

Lemma ftv_Tm_subst_tvar_Tm_notin :
forall t1 t2 tx1 tx2,
  tx2 ∉ fv t1 ->
  tx2 ∉ fv t2 ->
  tx2 ∉ fv (subst__x t2 tx1 t1).
Proof.
unfold_singletons; exact ftv_Tm_subst_tvar_Tm_notin.
Qed.

#[export] Hint Resolve ftv_Tm_subst_tvar_Tm_notin : lngen.

(*hidden lems removed*)

Lemma fv_Ex_subst_var_Ex_upper :
forall e1 e2 x1,
  fv_Ex (subst__x e2 x1 e1) ⊆ fv_Ex e2 `union` remove x1 (fv_Ex e1).
Proof.
unfold_singletons; exact fv_Ex_subst_var_Ex_upper.
Qed.

#[export] Hint Resolve fv_Ex_subst_var_Ex_upper : lngen.

(*hidden lems removed*)

Lemma fsk_T_subst_skvar_T_upper :
forall T1 T2 β1,
  fsk (subst (X:=T) T2 β1 T1) ⊆ fsk T2 `union` remove β1 (fsk T1).
Proof.
unfold_singletons; exact fsk_T_subst_skvar_T_upper.
Qed.

#[export] Hint Resolve fsk_T_subst_skvar_T_upper : lngen.

(*hidden lems removed*)

Lemma fsk_Sc_subst_skvar_Sc_upper :
forall Sc1 T1 β1,
  fsk (subst (X:=Sc) T1 β1 Sc1) ⊆ fsk T1 `union` remove β1 (fsk Sc1).
Proof.
unfold_singletons; exact fsk_Sc_subst_skvar_Sc_upper.
Qed.

#[export] Hint Resolve fsk_Sc_subst_skvar_Sc_upper : lngen.

(*hidden lems removed*)

Lemma fsk_Tm_subst_skvar_Tm_upper :
forall t1 T1 β1,
  fsk (subst (X:=Tm) T1 β1 t1) ⊆ fsk T1 `union` remove β1 (fsk t1).
Proof.
unfold_singletons; exact fsk_Tm_subst_skvar_Tm_upper.
Qed.

#[export] Hint Resolve fsk_Tm_subst_skvar_Tm_upper : lngen.

(*hidden lems removed*)

Lemma fsk_Tm_subst_tvar_Tm_upper :
forall t1 t2 tx1,
  fsk (subst__x t2 tx1 t1) ⊆ fsk t2 `union` fsk t1.
Proof.
unfold_singletons; exact fsk_Tm_subst_tvar_Tm_upper.
Qed.

#[export] Hint Resolve fsk_Tm_subst_tvar_Tm_upper : lngen.

(*hidden lems removed*)

Lemma ftv_Tm_subst_skvar_Tm_upper :
forall t1 T1 β1,
  fv (subst (X:=Tm) T1 β1 t1) ⊆ fv t1.
Proof.
unfold_singletons; exact ftv_Tm_subst_skvar_Tm_upper.
Qed.

#[export] Hint Resolve ftv_Tm_subst_skvar_Tm_upper : lngen.

(*hidden lems removed*)

Lemma ftv_Tm_subst_tvar_Tm_upper :
forall t1 t2 tx1,
  fv (subst__x t2 tx1 t1) ⊆ fv t2 `union` remove tx1 (fv t1).
Proof.
unfold_singletons; exact ftv_Tm_subst_tvar_Tm_upper.
Qed.

#[export] Hint Resolve ftv_Tm_subst_tvar_Tm_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

(*ltac removed*)

(*hidden lems removed*)

Lemma subst_var_Ex_close_Ex_wrt_Ex_rec :
forall e2 e1 x1 x2 n1,
  degree_Ex_wrt_Ex n1 e1 ->
  x1 <> x2 ->
  x2 ∉ fv_Ex e1 ->
  subst__x e1 x1 (close_Ex_wrt_Ex_rec n1 x2 e2) = close_Ex_wrt_Ex_rec n1 x2 (subst__x e1 x1 e2).
Proof.
unfold_singletons; exact subst_var_Ex_close_Ex_wrt_Ex_rec.
Qed.

#[export] Hint Resolve subst_var_Ex_close_Ex_wrt_Ex_rec : lngen.

(*hidden lems removed*)

Lemma subst_skvar_T_close_T_wrt_T_rec :
forall T2 T1 β1 β2 n1,
  degree_T_wrt_T n1 T1 ->
  β1 <> β2 ->
  β2 ∉ fsk T1 ->
  subst (X:=T) T1 β1 (close_T_wrt_T_rec n1 β2 T2) = close_T_wrt_T_rec n1 β2 (subst (X:=T) T1 β1 T2).
Proof.
unfold_singletons; exact subst_skvar_T_close_T_wrt_T_rec.
Qed.

#[export] Hint Resolve subst_skvar_T_close_T_wrt_T_rec : lngen.

(*hidden lems removed*)

Lemma subst_skvar_Sc_close_Sc_wrt_T_rec :
forall Sc1 T1 β1 β2 n1,
  degree_T_wrt_T n1 T1 ->
  β1 <> β2 ->
  β2 ∉ fsk T1 ->
  subst (X:=Sc) T1 β1 (close_Sc_wrt_T_rec n1 β2 Sc1) = close_Sc_wrt_T_rec n1 β2 (subst (X:=Sc) T1 β1 Sc1).
Proof.
unfold_singletons; exact subst_skvar_Sc_close_Sc_wrt_T_rec.
Qed.

#[export] Hint Resolve subst_skvar_Sc_close_Sc_wrt_T_rec : lngen.

(*hidden lems removed*)

Lemma subst_skvar_Tm_close_Tm_wrt_T_rec :
forall t1 T1 β1 β2 n1,
  degree_T_wrt_T n1 T1 ->
  β1 <> β2 ->
  β2 ∉ fsk T1 ->
  subst (X:=Tm) T1 β1 (close_Tm_wrt_T_rec n1 β2 t1) = close_Tm_wrt_T_rec n1 β2 (subst (X:=Tm) T1 β1 t1).
Proof.
unfold_singletons; exact subst_skvar_Tm_close_Tm_wrt_T_rec.
Qed.

#[export] Hint Resolve subst_skvar_Tm_close_Tm_wrt_T_rec : lngen.

(*hidden lems removed*)

Lemma subst_skvar_Tm_close_Tm_wrt_Tm_rec :
forall t1 T1 tx1 β1 n1,
  subst (X:=Tm) T1 tx1 (close_Tm_wrt_Tm_rec n1 β1 t1) = close_Tm_wrt_Tm_rec n1 β1 (subst (X:=Tm) T1 tx1 t1).
Proof.
unfold_singletons; exact subst_skvar_Tm_close_Tm_wrt_Tm_rec.
Qed.

#[export] Hint Resolve subst_skvar_Tm_close_Tm_wrt_Tm_rec : lngen.

(*hidden lems removed*)

Lemma subst_tvar_Tm_close_Tm_wrt_T_rec :
forall t2 t1 β1 tx1 n1,
  degree_Tm_wrt_T n1 t1 ->
  tx1 ∉ fsk t1 ->
  subst__x t1 β1 (close_Tm_wrt_T_rec n1 tx1 t2) = close_Tm_wrt_T_rec n1 tx1 (subst__x t1 β1 t2).
Proof.
unfold_singletons; exact subst_tvar_Tm_close_Tm_wrt_T_rec.
Qed.

#[export] Hint Resolve subst_tvar_Tm_close_Tm_wrt_T_rec : lngen.

(*hidden lems removed*)

Lemma subst_tvar_Tm_close_Tm_wrt_Tm_rec :
forall t2 t1 tx1 tx2 n1,
  degree_Tm_wrt_Tm n1 t1 ->
  tx1 <> tx2 ->
  tx2 ∉ fv t1 ->
  subst__x t1 tx1 (close_Tm_wrt_Tm_rec n1 tx2 t2) = close_Tm_wrt_Tm_rec n1 tx2 (subst__x t1 tx1 t2).
Proof.
unfold_singletons; exact subst_tvar_Tm_close_Tm_wrt_Tm_rec.
Qed.

#[export] Hint Resolve subst_tvar_Tm_close_Tm_wrt_Tm_rec : lngen.

Lemma subst_var_Ex_close_Ex_wrt_Ex :
forall e2 e1 x1 x2,
  lc e1 ->  x1 <> x2 ->
  x2 ∉ fv_Ex e1 ->
  subst__x e1 x1 (close_Ex_wrt_Ex x2 e2) = close_Ex_wrt_Ex x2 (subst__x e1 x1 e2).
Proof.
unfold_singletons; exact subst_var_Ex_close_Ex_wrt_Ex.
Qed.

#[export] Hint Resolve subst_var_Ex_close_Ex_wrt_Ex : lngen.

Lemma subst_skvar_T_close_T_wrt_T :
forall T2 T1 β1 β2,
  lc T1 ->  β1 <> β2 ->
  β2 ∉ fsk T1 ->
  subst (X:=T) T1 β1 (close_T_wrt_T β2 T2) = close_T_wrt_T β2 (subst (X:=T) T1 β1 T2).
Proof.
unfold_singletons; exact subst_skvar_T_close_T_wrt_T.
Qed.

#[export] Hint Resolve subst_skvar_T_close_T_wrt_T : lngen.

Lemma subst_skvar_Sc_close_Sc_wrt_T :
forall Sc1 T1 β1 β2,
  lc T1 ->  β1 <> β2 ->
  β2 ∉ fsk T1 ->
  subst (X:=Sc) T1 β1 (close_Sc_wrt_T β2 Sc1) = close_Sc_wrt_T β2 (subst (X:=Sc) T1 β1 Sc1).
Proof.
unfold_singletons; exact subst_skvar_Sc_close_Sc_wrt_T.
Qed.

#[export] Hint Resolve subst_skvar_Sc_close_Sc_wrt_T : lngen.

Lemma subst_skvar_Tm_close_Tm_wrt_T :
forall t1 T1 β1 β2,
  lc T1 ->  β1 <> β2 ->
  β2 ∉ fsk T1 ->
  subst (X:=Tm) T1 β1 (close_Tm_wrt_T β2 t1) = close_Tm_wrt_T β2 (subst (X:=Tm) T1 β1 t1).
Proof.
unfold_singletons; exact subst_skvar_Tm_close_Tm_wrt_T.
Qed.

#[export] Hint Resolve subst_skvar_Tm_close_Tm_wrt_T : lngen.

Lemma subst_skvar_Tm_close_Tm_wrt_Tm :
forall t1 T1 tx1 β1,
  lc T1 ->  subst (X:=Tm) T1 tx1 (close_Tm_wrt_Tm β1 t1) = close_Tm_wrt_Tm β1 (subst (X:=Tm) T1 tx1 t1).
Proof.
unfold_singletons; exact subst_skvar_Tm_close_Tm_wrt_Tm.
Qed.

#[export] Hint Resolve subst_skvar_Tm_close_Tm_wrt_Tm : lngen.

Lemma subst_tvar_Tm_close_Tm_wrt_T :
forall t2 t1 β1 tx1,
  lc (X:=Tm) t1 ->  tx1 ∉ fsk t1 ->
  subst__x t1 β1 (close_Tm_wrt_T tx1 t2) = close_Tm_wrt_T tx1 (subst__x t1 β1 t2).
Proof.
unfold_singletons; exact subst_tvar_Tm_close_Tm_wrt_T.
Qed.

#[export] Hint Resolve subst_tvar_Tm_close_Tm_wrt_T : lngen.

Lemma subst_tvar_Tm_close_Tm_wrt_Tm :
forall t2 t1 tx1 tx2,
  lc (X:=Tm) t1 ->  tx1 <> tx2 ->
  tx2 ∉ fv t1 ->
  subst__x t1 tx1 (close_Tm_wrt_Tm tx2 t2) = close_Tm_wrt_Tm tx2 (subst__x t1 tx1 t2).
Proof.
unfold_singletons; exact subst_tvar_Tm_close_Tm_wrt_Tm.
Qed.

#[export] Hint Resolve subst_tvar_Tm_close_Tm_wrt_Tm : lngen.

(*hidden lems removed*)

Lemma subst_var_Ex_degree_Ex_wrt_Ex :
forall e1 e2 x1 n1,
  degree_Ex_wrt_Ex n1 e1 ->
  degree_Ex_wrt_Ex n1 e2 ->
  degree_Ex_wrt_Ex n1 (subst__x e2 x1 e1).
Proof.
unfold_singletons; exact subst_var_Ex_degree_Ex_wrt_Ex.
Qed.

#[export] Hint Resolve subst_var_Ex_degree_Ex_wrt_Ex : lngen.

(*hidden lems removed*)

Lemma subst_skvar_T_degree_T_wrt_T :
forall T1 T2 β1 n1,
  degree_T_wrt_T n1 T1 ->
  degree_T_wrt_T n1 T2 ->
  degree_T_wrt_T n1 (subst (X:=T) T2 β1 T1).
Proof.
unfold_singletons; exact subst_skvar_T_degree_T_wrt_T.
Qed.

#[export] Hint Resolve subst_skvar_T_degree_T_wrt_T : lngen.

(*hidden lems removed*)

Lemma subst_skvar_Sc_degree_Sc_wrt_T :
forall Sc1 T1 β1 n1,
  degree_Sc_wrt_T n1 Sc1 ->
  degree_T_wrt_T n1 T1 ->
  degree_Sc_wrt_T n1 (subst (X:=Sc) T1 β1 Sc1).
Proof.
unfold_singletons; exact subst_skvar_Sc_degree_Sc_wrt_T.
Qed.

#[export] Hint Resolve subst_skvar_Sc_degree_Sc_wrt_T : lngen.

(*hidden lems removed*)

Lemma subst_skvar_Tm_degree_Tm_wrt_T :
forall t1 T1 β1 n1,
  degree_Tm_wrt_T n1 t1 ->
  degree_T_wrt_T n1 T1 ->
  degree_Tm_wrt_T n1 (subst (X:=Tm) T1 β1 t1).
Proof.
unfold_singletons; exact subst_skvar_Tm_degree_Tm_wrt_T.
Qed.

#[export] Hint Resolve subst_skvar_Tm_degree_Tm_wrt_T : lngen.

(*hidden lems removed*)

Lemma subst_skvar_Tm_degree_Tm_wrt_Tm :
forall t1 T1 β1 n1,
  degree_Tm_wrt_Tm n1 t1 ->
  degree_Tm_wrt_Tm n1 (subst (X:=Tm) T1 β1 t1).
Proof.
unfold_singletons; exact subst_skvar_Tm_degree_Tm_wrt_Tm.
Qed.

#[export] Hint Resolve subst_skvar_Tm_degree_Tm_wrt_Tm : lngen.

(*hidden lems removed*)

Lemma subst_tvar_Tm_degree_Tm_wrt_T :
forall t1 t2 tx1 n1,
  degree_Tm_wrt_T n1 t1 ->
  degree_Tm_wrt_T n1 t2 ->
  degree_Tm_wrt_T n1 (subst__x t2 tx1 t1).
Proof.
unfold_singletons; exact subst_tvar_Tm_degree_Tm_wrt_T.
Qed.

#[export] Hint Resolve subst_tvar_Tm_degree_Tm_wrt_T : lngen.

(*hidden lems removed*)

Lemma subst_tvar_Tm_degree_Tm_wrt_Tm :
forall t1 t2 tx1 n1,
  degree_Tm_wrt_Tm n1 t1 ->
  degree_Tm_wrt_Tm n1 t2 ->
  degree_Tm_wrt_Tm n1 (subst__x t2 tx1 t1).
Proof.
unfold_singletons; exact subst_tvar_Tm_degree_Tm_wrt_Tm.
Qed.

#[export] Hint Resolve subst_tvar_Tm_degree_Tm_wrt_Tm : lngen.

(*hidden lems removed*)

Lemma subst_var_Ex_fresh_eq :
forall e2 e1 x1,
  x1 ∉ fv_Ex e2 ->
  subst__x e1 x1 e2 = e2.
Proof.
unfold_singletons; exact subst_var_Ex_fresh_eq.
Qed.

#[export] Hint Resolve subst_var_Ex_fresh_eq : lngen.
#[export] Hint Rewrite subst_var_Ex_fresh_eq using solve [auto] : lngen.

(*hidden lems removed*)

Lemma subst_skvar_T_fresh_eq :
forall T2 T1 β1,
  β1 ∉ fsk T2 ->
  subst (X:=T) T1 β1 T2 = T2.
Proof.
unfold_singletons; exact subst_skvar_T_fresh_eq.
Qed.

#[export] Hint Resolve subst_skvar_T_fresh_eq : lngen.
#[export] Hint Rewrite subst_skvar_T_fresh_eq using solve [auto] : lngen.

(*hidden lems removed*)

Lemma subst_skvar_Sc_fresh_eq :
forall Sc1 T1 β1,
  β1 ∉ fsk Sc1 ->
  subst (X:=Sc) T1 β1 Sc1 = Sc1.
Proof.
unfold_singletons; exact subst_skvar_Sc_fresh_eq.
Qed.

#[export] Hint Resolve subst_skvar_Sc_fresh_eq : lngen.
#[export] Hint Rewrite subst_skvar_Sc_fresh_eq using solve [auto] : lngen.

(*hidden lems removed*)

Lemma subst_skvar_Tm_fresh_eq :
forall t1 T1 β1,
  β1 ∉ fsk t1 ->
  subst (X:=Tm) T1 β1 t1 = t1.
Proof.
unfold_singletons; exact subst_skvar_Tm_fresh_eq.
Qed.

#[export] Hint Resolve subst_skvar_Tm_fresh_eq : lngen.
#[export] Hint Rewrite subst_skvar_Tm_fresh_eq using solve [auto] : lngen.

(*hidden lems removed*)

Lemma subst_tvar_Tm_fresh_eq :
forall t2 t1 tx1,
  tx1 ∉ fv t2 ->
  subst__x t1 tx1 t2 = t2.
Proof.
unfold_singletons; exact subst_tvar_Tm_fresh_eq.
Qed.

#[export] Hint Resolve subst_tvar_Tm_fresh_eq : lngen.
#[export] Hint Rewrite subst_tvar_Tm_fresh_eq using solve [auto] : lngen.

(*hidden lems removed*)

Lemma subst_var_Ex_fresh_same :
forall e2 e1 x1,
  x1 ∉ fv_Ex e1 ->
  x1 ∉ fv_Ex (subst__x e1 x1 e2).
Proof.
unfold_singletons; exact subst_var_Ex_fresh_same.
Qed.

#[export] Hint Resolve subst_var_Ex_fresh_same : lngen.

(*hidden lems removed*)

Lemma subst_skvar_T_fresh_same :
forall T2 T1 β1,
  β1 ∉ fsk T1 ->
  β1 ∉ fsk (subst (X:=T) T1 β1 T2).
Proof.
unfold_singletons; exact subst_skvar_T_fresh_same.
Qed.

#[export] Hint Resolve subst_skvar_T_fresh_same : lngen.

(*hidden lems removed*)

Lemma subst_skvar_Sc_fresh_same :
forall Sc1 T1 β1,
  β1 ∉ fsk T1 ->
  β1 ∉ fsk (subst (X:=Sc) T1 β1 Sc1).
Proof.
unfold_singletons; exact subst_skvar_Sc_fresh_same.
Qed.

#[export] Hint Resolve subst_skvar_Sc_fresh_same : lngen.

(*hidden lems removed*)

Lemma subst_skvar_Tm_fresh_same :
forall t1 T1 β1,
  β1 ∉ fsk T1 ->
  β1 ∉ fsk (subst (X:=Tm) T1 β1 t1).
Proof.
unfold_singletons; exact subst_skvar_Tm_fresh_same.
Qed.

#[export] Hint Resolve subst_skvar_Tm_fresh_same : lngen.

(*hidden lems removed*)

Lemma subst_tvar_Tm_fresh_same :
forall t2 t1 tx1,
  tx1 ∉ fv t1 ->
  tx1 ∉ fv (subst__x t1 tx1 t2).
Proof.
unfold_singletons; exact subst_tvar_Tm_fresh_same.
Qed.

#[export] Hint Resolve subst_tvar_Tm_fresh_same : lngen.

(*hidden lems removed*)

Lemma subst_var_Ex_fresh :
forall e2 e1 x1 x2,
  x1 ∉ fv_Ex e2 ->
  x1 ∉ fv_Ex e1 ->
  x1 ∉ fv_Ex (subst__x e1 x2 e2).
Proof.
unfold_singletons; exact subst_var_Ex_fresh.
Qed.

#[export] Hint Resolve subst_var_Ex_fresh : lngen.

(*hidden lems removed*)

Lemma subst_skvar_T_fresh :
forall T2 T1 β1 β2,
  β1 ∉ fsk T2 ->
  β1 ∉ fsk T1 ->
  β1 ∉ fsk (subst (X:=T) T1 β2 T2).
Proof.
unfold_singletons; exact subst_skvar_T_fresh.
Qed.

#[export] Hint Resolve subst_skvar_T_fresh : lngen.

(*hidden lems removed*)

Lemma subst_skvar_Sc_fresh :
forall Sc1 T1 β1 β2,
  β1 ∉ fsk Sc1 ->
  β1 ∉ fsk T1 ->
  β1 ∉ fsk (subst (X:=Sc) T1 β2 Sc1).
Proof.
unfold_singletons; exact subst_skvar_Sc_fresh.
Qed.

#[export] Hint Resolve subst_skvar_Sc_fresh : lngen.

(*hidden lems removed*)

Lemma subst_skvar_Tm_fresh :
forall t1 T1 β1 β2,
  β1 ∉ fsk t1 ->
  β1 ∉ fsk T1 ->
  β1 ∉ fsk (subst (X:=Tm) T1 β2 t1).
Proof.
unfold_singletons; exact subst_skvar_Tm_fresh.
Qed.

#[export] Hint Resolve subst_skvar_Tm_fresh : lngen.

(*hidden lems removed*)

Lemma subst_tvar_Tm_fresh :
forall t2 t1 tx1 tx2,
  tx1 ∉ fv t2 ->
  tx1 ∉ fv t1 ->
  tx1 ∉ fv (subst__x t1 tx2 t2).
Proof.
unfold_singletons; exact subst_tvar_Tm_fresh.
Qed.

#[export] Hint Resolve subst_tvar_Tm_fresh : lngen.

Lemma subst_var_Ex_lc_Ex :
forall e1 e2 x1,
  lc e1 ->
  lc e2 ->
  lc (subst__x e2 x1 e1).
Proof.
unfold_singletons; exact subst_var_Ex_lc_Ex.
Qed.

#[export] Hint Resolve subst_var_Ex_lc_Ex : lngen.

Lemma subst_skvar_T_lc_T :
forall T1 T2 β1,
  lc T1 ->
  lc T2 ->
  lc (subst (X:=T) T2 β1 T1).
Proof.
unfold_singletons; exact subst_skvar_T_lc_T.
Qed.

#[export] Hint Resolve subst_skvar_T_lc_T : lngen.

Lemma subst_skvar_Sc_lc_Sc :
forall Sc1 T1 β1,
  lc Sc1 ->
  lc T1 ->
  lc (subst (X:=Sc) T1 β1 Sc1).
Proof.
unfold_singletons; exact subst_skvar_Sc_lc_Sc.
Qed.

#[export] Hint Resolve subst_skvar_Sc_lc_Sc : lngen.

Lemma subst_skvar_Tm_lc_Tm :
forall t1 T1 β1,
  lc (X:=Tm) t1 ->
  lc T1 ->
  lc (X:=Tm) (subst (X:=Tm) T1 β1 t1).
Proof.
unfold_singletons; exact subst_skvar_Tm_lc_Tm.
Qed.

#[export] Hint Resolve subst_skvar_Tm_lc_Tm : lngen.

Lemma subst_tvar_Tm_lc_Tm :
forall t1 t2 tx1,
  lc (X:=Tm) t1 ->
  lc (X:=Tm) t2 ->
  lc (X:=Tm) (subst__x t2 tx1 t1).
Proof.
unfold_singletons; exact subst_tvar_Tm_lc_Tm.
Qed.

#[export] Hint Resolve subst_tvar_Tm_lc_Tm : lngen.

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

Lemma subst_var_Ex_open_Ex_wrt_Ex :
forall e3 e1 e2 x1,
  lc e1 ->
  subst__x e1 x1 (open_Ex_wrt_Ex e3 e2) = open_Ex_wrt_Ex (subst__x e1 x1 e3) (subst__x e1 x1 e2).
Proof.
unfold_singletons; exact subst_var_Ex_open_Ex_wrt_Ex.
Qed.

#[export] Hint Resolve subst_var_Ex_open_Ex_wrt_Ex : lngen.

Lemma subst_skvar_T_open_T_wrt_T :
forall T3 T1 T2 β1,
  lc T1 ->
  subst (X:=T) T1 β1 (open_T_wrt_T T3 T2) = open_T_wrt_T (subst (X:=T) T1 β1 T3) (subst (X:=T) T1 β1 T2).
Proof.
unfold_singletons; exact subst_skvar_T_open_T_wrt_T.
Qed.

#[export] Hint Resolve subst_skvar_T_open_T_wrt_T : lngen.

Lemma subst_skvar_Sc_open_Sc_wrt_T :
forall Sc1 T1 T2 β1,
  lc T1 ->
  subst (X:=Sc) T1 β1 (open_Sc_wrt_T Sc1 T2) = open_Sc_wrt_T (subst (X:=Sc) T1 β1 Sc1) (subst (X:=T) T1 β1 T2).
Proof.
unfold_singletons; exact subst_skvar_Sc_open_Sc_wrt_T.
Qed.

#[export] Hint Resolve subst_skvar_Sc_open_Sc_wrt_T : lngen.

Lemma subst_skvar_Tm_open_Tm_wrt_T :
forall t1 T1 T2 β1,
  lc T1 ->
  subst (X:=Tm) T1 β1 (open_Tm_wrt_T t1 T2) = open_Tm_wrt_T (subst (X:=Tm) T1 β1 t1) (subst (X:=T) T1 β1 T2).
Proof.
unfold_singletons; exact subst_skvar_Tm_open_Tm_wrt_T.
Qed.

#[export] Hint Resolve subst_skvar_Tm_open_Tm_wrt_T : lngen.

Lemma subst_skvar_Tm_open_Tm_wrt_Tm :
forall t2 T1 t1 β1,
  subst (X:=Tm) T1 β1 (open_Tm_wrt_Tm t2 t1) = open_Tm_wrt_Tm (subst (X:=Tm) T1 β1 t2) (subst (X:=Tm) T1 β1 t1).
Proof.
unfold_singletons; exact subst_skvar_Tm_open_Tm_wrt_Tm.
Qed.

#[export] Hint Resolve subst_skvar_Tm_open_Tm_wrt_Tm : lngen.

Lemma subst_tvar_Tm_open_Tm_wrt_T :
forall t2 t1 T1 tx1,
  lc (X:=Tm) t1 ->
  subst__x t1 tx1 (open_Tm_wrt_T t2 T1) = open_Tm_wrt_T (subst__x t1 tx1 t2) T1.
Proof.
unfold_singletons; exact subst_tvar_Tm_open_Tm_wrt_T.
Qed.

#[export] Hint Resolve subst_tvar_Tm_open_Tm_wrt_T : lngen.

Lemma subst_tvar_Tm_open_Tm_wrt_Tm :
forall t3 t1 t2 tx1,
  lc (X:=Tm) t1 ->
  subst__x t1 tx1 (open_Tm_wrt_Tm t3 t2) = open_Tm_wrt_Tm (subst__x t1 tx1 t3) (subst__x t1 tx1 t2).
Proof.
unfold_singletons; exact subst_tvar_Tm_open_Tm_wrt_Tm.
Qed.

#[export] Hint Resolve subst_tvar_Tm_open_Tm_wrt_Tm : lngen.

Lemma subst_var_Ex_open_Ex_wrt_Ex_var :
forall e2 e1 x1 x2,
  x1 <> x2 ->
  lc e1 ->
  open_Ex_wrt_Ex (subst__x e1 x1 e2) (e__Var_f x2) = subst__x e1 x1 (open_Ex_wrt_Ex e2 (e__Var_f x2)).
Proof.
unfold_singletons; exact subst_var_Ex_open_Ex_wrt_Ex_var.
Qed.

#[export] Hint Resolve subst_var_Ex_open_Ex_wrt_Ex_var : lngen.

Lemma subst_skvar_T_open_T_wrt_T_var :
forall T2 T1 β1 β2,
  β1 <> β2 ->
  lc T1 ->
  open_T_wrt_T (subst (X:=T) T1 β1 T2) (T__Var_f β2) = subst (X:=T) T1 β1 (open_T_wrt_T T2 (T__Var_f β2)).
Proof.
unfold_singletons; exact subst_skvar_T_open_T_wrt_T_var.
Qed.

#[export] Hint Resolve subst_skvar_T_open_T_wrt_T_var : lngen.

Lemma subst_skvar_Sc_open_Sc_wrt_T_var :
forall Sc1 T1 β1 β2,
  β1 <> β2 ->
  lc T1 ->
  open_Sc_wrt_T (subst (X:=Sc) T1 β1 Sc1) (T__Var_f β2) = subst (X:=Sc) T1 β1 (open_Sc_wrt_T Sc1 (T__Var_f β2)).
Proof.
unfold_singletons; exact subst_skvar_Sc_open_Sc_wrt_T_var.
Qed.

#[export] Hint Resolve subst_skvar_Sc_open_Sc_wrt_T_var : lngen.

Lemma subst_skvar_Tm_open_Tm_wrt_T_var :
forall t1 T1 β1 β2,
  β1 <> β2 ->
  lc T1 ->
  open_Tm_wrt_T (subst (X:=Tm) T1 β1 t1) (T__Var_f β2) = subst (X:=Tm) T1 β1 (open_Tm_wrt_T t1 (T__Var_f β2)).
Proof.
unfold_singletons; exact subst_skvar_Tm_open_Tm_wrt_T_var.
Qed.

#[export] Hint Resolve subst_skvar_Tm_open_Tm_wrt_T_var : lngen.

Lemma subst_skvar_Tm_open_Tm_wrt_Tm_var :
forall t1 T1 β1 tx1,
  open_Tm_wrt_Tm (subst (X:=Tm) T1 β1 t1) (t__Var_f tx1) = subst (X:=Tm) T1 β1 (open_Tm_wrt_Tm t1 (t__Var_f tx1)).
Proof.
unfold_singletons; exact subst_skvar_Tm_open_Tm_wrt_Tm_var.
Qed.

#[export] Hint Resolve subst_skvar_Tm_open_Tm_wrt_Tm_var : lngen.

Lemma subst_tvar_Tm_open_Tm_wrt_T_var :
forall t2 t1 tx1 β1,
  lc (X:=Tm) t1 ->
  open_Tm_wrt_T (subst__x t1 tx1 t2) (T__Var_f β1) = subst__x t1 tx1 (open_Tm_wrt_T t2 (T__Var_f β1)).
Proof.
unfold_singletons; exact subst_tvar_Tm_open_Tm_wrt_T_var.
Qed.

#[export] Hint Resolve subst_tvar_Tm_open_Tm_wrt_T_var : lngen.

Lemma subst_tvar_Tm_open_Tm_wrt_Tm_var :
forall t2 t1 tx1 tx2,
  tx1 <> tx2 ->
  lc (X:=Tm) t1 ->
  open_Tm_wrt_Tm (subst__x t1 tx1 t2) (t__Var_f tx2) = subst__x t1 tx1 (open_Tm_wrt_Tm t2 (t__Var_f tx2)).
Proof.
unfold_singletons; exact subst_tvar_Tm_open_Tm_wrt_Tm_var.
Qed.

#[export] Hint Resolve subst_tvar_Tm_open_Tm_wrt_Tm_var : lngen.

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

Lemma subst_var_Ex_spec :
forall e1 e2 x1,
  subst__x e2 x1 e1 = open_Ex_wrt_Ex (close_Ex_wrt_Ex x1 e1) e2.
Proof.
unfold_singletons; exact subst_var_Ex_spec.
Qed.

#[export] Hint Resolve subst_var_Ex_spec : lngen.

Lemma subst_skvar_T_spec :
forall T1 T2 β1,
  subst (X:=T) T2 β1 T1 = open_T_wrt_T (close_T_wrt_T β1 T1) T2.
Proof.
unfold_singletons; exact subst_skvar_T_spec.
Qed.

#[export] Hint Resolve subst_skvar_T_spec : lngen.

Lemma subst_skvar_Sc_spec :
forall Sc1 T1 β1,
  subst (X:=Sc) T1 β1 Sc1 = open_Sc_wrt_T (close_Sc_wrt_T β1 Sc1) T1.
Proof.
unfold_singletons; exact subst_skvar_Sc_spec.
Qed.

#[export] Hint Resolve subst_skvar_Sc_spec : lngen.

Lemma subst_skvar_Tm_spec :
forall t1 T1 β1,
  subst (X:=Tm) T1 β1 t1 = open_Tm_wrt_T (close_Tm_wrt_T β1 t1) T1.
Proof.
unfold_singletons; exact subst_skvar_Tm_spec.
Qed.

#[export] Hint Resolve subst_skvar_Tm_spec : lngen.

Lemma subst_tvar_Tm_spec :
forall t1 t2 tx1,
  subst__x t2 tx1 t1 = open_Tm_wrt_Tm (close_Tm_wrt_Tm tx1 t1) t2.
Proof.
unfold_singletons; exact subst_tvar_Tm_spec.
Qed.

#[export] Hint Resolve subst_tvar_Tm_spec : lngen.

(*hidden lems removed*)

Lemma subst_var_Ex_subst_var_Ex :
forall e1 e2 e3 x2 x1,
  x2 ∉ fv_Ex e2 ->
  x2 <> x1 ->
  subst__x e2 x1 (subst__x e3 x2 e1) = subst__x (subst__x e2 x1 e3) x2 (subst__x e2 x1 e1).
Proof.
unfold_singletons; exact subst_var_Ex_subst_var_Ex.
Qed.

#[export] Hint Resolve subst_var_Ex_subst_var_Ex : lngen.

(*hidden lems removed*)

Lemma subst_skvar_T_subst_skvar_T :
forall T1 T2 T3 β2 β1,
  β2 ∉ fsk T2 ->
  β2 <> β1 ->
  subst (X:=T) T2 β1 (subst (X:=T) T3 β2 T1) = subst (X:=T) (subst (X:=T) T2 β1 T3) β2 (subst (X:=T) T2 β1 T1).
Proof.
unfold_singletons; exact subst_skvar_T_subst_skvar_T.
Qed.

#[export] Hint Resolve subst_skvar_T_subst_skvar_T : lngen.

(*hidden lems removed*)

Lemma subst_skvar_Sc_subst_skvar_Sc :
forall Sc1 T1 T2 β2 β1,
  β2 ∉ fsk T1 ->
  β2 <> β1 ->
  subst (X:=Sc) T1 β1 (subst (X:=Sc) T2 β2 Sc1) = subst (X:=Sc) (subst (X:=T) T1 β1 T2) β2 (subst (X:=Sc) T1 β1 Sc1).
Proof.
unfold_singletons; exact subst_skvar_Sc_subst_skvar_Sc.
Qed.

#[export] Hint Resolve subst_skvar_Sc_subst_skvar_Sc : lngen.

(*hidden lems removed*)

Lemma subst_skvar_Tm_subst_skvar_Tm :
forall t1 T1 T2 β2 β1,
  β2 ∉ fsk T1 ->
  β2 <> β1 ->
  subst (X:=Tm) T1 β1 (subst (X:=Tm) T2 β2 t1) = subst (X:=Tm) (subst (X:=T) T1 β1 T2) β2 (subst (X:=Tm) T1 β1 t1).
Proof.
unfold_singletons; exact subst_skvar_Tm_subst_skvar_Tm.
Qed.

#[export] Hint Resolve subst_skvar_Tm_subst_skvar_Tm : lngen.

(*hidden lems removed*)

Lemma subst_skvar_Tm_subst_tvar_Tm :
forall t1 T1 t2 tx1 β1,
  subst (X:=Tm) T1 β1 (subst__x t2 tx1 t1) = subst__x (subst (X:=Tm) T1 β1 t2) tx1 (subst (X:=Tm) T1 β1 t1).
Proof.
unfold_singletons; exact subst_skvar_Tm_subst_tvar_Tm.
Qed.

#[export] Hint Resolve subst_skvar_Tm_subst_tvar_Tm : lngen.

(*hidden lems removed*)

Lemma subst_tvar_Tm_subst_skvar_Tm :
forall t1 t2 T1 β1 tx1,
  β1 ∉ fsk t2 ->
  subst__x t2 tx1 (subst (X:=Tm) T1 β1 t1) = subst (X:=Tm) T1 β1 (subst__x t2 tx1 t1).
Proof.
unfold_singletons; exact subst_tvar_Tm_subst_skvar_Tm.
Qed.

#[export] Hint Resolve subst_tvar_Tm_subst_skvar_Tm : lngen.

(*hidden lems removed*)

Lemma subst_tvar_Tm_subst_tvar_Tm :
forall t1 t2 t3 tx2 tx1,
  tx2 ∉ fv t2 ->
  tx2 <> tx1 ->
  subst__x t2 tx1 (subst__x t3 tx2 t1) = subst__x (subst__x t2 tx1 t3) tx2 (subst__x t2 tx1 t1).
Proof.
unfold_singletons; exact subst_tvar_Tm_subst_tvar_Tm.
Qed.

#[export] Hint Resolve subst_tvar_Tm_subst_tvar_Tm : lngen.

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

(*hidden lems removed*)

Lemma subst_var_Ex_close_Ex_wrt_Ex_open_Ex_wrt_Ex :
forall e2 e1 x1 x2,
  x2 ∉ fv_Ex e2 ->
  x2 ∉ fv_Ex e1 ->
  x2 <> x1 ->
  lc e1 ->
  subst__x e1 x1 e2 = close_Ex_wrt_Ex x2 (subst__x e1 x1 (open_Ex_wrt_Ex e2 (e__Var_f x2))).
Proof.
unfold_singletons; exact subst_var_Ex_close_Ex_wrt_Ex_open_Ex_wrt_Ex.
Qed.

#[export] Hint Resolve subst_var_Ex_close_Ex_wrt_Ex_open_Ex_wrt_Ex : lngen.

Lemma subst_skvar_T_close_T_wrt_T_open_T_wrt_T :
forall T2 T1 β1 β2,
  β2 ∉ fsk T2 ->
  β2 ∉ fsk T1 ->
  β2 <> β1 ->
  lc T1 ->
  subst (X:=T) T1 β1 T2 = close_T_wrt_T β2 (subst (X:=T) T1 β1 (open_T_wrt_T T2 (T__Var_f β2))).
Proof.
unfold_singletons; exact subst_skvar_T_close_T_wrt_T_open_T_wrt_T.
Qed.

#[export] Hint Resolve subst_skvar_T_close_T_wrt_T_open_T_wrt_T : lngen.

Lemma subst_skvar_Sc_close_Sc_wrt_T_open_Sc_wrt_T :
forall Sc1 T1 β1 β2,
  β2 ∉ fsk Sc1 ->
  β2 ∉ fsk T1 ->
  β2 <> β1 ->
  lc T1 ->
  subst (X:=Sc) T1 β1 Sc1 = close_Sc_wrt_T β2 (subst (X:=Sc) T1 β1 (open_Sc_wrt_T Sc1 (T__Var_f β2))).
Proof.
unfold_singletons; exact subst_skvar_Sc_close_Sc_wrt_T_open_Sc_wrt_T.
Qed.

#[export] Hint Resolve subst_skvar_Sc_close_Sc_wrt_T_open_Sc_wrt_T : lngen.

Lemma subst_skvar_Tm_close_Tm_wrt_T_open_Tm_wrt_T :
forall t1 T1 β1 β2,
  β2 ∉ fsk t1 ->
  β2 ∉ fsk T1 ->
  β2 <> β1 ->
  lc T1 ->
  subst (X:=Tm) T1 β1 t1 = close_Tm_wrt_T β2 (subst (X:=Tm) T1 β1 (open_Tm_wrt_T t1 (T__Var_f β2))).
Proof.
unfold_singletons; exact subst_skvar_Tm_close_Tm_wrt_T_open_Tm_wrt_T.
Qed.

#[export] Hint Resolve subst_skvar_Tm_close_Tm_wrt_T_open_Tm_wrt_T : lngen.

Lemma subst_skvar_Tm_close_Tm_wrt_Tm_open_Tm_wrt_Tm :
forall t1 T1 β1 tx1,
  tx1 ∉ fv t1 ->
  lc T1 ->
  subst (X:=Tm) T1 β1 t1 = close_Tm_wrt_Tm tx1 (subst (X:=Tm) T1 β1 (open_Tm_wrt_Tm t1 (t__Var_f tx1))).
Proof.
unfold_singletons; exact subst_skvar_Tm_close_Tm_wrt_Tm_open_Tm_wrt_Tm.
Qed.

#[export] Hint Resolve subst_skvar_Tm_close_Tm_wrt_Tm_open_Tm_wrt_Tm : lngen.

Lemma subst_tvar_Tm_close_Tm_wrt_T_open_Tm_wrt_T :
forall t2 t1 tx1 β1,
  β1 ∉ fsk t2 ->
  β1 ∉ fsk t1 ->
  lc (X:=Tm) t1 ->
  subst__x t1 tx1 t2 = close_Tm_wrt_T β1 (subst__x t1 tx1 (open_Tm_wrt_T t2 (T__Var_f β1))).
Proof.
unfold_singletons; exact subst_tvar_Tm_close_Tm_wrt_T_open_Tm_wrt_T.
Qed.

#[export] Hint Resolve subst_tvar_Tm_close_Tm_wrt_T_open_Tm_wrt_T : lngen.

Lemma subst_tvar_Tm_close_Tm_wrt_Tm_open_Tm_wrt_Tm :
forall t2 t1 tx1 tx2,
  tx2 ∉ fv t2 ->
  tx2 ∉ fv t1 ->
  tx2 <> tx1 ->
  lc (X:=Tm) t1 ->
  subst__x t1 tx1 t2 = close_Tm_wrt_Tm tx2 (subst__x t1 tx1 (open_Tm_wrt_Tm t2 (t__Var_f tx2))).
Proof.
unfold_singletons; exact subst_tvar_Tm_close_Tm_wrt_Tm_open_Tm_wrt_Tm.
Qed.

#[export] Hint Resolve subst_tvar_Tm_close_Tm_wrt_Tm_open_Tm_wrt_Tm : lngen.

Lemma subst_var_Ex_e__Lam :
forall x2 e2 e1 x1,
  lc e1 ->
  x2 ∉ fv_Ex e1 `union` fv_Ex e2 `union` singleton x1 ->
  subst__x e1 x1 (e__Lam e2) = e__Lam (close_Ex_wrt_Ex x2 (subst__x e1 x1 (open_Ex_wrt_Ex e2 (e__Var_f x2)))).
Proof.
unfold_singletons; exact subst_var_Ex_e__Lam.
Qed.

#[export] Hint Resolve subst_var_Ex_e__Lam : lngen.

Lemma subst_var_Ex_e__Let :
forall x2 e2 e3 e1 x1,
  lc e1 ->
  x2 ∉ fv_Ex e1 `union` fv_Ex e3 `union` singleton x1 ->
  subst__x e1 x1 (e__Let e2 e3) = e__Let (subst__x e1 x1 e2) (close_Ex_wrt_Ex x2 (subst__x e1 x1 (open_Ex_wrt_Ex e3 (e__Var_f x2)))).
Proof.
unfold_singletons; exact subst_var_Ex_e__Let.
Qed.

#[export] Hint Resolve subst_var_Ex_e__Let : lngen.

Lemma subst_skvar_Sc_S__Forall :
forall α1 σ1 T1 β1,
  lc T1 ->
  α1 ∉ fsk T1 `union` fsk σ1 `union` singleton β1 ->
  subst (X:=Sc) T1 β1 (S__Forall σ1) = S__Forall (close_Sc_wrt_T α1 (subst (X:=Sc) T1 β1 (open_Sc_wrt_T σ1 (T__Var_f α1)))).
Proof.
unfold_singletons; exact subst_skvar_Sc_S__Forall.
Qed.

#[export] Hint Resolve subst_skvar_Sc_S__Forall : lngen.

Lemma subst_skvar_Tm_t__Lam :
forall tx1 τ1 t1 T1 β1,
  lc T1 ->
  tx1 ∉ fv t1 ->
  subst (X:=Tm) T1 β1 (t__Lam τ1 t1) = t__Lam (subst (X:=T) T1 β1 τ1) (close_Tm_wrt_Tm tx1 (subst (X:=Tm) T1 β1 (open_Tm_wrt_Tm t1 (t__Var_f tx1)))).
Proof.
unfold_singletons; exact subst_skvar_Tm_t__Lam.
Qed.

#[export] Hint Resolve subst_skvar_Tm_t__Lam : lngen.

Lemma subst_skvar_Tm_t__TLam :
forall α1 t1 T1 β1,
  lc T1 ->
  α1 ∉ fsk T1 `union` fsk t1 `union` singleton β1 ->
  subst (X:=Tm) T1 β1 (t__TLam t1) = t__TLam (close_Tm_wrt_T α1 (subst (X:=Tm) T1 β1 (open_Tm_wrt_T t1 (T__Var_f α1)))).
Proof.
unfold_singletons; exact subst_skvar_Tm_t__TLam.
Qed.

#[export] Hint Resolve subst_skvar_Tm_t__TLam : lngen.

Lemma subst_tvar_Tm_t__Lam :
forall tx2 τ1 t2 t1 tx1,
  lc (X:=Tm) t1 ->
  tx2 ∉ fv t1 `union` fv t2 `union` singleton tx1 ->
  subst__x t1 tx1 (t__Lam τ1 t2) = t__Lam (τ1) (close_Tm_wrt_Tm tx2 (subst__x t1 tx1 (open_Tm_wrt_Tm t2 (t__Var_f tx2)))).
Proof.
unfold_singletons; exact subst_tvar_Tm_t__Lam.
Qed.

#[export] Hint Resolve subst_tvar_Tm_t__Lam : lngen.

Lemma subst_tvar_Tm_t__TLam :
forall α1 t2 t1 tx1,
  lc (X:=Tm) t1 ->
  α1 ∉ fsk t1 `union` fsk t2 ->
  subst__x t1 tx1 (t__TLam t2) = t__TLam (close_Tm_wrt_T α1 (subst__x t1 tx1 (open_Tm_wrt_T t2 (T__Var_f α1)))).
Proof.
unfold_singletons; exact subst_tvar_Tm_t__TLam.
Qed.

#[export] Hint Resolve subst_tvar_Tm_t__TLam : lngen.

(*hidden lems removed*)

Lemma subst_var_Ex_intro_rec :
forall e1 x1 e2 n1,
  x1 ∉ fv_Ex e1 ->
  open_Ex_wrt_Ex_rec n1 e2 e1 = subst__x e2 x1 (open_Ex_wrt_Ex_rec n1 (e__Var_f x1) e1).
Proof.
unfold_singletons; exact subst_var_Ex_intro_rec.
Qed.

#[export] Hint Resolve subst_var_Ex_intro_rec : lngen.
#[export] Hint Rewrite subst_var_Ex_intro_rec using solve [auto] : lngen.

(*hidden lems removed*)

Lemma subst_skvar_T_intro_rec :
forall T1 β1 T2 n1,
  β1 ∉ fsk T1 ->
  open_T_wrt_T_rec n1 T2 T1 = subst (X:=T) T2 β1 (open_T_wrt_T_rec n1 (T__Var_f β1) T1).
Proof.
unfold_singletons; exact subst_skvar_T_intro_rec.
Qed.

#[export] Hint Resolve subst_skvar_T_intro_rec : lngen.
#[export] Hint Rewrite subst_skvar_T_intro_rec using solve [auto] : lngen.

(*hidden lems removed*)

Lemma subst_skvar_Sc_intro_rec :
forall Sc1 β1 T1 n1,
  β1 ∉ fsk Sc1 ->
  open_Sc_wrt_T_rec n1 T1 Sc1 = subst (X:=Sc) T1 β1 (open_Sc_wrt_T_rec n1 (T__Var_f β1) Sc1).
Proof.
unfold_singletons; exact subst_skvar_Sc_intro_rec.
Qed.

#[export] Hint Resolve subst_skvar_Sc_intro_rec : lngen.
#[export] Hint Rewrite subst_skvar_Sc_intro_rec using solve [auto] : lngen.

(*hidden lems removed*)

Lemma subst_skvar_Tm_intro_rec :
forall t1 β1 T1 n1,
  β1 ∉ fsk t1 ->
  open_Tm_wrt_T_rec n1 T1 t1 = subst (X:=Tm) T1 β1 (open_Tm_wrt_T_rec n1 (T__Var_f β1) t1).
Proof.
unfold_singletons; exact subst_skvar_Tm_intro_rec.
Qed.

#[export] Hint Resolve subst_skvar_Tm_intro_rec : lngen.
#[export] Hint Rewrite subst_skvar_Tm_intro_rec using solve [auto] : lngen.

(*hidden lems removed*)

Lemma subst_tvar_Tm_intro_rec :
forall t1 tx1 t2 n1,
  tx1 ∉ fv t1 ->
  open_Tm_wrt_Tm_rec n1 t2 t1 = subst__x t2 tx1 (open_Tm_wrt_Tm_rec n1 (t__Var_f tx1) t1).
Proof.
unfold_singletons; exact subst_tvar_Tm_intro_rec.
Qed.

#[export] Hint Resolve subst_tvar_Tm_intro_rec : lngen.
#[export] Hint Rewrite subst_tvar_Tm_intro_rec using solve [auto] : lngen.

Lemma subst_var_Ex_intro :
forall x1 e1 e2,
  x1 ∉ fv_Ex e1 ->
  open_Ex_wrt_Ex e1 e2 = subst__x e2 x1 (open_Ex_wrt_Ex e1 (e__Var_f x1)).
Proof.
unfold_singletons; exact subst_var_Ex_intro.
Qed.

#[export] Hint Resolve subst_var_Ex_intro : lngen.

Lemma subst_skvar_T_intro :
forall β1 T1 T2,
  β1 ∉ fsk T1 ->
  open_T_wrt_T T1 T2 = subst (X:=T) T2 β1 (open_T_wrt_T T1 (T__Var_f β1)).
Proof.
unfold_singletons; exact subst_skvar_T_intro.
Qed.

#[export] Hint Resolve subst_skvar_T_intro : lngen.

Lemma subst_skvar_Sc_intro :
forall β1 Sc1 T1,
  β1 ∉ fsk Sc1 ->
  open_Sc_wrt_T Sc1 T1 = subst (X:=Sc) T1 β1 (open_Sc_wrt_T Sc1 (T__Var_f β1)).
Proof.
unfold_singletons; exact subst_skvar_Sc_intro.
Qed.

#[export] Hint Resolve subst_skvar_Sc_intro : lngen.

Lemma subst_skvar_Tm_intro :
forall β1 t1 T1,
  β1 ∉ fsk t1 ->
  open_Tm_wrt_T t1 T1 = subst (X:=Tm) T1 β1 (open_Tm_wrt_T t1 (T__Var_f β1)).
Proof.
unfold_singletons; exact subst_skvar_Tm_intro.
Qed.

#[export] Hint Resolve subst_skvar_Tm_intro : lngen.

Lemma subst_tvar_Tm_intro :
forall tx1 t1 t2,
  tx1 ∉ fv t1 ->
  open_Tm_wrt_Tm t1 t2 = subst__x t2 tx1 (open_Tm_wrt_Tm t1 (t__Var_f tx1)).
Proof.
unfold_singletons; exact subst_tvar_Tm_intro.
Qed.

#[export] Hint Resolve subst_tvar_Tm_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

(*ltac removed*)
