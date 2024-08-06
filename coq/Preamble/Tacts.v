Set Warnings "-notation-overridden".
Require Import Defs.HdmDefs.

Require Export Metalib.Metatheory.
Require Export Cpdtlib.CpdtTactics.
(* Require Export LibTactics.LibTactics. *)
Require Export TLC.LibTactics.

Ltac introx := intros ?x ?NIL__x.
Ltac introy := intros ?y ?NIL__y.
Ltac introz := intros ?z ?NIL__z.
Ltac introα := intros ?α ?NIL__α.
Ltac introβ := intros ?β ?NIL__β.

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

Ltac destr_rename H :=
  let WfT := fresh "WfT" in
  match type of H with
  | (lc(_)) => let LC := fresh "LC" in rename H into LC
  | (_ ⊆ _) => let SUB := fresh "SUB" in rename H into SUB
  | (_ ⊢wfσ _) => let WfS := fresh "WfS" in rename H into WfS
  | (_ ⊢wfτ _) => let WfT := fresh "WfT" in rename H into WfT
  | (_ ⊢wft _) => let Wft := fresh "Wft" in rename H into Wft
  end.

Ltac destr :=
  repeat match goal with
  | [ H : ex (fun x => _) |- _ ] => let x := fresh x in destruct H as [x H]
  | [ H : _ /\ _ |- _ ] =>
      let H1 := fresh "H" in
      let H2 := fresh "H" in
      destruct H as [H1 H2]; try destr_rename H1; try destr_rename H2
  | [ H : (_,_) = (_,_) |- _ ] => inverts H
  end; subst.

(* Ltac rename_vars := *)
(*     try (rename ein into e__in) *)
(*   ; try (rename eout into e__out) *)
(*   ; try (rename ain into a__in) *)
(*   ; try (rename aout into a__out). *)
Ltac constructor_eq :=
  match goal with
    | |- EInst _ _ _ (_ ::a _          ) _ _ => applys_eq EInst__A; try symmetry
    | |- EInst _ _ _ (_ ::x _ :- _     ) _ _ => applys_eq EInst__S; try symmetry
    | |- EInst _ _ _ (_ ::o ⦇_ ▸ ⟨_⟩ _⦈) _ _ => applys_eq EInst__O; try symmetry
  end.

Ltac if_taut :=
  let EQ := fresh "EQ" in
  repeat match goal with
    | [ |- context[if ?X then _ else _] ]       => destruct X as [EQ|?]; try congruence; try clear EQ
    | [ H : context[if ?X then _ else _] |- _ ] => destruct X as [EQ|?]; try congruence; try clear EQ
  end.

Ltac if_dec :=
  let EQ := fresh "EQ" in
  repeat match goal with
    | [ |- context[if ?X then _ else _] ]       => destruct X as [EQ|?]; [subst|idtac]
    | [ H : context[if ?X then _ else _] |- _ ] => destruct X as [EQ|?]; [subst|idtac]
  end.

Ltac if_same :=
  match goal with
    | [ |- context[if ?B then ?E1 else ?E1] ]      =>
        asserts_rewrite ((if B then E1 else E1) = E1) in *; [destruct B; simpl; reflexivity|idtac]
    | [ H : context[if ?B then ?E1 else ?E1] |- _ ] =>
        asserts_rewrite ((if B then E1 else E1) = E1) in *; [destruct B; simpl; reflexivity|idtac]
  end.

Ltac lt_eq_dec :=
  let EQ := fresh "EQ" in
  repeat match goal with
    | [ |- context[lt_eq_lt_dec ?n ?m] ] => destruct (lt_eq_lt_dec n m) as [[?LE|?EQ]|?LE]; try subst m
    | [ H : context[lt_eq_lt_dec ?n ?m] |- _ ] => destruct (lt_eq_lt_dec n m) as [[?LE|?EQ]|?LE]; try subst m
  end.

Ltac inv :=
  repeat match goal with
    | [ H : True |- _ ]
      => clear H
    | [ H : S__T _ = S__T _ |- _ ]
      => inverts H
  end.

Ltac cleanhyps :=
  repeat match goal with
    | [ H : True |- _ ]
      => clear H
    | [ H : ?x = ?x |- _ ]
      => clear H
    | [ H : FrA nil _ |- _ ]
      => clear H
    | [ H : ⟦_ ▹ T__Unit⟧ = T__Unit |- _ ]
      => clear H
    | [ H : ⟦_ ▹ t__Unit⟧ = t__Unit |- _ ]
      => clear H
  end.

Tactic Notation "rewr" :=
  autounfold with algs
  ;
  autorewrite with core buildins WFacts List_to_Set E_to_Set
  .
Tactic Notation "rewr" "in" hyp(H) :=
  autounfold with algs
  in H
  ;
  autorewrite with core buildins WFacts List_to_Set E_to_Set
  in H.
Tactic Notation "rewr" "in" "*" :=
  autounfold with algs
  in *
  ;
  autorewrite with core buildins WFacts List_to_Set E_to_Set
  in *.

Tactic Notation "simpl+" :=
  repeat (cbn; rewr).
Tactic Notation "simpl+" "in" hyp(H) :=
  repeat (cbn in H; rewr in H).
Tactic Notation "simpl+" "in" "*" :=
  repeat (cbn in *; rewr in *); cleanhyps.

Tactic Notation "dist" :=
  repeat(autorewrite with sub_dist; simpl+).
Tactic Notation "dist" "in" hyp(H) :=
  repeat(autorewrite with sub_dist in H; simpl+ in H).
Tactic Notation "dist" "in" "*" :=
  repeat(autorewrite with sub_dist in *; simpl+ in *).

Tactic Notation "crush+" := autounfold with defs in *; crush.

Ltac flds :=
  repeat(
    try (fold Sub_app_Sc)
  ).

Ltac destr_in H :=
    match type of H with
    | _ \/ _ => let H1 := fresh "H" in let H2 := fresh "H" in destruct H as [H1|H2]; [try destr_in H1|try destr_in H2]
    | ex (fun x => _) => let x := fresh x in destruct H as [x H]; try destr_in H
    end; subst.

Ltac destr_eq x y := destruct (eq_dec x y); [subst|idtac].


Tactic Notation "rewrite+" hyp(H) := autounfold with rels in H; rewrite H.
Tactic Notation "rewrite+" "<-" hyp(H) := autounfold with rels in H; rewrite <- H.

Ltac Sets_switch T__atoms T__TSet T__ScSet T__TmSet T__PairTSet T__PairScSet :=
  match goal with
    | |- AtomSetImpl.Equal _ _ => T__atoms
    | |- TSetI.Equal       _ _ => T__TSet
    | |- ScSetI.Equal      _ _ => T__ScSet
    | |- TmSetI.Equal      _ _ => T__TSet
    | |- PairTSetI.Equal   _ _ => T__PairTSet
    | |- PairScSetI.Equal  _ _ => T__PairScSet

    | |- AtomSetImpl.Subset _ _ => T__atoms
    | |- TSetI.Subset       _ _ => T__TSet
    | |- ScSetI.Subset      _ _ => T__ScSet
    | |- TmSetI.Subset       _ _ => T__TmSet
    | |- PairTSetI.Subset   _ _ => T__PairTSet
    | |- PairScSetI.Subset  _ _ => T__PairScSet

    | |- AtomSetImpl.In _ _ => T__atoms
    | |- TSetI.In       _ _ => T__TSet
    | |- ScSetI.In      _ _ => T__ScSet
    | |- TmSetI.In       _ _ => T__TmSet
    | |- PairTSetI.In   _ _ => T__PairTSet
    | |- PairScSetI.In  _ _ => T__PairScSet
  end.

(*** Fsetdec *)
Ltac fsetdec'' := AtomSetDecide.fsetdec || TSetD.fsetdec || ScSetD.fsetdec || TmSetD.fsetdec || PairTSetD.fsetdec || PairScSetD.fsetdec.

(** Base *)
Ltac fsetdec'_base := Sets_switch AtomSetDecide.fsetdec TSetD.fsetdec ScSetD.fsetdec TmSetD.fsetdec PairTSetD.fsetdec PairScSetD.fsetdec.

Ltac fsetdec_base := Metalib.MetatheoryAtom.AtomSetDecide.fsetdec.

Tactic Notation "fsetdec'_base" := fsetdec'_base.
Ltac fsetdecplus_base :=
  autounfold with defs in *; simpl+ in *; fsetdec_base.
Tactic Notation "fsetdec+_base" := fsetdecplus_base.
Ltac fsetdec'plus_base :=
  autounfold with defs in *; simpl+ in *; fsetdec'_base.
Tactic Notation "fsetdec'+_base" := fsetdec'plus_base.

Tactic Notation "clfsetdec" := clear; fsetdec_base.
Tactic Notation "clfsetdec'" := clear; fsetdec'_base.
Tactic Notation "clfsetdec+" := clear; fsetdec+_base.
Tactic Notation "clfsetdec'+" := clear; fsetdec'+_base.

(** Normal *)
Ltac fsetdec                := fsetdec_base.
Tactic Notation "fsetdec'"  := fsetdec'_base.
Tactic Notation "fsetdec+"  := fsetdecplus_base.
Tactic Notation "fsetdec'+" := fsetdec'plus_base.

(** Debug *)
(* Ltac tryclear tac := solve [clear; tac; idtac "could clear first!" *)
(*                            | tac *)
(*                            ]. *)

(* Ltac fsetdec                := tryclear fsetdec_base. *)
(* Tactic Notation "fsetdec'"  := tryclear fsetdec'_base. *)
(* Tactic Notation "fsetdec+"  := tryclear fsetdecplus_base. *)
(* Tactic Notation "fsetdec'+" := tryclear fsetdec'plus_base. *)

(** Time *)
(* Ltac fsetdec                := time fsetdec_base. *)
(* Tactic Notation "fsetdec'"  := time fsetdec'_base. *)
(* Tactic Notation "fsetdec+"  := time fsetdecplus_base. *)
(* Tactic Notation "fsetdec'+" := time fsetdec'plus_base. *)

(*** Instantiation NIL statements *)
Lemma Sub_union_split : forall L1 L2 L3,
    L1 ∪ L2 ⊆ L3
  -> L1 ⊆ L3
  /\ L2 ⊆ L3.
Proof. intros. split; fsetdec. Qed.
Corollary Sub_union_split__l : forall L1 L2 L3,
    L1 ∪ L2 ⊆ L3
  -> L1 ⊆ L3.
Proof. apply Sub_union_split. Qed.
Corollary Sub_union_split__r : forall L1 L2 L3,
    L1 ∪ L2 ⊆ L3
  -> L2 ⊆ L3.
Proof. apply Sub_union_split. Qed.

Ltac Sub_extend_in_L' Sub L :=
  (is_evar L; applys Sub) ||
  match L with
    | ?L__l ∪ ?L__r => eapply Sub_union_split__r; Sub_extend_in_L' Sub L__r
  end.
Ltac Sub_extend_in_L Sub L := eapply Sub_union_split__l; Sub_extend_in_L' Sub L.

Ltac extend_in H :=
  match type of H with
  | (?L ⊆ _) => Sub_extend_in_L H L
  end.

Example test__sub : forall (L0 : atoms), exists L2, forall (L1 : atoms), L2 ⊆ L1 -> False.
Proof.
  intro. exists. intros.

  assert (L0 ⊆ L1). intros.
  extend_in H.
Abort.

(*** Forwards *)
Tactic Notation "forwards>" ":" constr(E) :=
  forwards: ZifyClasses.rew_iff E.
Tactic Notation "forwards>" ":" constr(E0)
 constr(A1) :=
  forwards: ZifyClasses.rew_iff E0 A1.
Tactic Notation "forwards>" ":" constr(E0)
 constr(A1) constr(A2) :=
  forwards: ZifyClasses.rew_iff E0 A1 A2.
Tactic Notation "forwards>" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  forwards: ZifyClasses.rew_iff E0 A1 A2 A3.
Tactic Notation "forwards>" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  forwards: ZifyClasses.rew_iff E0 A1 A2 A3 A4.

Tactic Notation "forwards>" simple_intropattern(I) ":" constr(E0) :=
  forwards I: ZifyClasses.rew_iff E0.
Tactic Notation "forwards>" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) :=
  forwards I: ZifyClasses.rew_iff E0 A1 A2.
Tactic Notation "forwards>" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  forwards I: ZifyClasses.rew_iff E0 A1 A2 A3.
Tactic Notation "forwards>" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  forwards I: ZifyClasses.rew_iff E0 A1 A2 A3 A4.

Tactic Notation "forwards<" ":" constr(E) :=
  forwards: ZifyClasses.rew_iff_rev E.
Tactic Notation "forwards<" ":" constr(E0)
 constr(A1) :=
  forwards: ZifyClasses.rew_iff_rev E0 A1.
Tactic Notation "forwards<" ":" constr(E0)
 constr(A1) constr(A2) :=
  forwards: ZifyClasses.rew_iff_rev E0 A1 A2.
Tactic Notation "forwards<" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  forwards: ZifyClasses.rew_iff_rev E0 A1 A2 A3.
Tactic Notation "forwards<" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  forwards: ZifyClasses.rew_iff_rev E0 A1 A2 A3 A4.

Tactic Notation "forwards<" simple_intropattern(I) ":" constr(E0) :=
  forwards I: ZifyClasses.rew_iff_rev E0.
Tactic Notation "forwards<" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) :=
  forwards I: ZifyClasses.rew_iff_rev E0 A1 A2.
Tactic Notation "forwards<" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  forwards I: ZifyClasses.rew_iff_rev E0 A1 A2 A3.
Tactic Notation "forwards<" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  forwards I: ZifyClasses.rew_iff_rev E0 A1 A2 A3 A4.

Ltac reldec := autounfold with rels; simpl+; fsetdec.
Ltac reldec' := autounfold with rels; simpl+; fsetdec'.
