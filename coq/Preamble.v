Set Warnings "-notation-overridden".

Require Export Defs.HdmDefs.
(* Require Export Defs.HdmLemsOrig. *)
(* Require Export Defs.HdmLems. *)

Require Export Preamble.Buildins.
Require Export Preamble.Tacts.
(* Require Export Preamble.Tag. *)
(* Require Export Preamble.NILInst. *)
Require Export Preamble.SetFacts.

Require Export Classes.Morphisms.
Require Export Coq.Program.Equality.
Require Export Metalib.Metatheory.
(* Require Export LibTactics.LibTactics. *)
Require Export TLC.LibTactics.
Require Export Cpdtlib.CpdtTactics.

Notation "[ ]" := nil (format "[ ]").
Notation "[ x ]" := (one x).
Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..)) : list_scope.

Require Export Preamble.Tacts.

(** To let the set stuff point to what is defined in HdmDefs *)
Require Export Defs.HdmDefs.
(** To let eq point to Leibniz equality again*)
Require Export Coq.Init.Logic.
(** To let map point to list map again *)
Require Export Coq.Lists.List.

From Equations Require Import Equations.
