Set Warnings "-notation-overridden".
Require Import Metalib.Metatheory.

Module Type WSfunPlus (X : DecidableType).

  Include FSetExtra.WSfun X.

  (* #[export] Instance SetInterface_inst : SetInterface t X.t := *)
  (*   { Sempty     := empty *)

  (*   ; Sunion     := union *)
  (*   ; Sinter     := inter *)
  (*   ; Sdiff      := diff *)

  (*   ; SEqual     := Equal *)
  (*   ; SSubset    := Subset *)
  (*   ; Sdisjoint  := disjoint *)

  (*   ; SIn        := In *)

  (*   ; Sadd       := add *)
  (*   ; Ssingleton := singleton *)
  (*   }. *)

  (* #[export] Instance Semptyable_inst : Semptyable t := { Sempty := empty }. *)

  (* #[export] Instance Sunionable_inst     : Sunionable     t     := { Sunion := union }. *)
  (* #[export] Instance Sinterable_inst     : Sinterable     t     := { Sinter := inter }. *)
  (* #[export] Instance Sdiffable_inst      : Sdiffable      t     := { Sdiff := diff }. *)

  (* #[export] Instance SEqualable_inst     : SEqualable     t     := { SEqual := Equal }. *)
  (* #[export] Instance SSubsetable_inst    : SSubsetable    t     := { SSubset := Subset }. *)
  (* #[export] Instance Sdisjointable_inst  : Sdisjointable  t     := { Sdisjoint := disjoint }. *)

  (* #[export] Instance SInable_inst        : SInable        t X.t := { SIn := In }. *)

  (* #[export] Instance Saddable_inst       : Saddable       t X.t := { Sadd := add }. *)
  (* #[export] Instance Ssingletonable_inst : Ssingletonable t X.t := { Ssingleton := singleton }. *)

  (* #[export] Hint Unfold Semptyable_inst     : SetInterface. *)

  (* #[export] Hint Unfold Sunionable_inst     : SetInterface. *)
  (* #[export] Hint Unfold Sinterable_inst     : SetInterface. *)
  (* #[export] Hint Unfold Sdiffable_inst      : SetInterface. *)

  (* #[export] Hint Unfold SEqualable_inst     : SetInterface. *)
  (* #[export] Hint Unfold SSubsetable_inst    : SetInterface. *)
  (* #[export] Hint Unfold Sdisjointable_inst  : SetInterface. *)

  (* #[export] Hint Unfold SInable_inst        : SetInterface. *)

  (* #[export] Hint Unfold Saddable_inst       : SetInterface. *)
  (* #[export] Hint Unfold Ssingletonable_inst : SetInterface. *)

End WSfunPlus.

Module MakePlus (X : DecidableType) <: WSfunPlus X.

  Include FSetExtra.Make X.

  (* #[export] Instance SetInterface_inst : SetInterface t X.t := *)
  (*   { Sempty     := empty *)

  (*   ; Sunion     := union *)
  (*   ; Sinter     := inter *)
  (*   ; Sdiff      := diff *)

  (*   ; SEqual     := Equal *)
  (*   ; SSubset    := Subset *)
  (*   ; Sdisjoint  := disjoint *)

  (*   ; SIn        := In *)

  (*   ; Sadd       := add *)
  (*   ; Ssingleton := singleton *)
  (*   }. *)

  (* #[export] Instance Semptyable_inst : Semptyable t := { Sempty := empty }. *)

  (* #[export] Instance Sunionable_inst     : Sunionable     t     := { Sunion := union }. *)
  (* #[export] Instance Sinterable_inst     : Sinterable     t     := { Sinter := inter }. *)
  (* #[export] Instance Sdiffable_inst      : Sdiffable      t     := { Sdiff := diff }. *)

  (* #[export] Instance SEqualable_inst     : SEqualable     t     := { SEqual := Equal }. *)
  (* #[export] Instance SSubsetable_inst    : SSubsetable    t     := { SSubset := Subset }. *)
  (* #[export] Instance Sdisjointable_inst  : Sdisjointable  t     := { Sdisjoint := disjoint }. *)

  (* #[export] Instance SInable_inst        : SInable        t X.t := { SIn := In }. *)

  (* #[export] Instance Saddable_inst       : Saddable       t X.t := { Sadd := add }. *)
  (* #[export] Instance Ssingletonable_inst : Ssingletonable t X.t := { Ssingleton := singleton }. *)

  (* Instance Semptyable_inst : Semptyable t := { Sempty := empty }. *)

  (* Instance Sunionable_inst     : Sunionable     t     := { Sunion := union }. *)
  (* Instance Sinterable_inst     : Sinterable     t     := { Sinter := inter }. *)
  (* Instance Sdiffable_inst      : Sdiffable      t     := { Sdiff := diff }. *)

  (* Instance SEqualable_inst     : SEqualable     t     := { SEqual := Equal }. *)
  (* Instance SSubsetable_inst    : SSubsetable    t     := { SSubset := Subset }. *)
  (* Instance Sdisjointable_inst  : Sdisjointable  t     := { Sdisjoint := disjoint }. *)

  (* Instance SInable_inst        : SInable        t X.t := { SIn := In }. *)

  (* Instance Saddable_inst       : Saddable       t X.t := { Sadd := add }. *)
  (* Instance Ssingletonable_inst : Ssingletonable t X.t := { Ssingleton := singleton }. *)
End MakePlus.

Module SetInterface (Import X : DecidableType)(Import M : FSetExtra.WSfun X).
  (* #[export] Instance SetInterface_inst : SetInterface t X.t := *)
  (*   { Sempty     := empty *)

  (*   ; Sunion     := union *)
  (*   ; Sinter     := inter *)
  (*   ; Sdiff      := diff *)

  (*   ; SEqual     := Equal *)
  (*   ; SSubset    := Subset *)
  (*   ; Sdisjoint  := disjoint *)

  (*   ; SIn        := In *)

  (*   ; Sadd       := add *)
  (*   ; Ssingleton := singleton *)
  (*   }. *)

  (* #[export] Instance Semptyable_inst : Semptyable t := { Sempty := empty }. *)

  (* #[export] Instance Sunionable_inst     : Sunionable     t     := { Sunion := union }. *)
  (* #[export] Instance Sinterable_inst     : Sinterable     t     := { Sinter := inter }. *)
  (* #[export] Instance Sdiffable_inst      : Sdiffable      t     := { Sdiff := diff }. *)

  (* #[export] Instance SEqualable_inst     : SEqualable     t     := { SEqual := Equal }. *)
  (* #[export] Instance SSubsetable_inst    : SSubsetable    t     := { SSubset := Subset }. *)
  (* #[export] Instance Sdisjointable_inst  : Sdisjointable  t     := { Sdisjoint := disjoint }. *)

  (* #[export] Instance SInable_inst        : SInable        t X.t := { SIn := In }. *)

  (* #[export] Instance Saddable_inst       : Saddable       t X.t := { Sadd := add }. *)
  (* #[export] Instance Ssingletonable_inst : Ssingletonable t X.t := { Ssingleton := singleton }. *)

  (* #[export] Hint Unfold Semptyable_inst     : SetInterface. *)

  (* #[export] Hint Unfold Sunionable_inst     : SetInterface. *)
  (* #[export] Hint Unfold Sinterable_inst     : SetInterface. *)
  (* #[export] Hint Unfold Sdiffable_inst      : SetInterface. *)

  (* #[export] Hint Unfold SEqualable_inst     : SetInterface. *)
  (* #[export] Hint Unfold SSubsetable_inst    : SetInterface. *)
  (* #[export] Hint Unfold Sdisjointable_inst  : SetInterface. *)

  (* #[export] Hint Unfold SInable_inst        : SetInterface. *)

  (* #[export] Hint Unfold Saddable_inst       : SetInterface. *)
  (* #[export] Hint Unfold Ssingletonable_inst : SetInterface. *)
End SetInterface.
