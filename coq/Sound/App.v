Set Warnings "-notation-overridden".
Require Import Preamble.

Require Import Defs.EInst.

Lemma U_unifies : forall ψ__in τ1 τ2 ψ__out,
    U ψ__in τ1 τ2 ψ__out
  -> exists τ__u, U (ψ__in ::o ⦇t__Unit ▸ ⟨[]⟩ S__T τ1⦈ ::o ⦇t__Unit ▸ ⟨[]⟩ S__T τ2⦈) τ1 τ2 (ψ__out ::o ⦇t__Unit ▸ ⟨[]⟩ S__T τ__u⦈ ::o ⦇t__Unit ▸ ⟨[]⟩ S__T τ__u⦈).
Admitted.

Lemma U_maintains_instantiation : forall ψ__in τ1 τ2 ψ__out ψ__dec,
    U ψ__in τ1 τ2 ψ__out
  -> ψ__out ⤳' ψ__dec
  -> ψ__in  ⤳' ψ__dec.
Admitted.
