Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.

Notation  "ψ ⊢d e ▸ τ ⤳ t" := (Dec ψ e τ t) (at level 70, format "ψ  ⊢d  e  ▸  τ  ⤳  t" ) : type_scope.
