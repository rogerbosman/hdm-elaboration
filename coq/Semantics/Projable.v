Set Warnings "-notation-overridden".

Require Import Preamble.

Class proj1able (In Out : Type) := π1 : In -> Out.
Class proj2able (In Out : Type) := π2 : In -> Out.
Class projRable (In Var Out : Type) := π__R : In -> Var -> Out.
