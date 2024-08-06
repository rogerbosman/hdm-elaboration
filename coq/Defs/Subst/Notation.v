Set Warnings "-notation-overridden".
Require Import Preamble.

Notation  "{ τ ≔__x α } x"   := (subst__x τ α x) (at level 50, format "{ τ  ≔__x  α } x") : type_scope.
Notation  "{ τ ≔ α } x"   := (subst τ α x) (at level 50, format "{ τ  ≔  α } x") : type_scope.

Class renamable_skvar (X : Type) (Var : Type) := rename_skvar : Var -> Var -> X -> X.

Notation  "{ α ↤ β } x" := (rename_skvar α β x) (at level 50, format "{ α  ↤  β } x") : type_scope.

Class renamable_name (X : Type) (Var : Type) := rename_name : Var -> Var -> X -> X.

Notation  "{ α ↤__x β } X" := (rename_name α β X) (at level 50, format "{ α  ↤__x  β } X") : type_scope.
