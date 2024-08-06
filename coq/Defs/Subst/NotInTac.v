Set Warnings "-notation-overridden".
Require Import Preamble.

Require Import Defs.Subst.HdmSubst.

Ltac subst_notin' :=
  let H := fresh "H" in
  match goal with
    | [ |- context[subst ?t ?α ?x] ]  =>
        match type of x with
        | Sc => rewrite subst_skvar_Sc_notin
        | T  => rewrite subst_skvar_T_notin
        | Tm => rewrite subst_skvar_Tm_notin
        end; try reflexivity
    | [ |- context[subst__x ?t ?α ?x] ]  =>
        match type of x with
        | Tm => rewrite subst_tvar_Tm_notin
        end; try reflexivity
    | [ |- context[subst_skvar_Sc ?t ?α ?x] ]  =>
        rewrite subst_skvar_Sc_notin
    | [ |- context[subst_skvar_T ?t ?α ?x] ]  =>
        rewrite subst_skvar_T_notin
    | [ |- context[subst_skvar_Tm ?t ?α ?x] ]  =>
        rewrite subst_skvar_Tm_notin
  end.
Ltac subst_notin := subst_notin'; try solve [fsetdec+|crush].
