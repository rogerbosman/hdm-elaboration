Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Defs.HdmDefs.

Ltac unfold_subst :=
   unfold subst; unfold substable_var_Ex
  || unfold subst; unfold substable_var_Tm
  || unfold subst; unfold substable_skvar_Sc
  || unfold subst; unfold substable_skvar_T
  || unfold subst; unfold substable_skvar_Tm.
Ltac unfold_fsk :=
    unfold fsk; unfold fskable_Sc
  || unfold fsk; unfold fskable_T
  || unfold fsk; unfold fskable_Tm.
Ltac unfold_fv :=
    unfold fv; unfold fvable_Tm
  || unfold fv; unfold fvable_Ex.
Ltac unfold_lc :=
    unfold lc; unfold lcable_Ex.
Ltac unfold_singletons := repeat ( unfold_subst || unfold_fsk || unfold_lc || unfold fv).
