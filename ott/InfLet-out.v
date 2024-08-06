 | Inf__Let : forall (L:vars) (psi__in:E) (e1 e2:Ex) (a2:A) (tau2:T) (sigma__out:Sc) (t1' t2:Tm) (psiout:E) (a1:A) (tau:T) (t1:Tm) (psi1:E),
     Inf psi__in e1 a1 tau t1 psi1 ->
      ( forall tx , tx \notin  L  ->  ( forall x , x \notin   L  \u {{ tx }}  -> Inf  (E__O  (E__Var psi1 x  (close_Sc_wrt_A ( S__T  tau  )  a1 ) )    (close_Tm_wrt_A  t1   a1 )   (nil:A) (S__T T__Unit))   ( open_Ex_wrt_Ex e2 (e__Var_f x) )  a2 tau2  ( open_Tm_wrt_Tm t2 (t__Tvar_f tx) )   (E__O  (E__Var psiout x sigma__out)   t1'  (nil:A) (S__T T__Unit))  )  )  ->
     Inf psi__in (e__Let e1 e2) a2 tau2 (t__Let sigma__out t1' t2) psiout.
