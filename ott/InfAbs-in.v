 | Inf__Abs : forall (L:vars) (psi__in:E) (e:Ex) (a1 a2:A) (tau1 tau2:T) (t:Tm) (psi__out:E) (alpha:skvar)
     (FR:  ( alpha  ∉ (E_O_skvars  psi__in )) )
     (INF:  ( forall x , x \notin   L   -> Inf (E__Var (E__A psi__in  (  alpha  :: nil ) ) x (S__T (T__Skvar_f alpha)))  ( open_Ex_wrt_Ex e (e__Var_f x) )  a2 tau2  ( open_Tm_wrt_Tm t (t__Tvar_f x) )  (E__Var (E__A psi__out a1) x (S__T tau1)) ) ),
     Inf psi__in (e__Lam e)  (  a2  ++  a1  )  (T__Fun tau1 tau2) (t__Lam (S__T tau1) t) psi__out
