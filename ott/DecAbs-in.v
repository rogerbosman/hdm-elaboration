 | Dec__Abs : forall (L:vars) (psi:E) (e:Ex) (tau1 tau2:T) (t:Tm)
     (WFTY:  (WfT  psi   tau1 ) )
     (MON:  ( forall x , x \notin   L  -> Dec (E__Var psi x (S__T tau1))  ( open_Ex_wrt_Ex e (e__Var_f x) )  tau2  ( open_Tm_wrt_Tm t (t__Var_f x) )  ) ),
     Dec psi (e__Lam e) (T__Fun tau1 tau2) (t__Lam tau1 t)
