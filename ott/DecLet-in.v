 | Dec__Let : forall (L:vars) (psi:E) (e1 e2:Ex) (tau:T) (a:A) (tau1:T) (t1 t2:Tm),
      (FrA  a    (E_O_skvars  psi )  )  ->
     Dec (E__A psi a) e1 tau1 t1 ->
      ( forall x , x \notin   L -> Dec (E__Var psi x  (close_Sc_wrt_A ( S__T  tau1  )  a ) )  ( open_Ex_wrt_Ex e2 (e__Var_f x) )  tau  ( open_Tm_wrt_Tm t2 (t__Var_f x) )  )  ->
     Dec psi (e__Let e1 e2) tau (t__Let  (close_Sc_wrt_A ( S__T  tau1  )  a )   (close_Tm_wrt_A  t1   a )  t2).
