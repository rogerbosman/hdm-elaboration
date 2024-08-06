Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.
Require Import Defs.HdmLems.
Require Import Preamble.Tag.

Require Import Defs.E.
Require Import Defs.ERels.
Require Import Defs.FrA.
Require Import Defs.Shape.
Require Import Defs.Subst.
Require Import Defs.WfE.

Require Import Coq.Relations.Relation_Operators.

Notation  "p ⟶ p'" := (Uss p p') (at level 70) : type_scope.
Notation Us := (clos_refl_trans_1n E_and_Eqs Uss).
Notation  "p ⟶* p'" := (Us p p') (at level 70) : type_scope.

#[export] Hint Rewrite app_length : core.

(*** Wf *)
Lemma U_Wf : forall ψ__in τ1 τ2 ψ__out,
    U ψ__in τ1 τ2 ψ__out
  -> wf(ψ__in)
  -> wf(ψ__out).
Admitted.

(*** Random *)

Lemma subst_skvar_τ_SameShape__τ : forall τ1 τ2 α,
    SameShape__τ τ1 (subst_skvar_T τ2 α τ1).
Proof. intro τ1. induction τ1; intros; simpl+; crush. Qed.

Lemma subst_skvar_σ_SameShape__σ : forall σ τ1 α,
    SameShape__σ σ (subst_skvar_Sc τ1 α σ).
Proof.
  intros σ. induction σ; intros; simpl+.
  - econstructor. apply subst_skvar_τ_SameShape__τ.
  - econstructor. crush.
Qed.

Lemma subst_skvar_t_SameShape__t : forall t τ1 α,
    SameShape__t t (subst_skvar_Tm τ1 α t).
Proof. intro t. induction t; intros; simpl+; solve [crush|econstructor; eauto using subst_skvar_τ_SameShape__τ, subst_skvar_σ_SameShape__σ]. Qed.

Lemma subst_skvar_E_SameShape__E : forall ψ τ1 α,
    SameShape__E ψ (subst τ1 α ψ).
Proof.
  intro ψ.
  induction ψ; intros; simpl+.
  - crush.
  - econstructor. eauto. reflexivity.
  - eauto using subst_skvar_σ_SameShape__σ.
  - econstructor. eauto. eauto using subst_skvar_t_SameShape__t. reflexivity.
    eauto using subst_skvar_σ_SameShape__σ.
Qed.

Lemma Uss_SameShape : forall ψ1 Eqs1 ψ2 Eqs2,
    (ψ1, Eqs1) ⟶ (ψ2, Eqs2)
  -> SameShape__E ψ1 ψ2.
Proof.
  introv STEP. inverts STEP. 1,2,3:crush.
  - norm. eapply SSE_app.
    econstructor. crush. econstructor. intros.
    simpl+. crush. eauto using subst_skvar_E_SameShape__E.
  - norm. eapply SSE_app.
    econstructor. crush. econstructor. intros.
    simpl+. crush. eauto using subst_skvar_E_SameShape__E.
  - norm. eapply SSE_app.
    econstructor. crush. econstructor. intros.
    simpl+. crush. eauto using subst_skvar_E_SameShape__E.
Qed.

Lemma Us_SameShape' : forall p1 p2,
    Us p1 p2
  -> SameShape__E (fst p1) (fst p2).
Proof.
  introv Us. induction Us. crush. destruct x. destruct y.
  etransitivity. eauto using Uss_SameShape. crush.
Qed.
Lemma Us_SameShape : forall ψ1 Eqs1 ψ2 Eqs2,
    Us (ψ1, Eqs1) (ψ2, Eqs2)
  -> SameShape__E ψ1 ψ2.
Proof. intros. applys_eq Us_SameShape'. 3:eassumption. all:simpl+; crush. Qed.

Lemma U_SameShape : forall ψ1 ψ2 τ1 τ2,
    U ψ1 τ1 τ2 ψ2
  -> SameShape__E ψ1 ψ2.
Proof. introv UNI. inverts UNI. eauto using Us_SameShape. Qed.

Lemma U_SameLength : forall ψ1 ψ2 τ1 τ2,
    U ψ1 τ1 τ2 ψ2
  -> SameLength__E ψ1 ψ2.
Proof. eauto using SSE_length, U_SameShape. Qed.

(* Lemma Us_alg_E : forall ψ1 Eqs1 ψ2 Eqs2, *)
(*     Uss ψ1 Eqs1 ψ2 Eqs2 *)
(*   -> alg_E ψ1 *)
(*   -> alg_E ψ2. *)

Lemma E_skvars_subst_skvar_E : forall (ψ:E) α (τ:T),
    E_skvars ({τ ≔ α}ψ) ⊆ fv__α(τ) ∪ E_skvars(ψ).
Proof.
  intros. induction ψ; simpl+. fsetdec. rewrite IHψ. reldec.
  rewrite fsk_Sc_subst_skvar_Sc_upper. fsetdec.
  rewrite fsk_Sc_subst_skvar_Sc_upper. rewrite fsk_Tm_subst_skvar_Tm_upper. fsetdec.
Qed.

Lemma alg_in_alg_L : forall α L,
    α ∈ L
  -> alg_L L
  -> alg α.
Proof. intros. unfold alg_L in *. eauto. Qed.

Lemma Uss_alg_E : forall ψ1 Eqs1 ψ2 Eqs2,
    Uss (ψ1, Eqs1) (ψ2, Eqs2)
  -> alg_E ψ1
  -> alg_E ψ2.
Proof.
  introv U ALG. inverts U.
  - crush.
  - crush.
  - crush.
  - unfold alg_E in *. simpl+.
    apply alg_L_union.
    + apply alg_L_union. apply alg_L_union.
      applys alg_L_subset ALG. reldec.
      apply alg_L_union. simpl+. assumption.
      apply alg_L_union. simpl+. assumption.
      applys alg_L_subset ALG. reldec.
      applys alg_L_subset ALG. reldec.
    + unfold alg_L. introv IN. rewrite E_skvars_subst_skvar_E in IN. destr_union. simpl+ in H.
      destr_union; crush. apply ALG. reldec.
  - unfold alg_E. simpl+. rewrite E_skvars_subst_skvar_E. simpl+.
    apply alg_L_union. applys alg_L_subset ALG. reldec.
    apply alg_L_union. applys alg_L_subset ALG. rewrite E_A_skvars_E_skvars in H2. simpl+ in H2. reldec.
    applys alg_L_subset ALG. reldec.
  - unfold alg_E. simpl+. rewrite E_skvars_subst_skvar_E. simpl+.
    applys alg_L_subset ALG. reldec.
Qed.

Lemma Us_alg_E' : forall p1 p2,
    Us p1 p2
  -> alg_E (fst p1)
  -> alg_E (fst p2).
Proof.
  introv UNI ALG. induction UNI. crush. destruct x. destruct y.
  eapply IHUNI. simpl+. eauto using Uss_alg_E.
Qed.
Lemma Us_alg_E : forall ψ1 Eqs1 ψ2 Eqs2,
    Us (ψ1, Eqs1) (ψ2, Eqs2)
  -> alg_E ψ1
  -> alg_E ψ2.
Proof. intros. applys_eq Us_alg_E'. 2:eassumption. all:simpl+; crush. Qed.

Lemma U_alg_E : forall ψ1 τ1 τ2 ψ2,
    U ψ1 τ1 τ2 ψ2
  -> alg_E ψ1
  -> alg_E ψ2.
Proof. introv UNI ALG. inverts UNI. eauto using Us_alg_E. Qed.

(*** Subst_name *)
Lemma rename_name_E_app : forall α β (ψ1 ψ2:E),
    {β ↤__x α}(ψ1 +++ ψ2) = ({β ↤__x α}ψ1) +++ ({β ↤__x α}ψ2).
Proof. intros. induction ψ2; simpl+; crush. Qed.
#[export] Hint Rewrite rename_name_E_app : sub_dist.


Lemma rename_name_E_subst_skvar_E : forall x__in x__out α τ ψ,
    {x__in ↤__x x__out}({τ ≔ α}ψ) = {τ ≔ α}({x__in ↤__x x__out}ψ).
Proof.
  introv. induction ψ. 2:induction a.
  all:simpl+. 1,2,3,4:crush.
  rewrite IHψ. fequals. rewrite subst_tvar_Tm_subst_skvar_Tm. crush. fsetdec.
Qed.


Lemma Uss_subst_name : forall x__in x__out ψ1 Eqs1 ψ2 Eqs2,
    Uss (ψ1, Eqs1) (ψ2, Eqs2)
  -> Uss ({x__in ↤__x x__out}ψ1, Eqs1) ({x__in ↤__x x__out}ψ2, Eqs2).
Proof.
  introv UNI. inverts UNI. crush. crush. crush.
  - dist. applys_eq Uss__Split. norm. simpl+. fequals. fequals.
    rewrite rename_name_E_subst_skvar_E. crush.
    eapply FrA_L_sub. eassumption. reldec. all:eassumption.
  - dist. applys_eq Uss__SubEx. norm. simpl+. fequals. fequals.
    rewrite rename_name_E_subst_skvar_E. crush.
    simpl+. simpl+ in H2. fsetdec. eassumption.
  - dist. applys_eq Uss__SubUnit. norm. simpl+. fequals. fequals.
    rewrite rename_name_E_subst_skvar_E. crush.
    eassumption.
Qed.

Lemma Us_subst_name' : forall x__in x__out p1 p2,
    Us p1 p2
  -> Us ({x__in ↤__x  x__out}(fst p1), snd p1) ({x__in ↤__x  x__out}(fst p2), snd p2).
Proof.
  introv UNI. induction UNI. econstructor. destruct x. destruct y. destruct z.
  forwards: Uss_subst_name. eassumption. econstructor. eassumption. eassumption.
Qed.
Lemma Us_subst_name : forall x__in x__out ψ1 Eqs1 ψ2 Eqs2,
    Us (ψ1, Eqs1) (ψ2, Eqs2)
  -> Us ({x__in ↤__x  x__out}ψ1, Eqs1) ({x__in ↤__x  x__out}ψ2, Eqs2).
Proof. intros. applys_eq Us_subst_name'. 3:eassumption. all:simpl+; crush. Qed.

Lemma U_subst_name : forall x__in x__out ψ__in τ1 τ2 ψ__out,
    U ψ__in τ1 τ2 ψ__out
  -> U ({x__in ↤__x  x__out}ψ__in) τ1 τ2 ({x__in ↤__x x__out}ψ__out).
Proof. introv UNI. inverts UNI. econstructor. eauto using Us_subst_name. Qed.

(*** Insert_ANil_at *)
Fact Insert_ANil_at_inj : forall n ψ1 ψ2 ψ2',
    Insert_ANil_at n ψ1 ψ2
  -> Insert_ANil_at n ψ1 ψ2'
  -> ψ2' = ψ2.
Proof.
  introv IN1 IN2. gen ψ2'. induction IN1; intros.
  - inverts IN2. crush.
    forwards EQ__n: Insert_ANil_at_smaller. eassumption. simpl+ in EQ__n. crush.
    forwards EQ__n: Insert_ANil_at_smaller. eassumption. simpl+ in EQ__n. crush.
    forwards EQ__n: Insert_ANil_at_smaller. eassumption. simpl+ in EQ__n. crush.
  - inverts IN2.
    forwards EQ__n: Insert_ANil_at_smaller. eassumption. simpl+ in EQ__n. crush.
    fequals. eauto.
  - inverts IN2.
    forwards EQ__n: Insert_ANil_at_smaller. eassumption. simpl+ in EQ__n. crush.
    fequals. eauto.
  - inverts IN2.
    forwards EQ__n: Insert_ANil_at_smaller. eassumption. simpl+ in EQ__n. crush.
    fequals. eauto.
Qed.

Fact Insert_ANil_at_app_exact : forall ψ1 ψ2,
    Insert_ANil_at (E_length ψ1) (ψ1 +++ ψ2) ((ψ1 ::a []) +++ ψ2).
Proof. introv. induction ψ2. crush. all:simpl+; eauto. Qed.

Fact Insert_ANil_at_app_exact' : forall ψ1 ψ2,
    Insert_ANil_at (E_length ψ1) ψ1 ψ2
  -> ψ2 = ψ1 ::a [].
Proof.
  intros. inverts H. crush.
  all:apply Insert_ANil_at_smaller in H0; simpl+ in H0; crush.
Qed.

Fact Insert_ANil_at_app_ge : forall ψ1 ψ2 ψ n,
    Insert_ANil_at n (ψ1 +++ ψ2) ψ
  -> n > E_length ψ1
  -> exists ψ1' ψ2',
      ψ = ψ1' +++ ψ2'
    /\ ψ1' = ψ1
    /\ Insert_ANil_at (n - E_length ψ1) ψ2 ψ2'.
Proof.
  intros. dependent induction H.
  - exists. splits. norm. rewrite E_app_assoc. reflexivity. reflexivity.
    applys_eq Insert_ANil_at_app_exact. simpl+. crush. instantiate (1 := •). crush. crush.
  - destruct ψ2; simpl+ in x; inverts x.
    forwards: Insert_ANil_at_smaller. eassumption. crush.
    specializes IHInsert_ANil_at. reflexivity. assumption.
    destruct IHInsert_ANil_at as [ψ1' [ψ2' [? [? IN]]]].
    exists. splits. 3:econstructor; eassumption. subst. crush. crush.
  - destruct ψ2; simpl+ in x; inverts x.
    forwards: Insert_ANil_at_smaller. eassumption. crush.
    specializes IHInsert_ANil_at. reflexivity. assumption.
    destruct IHInsert_ANil_at as [ψ1' [ψ2' [? [? IN]]]].
    exists. splits. 3:econstructor; eassumption. subst. crush. crush.
  - destruct ψ2; simpl+ in x; inverts x.
    forwards: Insert_ANil_at_smaller. eassumption. crush.
    specializes IHInsert_ANil_at. reflexivity. assumption.
    destruct IHInsert_ANil_at as [ψ1' [ψ2' [? [? IN]]]].
    exists. splits. 3:econstructor; eassumption. subst. crush. crush.
Qed.

Fact Insert_ANil_at_app_ge_constr : forall ψ1 ψ2 ψ2' n,
    Insert_ANil_at (n - E_length ψ1) ψ2 ψ2'
  -> n > E_length ψ1
  -> Insert_ANil_at n (ψ1 +++ ψ2) (ψ1 +++ ψ2').
Proof.
  introv IN GE. dependent induction IN.
  applys_eq Here. crush.
  all:simpl+; eauto.
Qed.

Fact Insert_ANil_at_app_leq : forall ψ1 ψ2 ψ n,
    Insert_ANil_at n (ψ1 +++ ψ2) ψ
  -> n <= E_length ψ1
  -> exists ψ1' ψ2',
      ψ = ψ1' +++ ψ2'
    /\ ψ2' = ψ2
    /\ Insert_ANil_at n ψ1 ψ1'.
Proof.
  intros. dependent induction H.
  - destruct ψ2; simpl+ in H0. 2,3,4: crush. simpl+.
    exists. splits. 2:reflexivity. simpl+. reflexivity. eauto using Insert_ANil_at_app_exact.
  - destruct ψ2; simpl+ in x; inverts x.
    + exists. splits. 2:reflexivity. simpl+. reflexivity. constructor. eassumption.
    + specializes IHInsert_ANil_at. 2:eassumption. crush. destr.
      exists. splits. 2:reflexivity. crush. crush.
  - destruct ψ2; simpl+ in x; inverts x.
    + exists. splits. 2:reflexivity. simpl+. reflexivity. constructor. eassumption.
    + specializes IHInsert_ANil_at. 2:eassumption. crush. destr.
      exists. splits. 2:reflexivity. crush. crush.
  - destruct ψ2; simpl+ in x; inverts x.
    + exists. splits. 2:reflexivity. simpl+. reflexivity. constructor. eassumption.
    + specializes IHInsert_ANil_at. 2:eassumption. crush. destr.
      exists. splits. 2:reflexivity. crush. crush.
Qed.

Fact Insert_ANil_at_app_leq_constr : forall ψ1 ψ1' ψ2 n,
    Insert_ANil_at n ψ1 ψ1'
  -> n <= E_length ψ1
  -> Insert_ANil_at n (ψ1 +++ ψ2) (ψ1' +++ ψ2).
Proof.
  introv IN LEQ. induction ψ2. crush.
  all:simpl+; eauto.
Qed.

Fact Insert_ANil_at_app : forall n ψ1 ψ2 ψ,
    Insert_ANil_at n (ψ1 +++ ψ2) ψ
  -> exists ψ1' ψ2',
      ψ = ψ1' +++ ψ2'
    /\ ( (n > E_length ψ1 /\ ψ1' = ψ1 /\ Insert_ANil_at (n - E_length ψ1) ψ2 ψ2')
      \/ (n <= E_length ψ1 /\ ψ2' = ψ2 /\ Insert_ANil_at n ψ1 ψ1')).
Proof.
  intros. forwards: (gt_eq_gt_dec n (E_length ψ1)). destruct H0.
  - forwards: Insert_ANil_at_app_leq. eassumption. crush. destr. exists. splits; crush.
  - forwards: Insert_ANil_at_app_ge. eassumption. crush. destr. exists. splits; crush.
Qed.

Fact subst_skvar_E_SameLengthE : forall ψ τ α,
    SameLength__E ψ ({τ ≔ α}ψ).
Proof. introv. eauto using SSE_length, subst_skvar_E_SameShape__E. Qed.

Fact Insert_ANil_at_subst_skvar_E : forall n ψ1 ψ2 τ α,
    Insert_ANil_at n ψ1 ψ2
  -> Insert_ANil_at n ({τ ≔ α}ψ1) ({τ ≔ α}ψ2).
Proof.
  introv IN. induction IN; simpl+; crush.
  forwards: Here ({τ ≔ α}ψ). applys_eq H.
  apply subst_skvar_E_SameLengthE.
Qed.

Fact Insert_ANil_at_destr' : forall n ψ ψ',
    Insert_ANil_at n ψ ψ'
  -> exists ψ1 ψ2, ψ = ψ1 +++ ψ2 /\ n = E_length ψ1 /\ ψ' = (ψ1 ::a []) +++ ψ2.
Proof.
  introv IN. induction IN.
  - exists ψ •. splits; crush.
  - destr. exists. splits. norm. rewrite <- E_app_assoc. reflexivity. all:crush.
  - destr. exists. splits. norm. rewrite <- E_app_assoc. reflexivity. all:crush.
  - destr. exists. splits. norm. rewrite <- E_app_assoc. reflexivity. all:crush.
Qed.

Fact sub_succ : forall x, S x - x = 1.
Proof. induction x; crush. Qed.

Lemma subst_skvar_E_app : forall ψ1 ψ2 τ α,
    {τ ≔ α} (ψ1 +++ ψ2) = ({τ ≔ α} ψ1) +++ ({τ ≔ α} ψ2).
Proof. introv. induction ψ2; simpl+; crush. Qed.
#[export] Hint Rewrite subst_skvar_E_app : sub_dist.

Lemma Uss_Insert_ANil_at : forall n ψ1 ψ1' ψ2 Eqs1 Eqs2,
    Uss (ψ1, Eqs1) (ψ2, Eqs2)
  -> Insert_ANil_at n ψ1 ψ1'
  -> exists ψ2',
      Insert_ANil_at n ψ2 ψ2'
    /\ Uss (ψ1', Eqs1) (ψ2', Eqs2).
Proof.
  introv UNI IN. inverts UNI.
  - exists. splits. eassumption. auto.
  - exists. splits. eassumption. auto.
  - exists. splits. eassumption. auto.
  - eapply Insert_ANil_at_app in IN. destruct IN as [?ψ [?ψ [?EQ IN]]]. destruct IN; destr.
    2:norm in H2; eapply Insert_ANil_at_app in H2; destruct H2 as [?ψ [?ψ [?EQ H2]]]; destruct H2; destr.
    + forwards: Insert_ANil_at_destr'. eassumption. destr.
      exists. splits.
      * eapply Insert_ANil_at_app_ge_constr. simpl+ in H2. simpl+.
        eauto using Insert_ANil_at_subst_skvar_E. crush.
      * econstructor. FrA_L_sub. all: eassumption.
    + forwards: Insert_ANil_at_destr'. eassumption. destr.
      simpl+ in H0. assert (n = S (E_length ψ0)). destruct H1; crush. subst.
      rewrite sub_succ in H.
      assert (ψ4 = •). destruct ψ4. crush.
        inverts H2. destruct ψ4; simpl+ in H9; inverts H9. inverts H. inverts H2. inverts H2. subst.
      simpl+ in H2. subst.
      exists. splits.
      * eapply Insert_ANil_at_app_leq_constr. norm. eapply Insert_ANil_at_app_ge_constr.
        rewrite sub_succ. applys_eq Here. simpl+. crush. crush. crush.
      * applys_eq Uss__Split. instantiate (4 := <[]>a +++ ψ3). simpl+. reflexivity.
        simpl+. dist. reflexivity. FrA_L_sub. all:eassumption.
    + exists. splits.
      * eapply Insert_ANil_at_app_leq_constr. 2:crush.
        norm. eapply Insert_ANil_at_app_leq_constr. 2:crush. eassumption.
      * forwards: Insert_ANil_at_destr'. eassumption. destr.
        applys_eq Uss__Split. FrA_L_sub. all:eassumption.
  - eapply Insert_ANil_at_app in IN. destruct IN as [?ψ [?ψ [?EQ IN]]]. destruct IN; destr.
    2:norm in H3; eapply Insert_ANil_at_app in H3; destruct H3 as [?ψ [?ψ [?EQ H3]]]; destruct H3; destr.
    + forwards: Insert_ANil_at_destr'. eassumption. destr.
      exists. splits.
      * eapply Insert_ANil_at_app_ge_constr. simpl+ in H2. simpl+.
        eauto using Insert_ANil_at_subst_skvar_E. crush.
      * econstructor. all: eassumption.
    + forwards: Insert_ANil_at_destr'. eassumption. destr.
      simpl+ in H0. assert (n = S (E_length ψ0)). destruct H1; crush. subst.
      rewrite sub_succ in H.
      assert (ψ4 = •). destruct ψ4. crush.
        inverts H3. destruct ψ4; simpl+ in H7; inverts H7. inverts H. inverts H3. inverts H3. subst.
      simpl+ in H3. subst.
      exists. splits.
      * eapply Insert_ANil_at_app_leq_constr. norm. eapply Insert_ANil_at_app_ge_constr.
        rewrite sub_succ. applys_eq Here. simpl+. crush. crush. crush.
      * applys_eq Uss__SubEx. instantiate (4 := <[]>a +++ ψ3). simpl+. reflexivity.
        simpl+. dist. reflexivity. all:eassumption.
    + exists. splits.
      * eapply Insert_ANil_at_app_leq_constr. 2:crush.
        norm. eapply Insert_ANil_at_app_leq_constr. 2:crush. eassumption.
      * forwards: Insert_ANil_at_destr'. eassumption. destr.
        applys_eq Uss__SubEx. simpl+. simpl+ in H2. fsetdec. all:eassumption.
  - eapply Insert_ANil_at_app in IN. destruct IN as [?ψ [?ψ [?EQ IN]]]. destruct IN; destr.
    2:norm in H3; eapply Insert_ANil_at_app in H3; destruct H3 as [?ψ [?ψ [?EQ H3]]]; destruct H3; destr.
    + forwards: Insert_ANil_at_destr'. eassumption. destr.
      exists. splits.
      * eapply Insert_ANil_at_app_ge_constr. simpl+ in H. simpl+.
        eauto using Insert_ANil_at_subst_skvar_E. crush.
      * econstructor. all: eassumption.
    + forwards: Insert_ANil_at_destr'. eassumption. destr.
      simpl+ in H4. assert (n = S (E_length ψ0)). destruct H; crush. subst.
      rewrite sub_succ in H.
      assert (ψ4 = •). destruct ψ4. crush.
        inverts H3. destruct ψ4; simpl+ in H6; inverts H6. inverts H. inverts H3. inverts H3. subst.
      simpl+ in H3. subst.
      exists. splits.
      * eapply Insert_ANil_at_app_leq_constr. norm. eapply Insert_ANil_at_app_ge_constr.
        rewrite sub_succ. applys_eq Here. simpl+. crush. crush. crush.
      * applys_eq Uss__SubUnit. instantiate (4 := <[]>a +++ ψ3). simpl+. reflexivity.
        simpl+. dist. reflexivity. all:eassumption.
    + exists. splits.
      * eapply Insert_ANil_at_app_leq_constr. 2:crush.
        norm. eapply Insert_ANil_at_app_leq_constr. 2:crush. eassumption.
      * forwards: Insert_ANil_at_destr'. eassumption. destr.
        applys_eq Uss__SubUnit. all:eassumption.
Qed.

Lemma Us_Insert_ANil_at' : forall n ψ1' p1 p2,
    Us p1 p2
  -> Insert_ANil_at n (fst p1) ψ1'
  -> exists ψ2', Insert_ANil_at n (fst p2) ψ2'
         /\ Us (ψ1', snd p1) (ψ2', snd p2).
Proof.
  introv US IN1. gen ψ1'. induction US; intros; destruct x; simpl+ in *.
  - exists. splits. eassumption. constructor.
  - destruct y. forwards [ψ [IN' UNI']]: Uss_Insert_ANil_at. eassumption. eassumption.
    specializes IHUS. eassumption.
    destruct IHUS as [ψ2' [IN'' UNI''']].
    exists. split. eassumption. econstructor; eassumption.
Qed.
Lemma Us_Insert_ANil_at : forall n ψ1' ψ1 ψ2 Eqs1 Eqs2,
    Us (ψ1, Eqs1) (ψ2, Eqs2)
  -> Insert_ANil_at n ψ1 ψ1'
  -> exists ψ2', Insert_ANil_at n ψ2 ψ2'
         /\ Us (ψ1', Eqs1) (ψ2', Eqs2).
Proof. intros. applys_eq Us_Insert_ANil_at'. 2:eassumption. all:simpl+; crush. Qed.

Lemma U_Insert_ANil_at : forall n ψ__in ψ__in' ψ__out τ1 τ2,
    U ψ__in τ1 τ2 ψ__out
  -> Insert_ANil_at n ψ__in ψ__in'
  -> exists ψ__out', Insert_ANil_at n ψ__out ψ__out'
           /\ U ψ__in' τ1 τ2 ψ__out'.
Proof. intros. inverts H. forwards: Us_Insert_ANil_at. eassumption. eassumption. destr. exists. crush. Qed.
