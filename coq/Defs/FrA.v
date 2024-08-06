Set Warnings "-notation-overridden".

Require Import Preamble.

Require Import Defs.NoDup.
Require Import Defs.List.

Notation  "a ### ψ"  := (FrA a ψ) (at level 50, format "a  ###  ψ") : type_scope.

(*** Rewriting *)
Fact FrA_L_sub : forall (a:A) (L1 L2:vars),
    a ### L1
  -> L2 ⊆ L1
  -> a ### L2.
Proof. intros. unfold FrA in *. split. crush. simpl+ in *. crush. Qed.
#[export] Hint Resolve FrA_L_sub : core.
#[export] Instance FrA_Env_sub_proper : Proper (eq ==> flip Subset ==> impl) FrA. autounfold. intros. subst. eauto. Qed.

Ltac FrA_L_sub_in_with H a1 L1 :=
  match type of H with
    | FrA ?a2 ?L2 => asserts_rewrite (L1 ⊆ L2); (only 1: solve[clfsetdec+|fsetdec+]); applys H; crush
  end.

Ltac FrA_L_sub_in H :=
  match goal with
    | |- FrA ?a ?L => FrA_L_sub_in_with H a L
  end.
Ltac FrA_L_sub :=
  match goal with
    | H : ?a ### _ |- _ =>
        match goal with
          | |- a ### ?L => FrA_L_sub_in_with H a L
        end
  end.

(*** Props *)
Fact FrA_props: forall a L,
    a ### L
  -> NoDup a
  /\ varl a ∐ L.
Proof. unfold FrA. crush. Qed.
Ltac FrA_props_in H := apply FrA_props in H; destruct H as [?ND ?FR].
Corollary FrA_props1 : forall a L,
    a ### L
  -> NoDup a.
Proof. apply FrA_props. Qed.
Corollary FrA_props2 : forall a L,
    a ### L
  -> varl a ∐ L.
Proof. apply FrA_props. Qed.
#[export] Hint Resolve FrA_props1 FrA_props2 : core.

Fact FrA_nil : forall ψ,
    [] ### ψ.
Proof. constructor; crush. Qed.
#[export] Hint Resolve FrA_nil : core.

(*** Constructing *)
Fact FrA_cons : forall α a L,
    FrA (α :: a) L
  <-> FrA a L
  /\ α ∉ L ∪ varl a.
Proof.
  intros. split; intros.
  - destruct H as [ND NIL]. split. constructor.
    + inverts ND. eassumption.
    + disj_sub.
    + unfold not. intro. destr_union. eapply (in_disj α). eassumption. fsetdec+. eassumption.
      inverts ND. crush.
  - destruct H as [FR NI]. split.
    + constructor. intro. apply NI. auto. eauto.
    + simpl+. disj_union. simpl+. intros. fsetdec. crush.
Qed.

Corollary FrA_cons1 : forall α a L,
    FrA (α :: a) L
  -> FrA a L.
Proof. apply FrA_cons. Qed.
Corollary FrA_cons2 : forall α a L,
    FrA (α :: a) L
  -> α ∉ L ∪ varl a.
Proof. apply FrA_cons. Qed.
#[export] Hint Resolve FrA_cons1 FrA_cons2 : core.

Fact FrA_app : forall a1 a2 L1 L2,
    a1 ### L1
  -> a2 ### L2
  -> varl a1 ∪ L1 ⊆ L2
  -> (a2 ++ a1) ### L1.
Proof.
  introv FR1 FR2 SUB. ind_a a2. crush. constructor.
  - simpl+. constructor. introv IN.
    apply in_app_or in IN. destruct IN as [IN|IN].
    + inverts FR2. inverts H. crush.
    + inverts FR2. simpl+ in H0.
      applys in_disj α. eassumption. fsetdec+. rewrite <- SUB. auto.
    + eauto.
  - simpl+. disj_union. simpl+. inverts FR2. simpl+ in H0. rewrite <- SUB in H0.
    intro. applys in_disj α. eassumption. fsetdec. fsetdec.
    forwards: IHa2. eauto. inverts H. simpl+ in H1. assumption.
Qed.

Lemma FrA_shift : forall α a L,
    (α :: a) ### L
  -> a ### (L ∪ {{α}}).
Proof.
  introv FRA. econstructor. eauto.
  symmetry. disj_union. symmetry. eauto. unfold disjoint.
  assert (α ∉ varl a).
  apply FrA_props1 in FRA. inverts FRA. crush.
  fsetdec.
Qed.

Lemma FrA_shift' : forall α a L,
    a ### (L ∪ {{α}})
  -> α ∉ L
  -> (α :: a) ### L.
Proof.
  intros. eapply FrA_cons. split. FrA_L_sub.
  apply notin_union_iff. assumption.
  apply FrA_props2 in H. in_disj.
Qed.

Lemma FrA_singleton : forall α L,
    α ∉ L
  -> [α] ### L.
Proof. intros. unfolds. split. auto. simpl+. fsetdec. Qed.

Fact FrA_app' : forall a1 a2 L,
    a1 ### L
  -> a2 ### (L ∪ varl a1)
  -> (a1 ++ a2) ### L.
Proof.
  intros. ind_a a1. crush. simpl+. eapply FrA_cons. split. eapply IHa1. eauto. FrA_L_sub.
  inverts H. simpl+.
  eapply notin_union_iff. in_disj.
  eapply notin_union_iff. inverts H1. eauto.
  eapply FrA_props2 in H0. simpl+ in H0. in_disj.
Qed.
