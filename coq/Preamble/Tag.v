Set Warnings "-notation-overridden,-intuition-auto-with-star".

(* Require Import Prelude. *)
Require Import Preamble.

Require Import Defs.HdmDefs.

Tactic Notation "unfold_alg_dec" :=
  autounfold with alg_dec.
Tactic Notation "unfold_alg_dec" "in" hyp(H) :=
  autounfold with alg_dec in H.
Tactic Notation "unfold_alg_dec" "in" "*" :=
  autounfold with alg_dec in *.

(*** Alternative freshess *)
Lemma atom_fresh_alg : forall L : atoms, { x : atom | ~ In x L /\ alg x }.
Proof.
  intros L. destruct (TaggedAtom.atom_fresh_for_list_taggedtrue (AtomSetImpl.elements L)) as [a [H H']].
  exists a. split. intros J. contradiction H.
  rewrite <- CoqListFacts.InA_iff_In. auto using AtomSetImpl.elements_1.
  crush.
Qed.

Lemma atom_fresh_dec : forall L : atoms, { x : atom | ~ In x L /\ dec x }.
Proof.
  intros L. destruct (TaggedAtom.atom_fresh_for_list_taggedfalse (AtomSetImpl.elements L)) as [a [H H']].
  exists a. split. intros J. contradiction H.
  rewrite <- CoqListFacts.InA_iff_In. auto using AtomSetImpl.elements_1.
  crush.
Qed.

Ltac freshalgx L := forwards [?x [?NIL__x ?ALG]] : atom_fresh_alg L.
Ltac freshalgx' := freshalgx empty.
Ltac freshalgy L := forwards [?y [?NIL__y ?ALG]]: atom_fresh_alg L.
Ltac freshalgy' := freshalgy empty.
Ltac freshalgz L := forwards [?z [?NIL__z ?ALG]]: atom_fresh_alg L.
Ltac freshalgz' := freshalgz empty.
Ltac freshalgα L := forwards [?α [?NIL__α ?ALG]]: atom_fresh_alg L.
Ltac freshalgα' := freshalgα empty.
Ltac freshalgβ L := forwards [?y [?NIL__β ?ALG]]: atom_fresh_alg L.
Ltac freshalgβ' := freshalgβ empty.

Ltac freshdecx L := forwards [?x [?NIL__x ?DEC]] : atom_fresh_dec L.
Ltac freshdecx' := freshdecx empty.
Ltac freshdecy L := forwards [?y [?NIL__y ?DEC]]: atom_fresh_dec L.
Ltac freshdecy' := freshdecy empty.
Ltac freshdecz L := forwards [?z [?NIL__z ?DEC]]: atom_fresh_dec L.
Ltac freshdecz' := freshdecz empty.
Ltac freshdecα L := forwards [?α [?NIL__α ?DEC]]: atom_fresh_dec L.
Ltac freshdecα' := freshdecα empty.
Ltac freshdecβ L := forwards [?y [?NIL__β ?DEC]]: atom_fresh_dec L.
Ltac freshdecβ' := freshdecβ empty.

(*** Lems *)
Fact L_alg_dec_disj : forall L1 L2,
    alg_L L1
  -> dec_L L2
  -> L1 ∐ L2.
Proof.
  introv ALG DEC. unfolds. unfolds. split. 2:fsetdec. intro.
  specializes ALG a. specializes ALG. fsetdec.
  specializes DEC a. specializes DEC. fsetdec.
  false.
Qed.

Fact alg_L_union : forall L1 L2,
    alg_L L1
  -> alg_L L2
  -> alg_L (L1 ∪ L2).
Admitted.

Fact alg_L_singleton : forall α,
    alg_L {{α}}
  <-> alg α.
Admitted.
#[export] Hint Rewrite alg_L_singleton : core.
Corollary alg_L_singleton' : forall α,
    alg α
  -> alg_L {{α}}.
Proof. intros. simpl+. assumption. Qed.
#[export] Hint Resolve alg_L_singleton' : core.

Fact alg_L_subset : forall L1 L2,
    alg_L L2
  -> L1 ⊆ L2
  -> alg_L L1.
Proof. intros. intro. intro. apply H. crush. Qed.
Fact dec_L_subset : forall L1 L2,
    dec_L L2
  -> L1 ⊆ L2
  -> dec_L L1.
Proof. intros. intro. intro. apply H. crush. Qed.
#[export] Instance alg_L_subset_proper : Proper (flip Subset ==> impl) alg_L.
Proof. autounfold. intros. eauto using alg_L_subset. Qed.
#[export] Instance dec_L_subset_proper : Proper (flip Subset ==> impl) dec_L.
Proof. autounfold. intros. eauto using dec_L_subset. Qed.


Fact alg_L_nil : alg_L (∅). unfolds. crush. Qed.
Fact dec_L_nil : dec_L (∅). unfolds. crush. Qed.
#[export] Hint Resolve alg_L_nil dec_L_nil : core.

#[export] Instance subset_alg_proper : Proper (flip Subset ==> impl) alg_L.
Proof. autounfold. intros. eauto using alg_L_subset. Qed.
#[export] Instance subset_dec_proper : Proper (flip Subset ==> impl) dec_L.
Proof. autounfold. intros. eauto using dec_L_subset. Qed.

Fact alg_E_nil : alg_E •. unfolds. simpl+. crush. Qed.
Fact dec_E_nil : dec_E •. unfolds. simpl+. crush. Qed.
#[export] Hint Resolve alg_E_nil dec_E_nil : core.

Fact alg_E_varl_a : forall a,
    alg_L (varl a) = alg_A a.
Proof. reflexivity. Qed.
#[export] Hint Rewrite alg_E_varl_a : core.

Fact alg_E_app : forall ψ1 ψ2,
    alg_E ψ1
  -> alg_E ψ2
  -> alg_E (ψ1 +++ ψ2).
Proof. intros. unfold alg_E in *. simpl+. eapply alg_L_union; crush. Qed.

Fact alg_E_oneA : forall a,
    alg_E <a>a <-> alg_A a.
Proof.
  unfold alg_E. unfold alg_A. intros. simpl+. split; intros.
  eapply alg_L_subset. eassumption. fsetdec.
  eapply alg_L_subset. eassumption. fsetdec.
Qed.
#[export] Hint Rewrite alg_E_oneA : core.

Lemma alg_E_subset : forall ψ1 ψ2,
    alg_E ψ2
  -> E_skvars ψ1 ⊆ E_skvars ψ2
  -> alg_E ψ1.
Proof. unfold alg_E. intros. eapply alg_L_subset. eassumption. eassumption. Qed.

Fact alg_union : forall L1 L2,
    alg_L (L1 ∪ L2)
  <-> alg_L L1
  /\ alg_L L2.
Admitted.
Corollary alg_union1 : forall L1 L2,
    alg_L (L1 ∪ L2)
  -> alg_L L1.
Proof. apply alg_union. Qed.
Corollary alg_union2 : forall L1 L2,
    alg_L (L1 ∪ L2)
  -> alg_L L2.
Proof. apply alg_union. Qed.
Corollary alg_union3 : forall L1 L2,
    alg_L L1
  -> alg_L L2
  -> alg_L (L1 ∪ L2).
Proof. intros. eapply alg_union; crush. Qed.
#[export] Hint Resolve alg_union1 alg_union2 alg_union3 : core.

Fact dec_union : forall L1 L2,
    dec_L (L1 ∪ L2)
  <-> dec_L L1
  /\ dec_L L2.
Admitted.
Corollary dec_union1 : forall L1 L2,
    dec_L (L1 ∪ L2)
  -> dec_L L1.
Proof. apply dec_union. Qed.
Corollary dec_union2 : forall L1 L2,
    dec_L (L1 ∪ L2)
  -> dec_L L2.
Proof. apply dec_union. Qed.
Corollary dec_union3 : forall L1 L2,
    dec_L L1
  -> dec_L L2
  -> dec_L (L1 ∪ L2).
Proof. intros. eapply dec_union; crush. Qed.
#[export] Hint Resolve dec_union1 dec_union2 dec_union3 : core.

Lemma alg_E_cons_a1 : forall ψ a,
    alg_E (ψ ::a a)
  -> alg_E ψ.
Proof. intros. applys alg_L_subset H. simpl+. fsetdec. Qed.
Lemma alg_E_cons_a2 : forall ψ a,
    alg_E (ψ ::a a)
  -> alg_A a.
Proof. intros. applys alg_L_subset H. simpl+. fsetdec. Qed.
#[export] Hint Resolve alg_E_cons_a1 alg_E_cons_a2 : core.
Lemma alg_E_cons_x : forall ψ x σ,
    alg_E (ψ ::x x :- σ)
  -> alg_E ψ.
Proof. intros. applys alg_L_subset H. simpl+. fsetdec. Qed.
#[export] Hint Resolve alg_E_cons_x : core.
Lemma alg_E_cons_o1 : forall ψ t a σ,
    alg_E (ψ ::o ⦇t ▸ ⟨a⟩ σ⦈)
  -> alg_E ψ.
Proof. intros. applys alg_L_subset H. simpl+. fsetdec. Qed.
Lemma alg_E_cons_o2 : forall ψ t a σ,
    alg_E (ψ ::o ⦇t ▸ ⟨a⟩ σ⦈)
  -> alg_A a.
Proof. intros. applys alg_L_subset H. simpl+. fsetdec. Qed.
#[export] Hint Resolve alg_E_cons_o1 alg_E_cons_o2 : core.

Lemma dec_E_cons_a1 : forall ψ a,
    dec_E (ψ ::a a)
  -> dec_E ψ.
Proof. intros. applys dec_L_subset H. simpl+. fsetdec. Qed.
Lemma dec_E_cons_a2 : forall ψ a,
    dec_E (ψ ::a a)
  -> dec_A a.
Proof. intros. applys dec_L_subset H. simpl+. fsetdec. Qed.
#[export] Hint Resolve dec_E_cons_a1 dec_E_cons_a2 : core.
Lemma dec_E_cons_x : forall ψ x σ,
    dec_E (ψ ::x x :- σ)
  -> dec_E ψ.
Proof. intros. applys dec_L_subset H. simpl+. fsetdec. Qed.
#[export] Hint Resolve dec_E_cons_x : core.
Lemma dec_E_cons_o1 : forall ψ t a σ,
    dec_E (ψ ::o ⦇t ▸ ⟨a⟩ σ⦈)
  -> dec_E ψ.
Proof. intros. applys dec_L_subset H. simpl+. fsetdec. Qed.
Lemma dec_E_cons_o2 : forall ψ t a σ,
    dec_E (ψ ::o ⦇t ▸ ⟨a⟩ σ⦈)
  -> dec_A a.
Proof. intros. applys dec_L_subset H. simpl+. fsetdec. Qed.
#[export] Hint Resolve dec_E_cons_o1 dec_E_cons_o2 : core.

Lemma alg_A_nil : alg_A []. unfolds. crush. Qed.
#[export] Hint Resolve alg_A_nil : core.

Fact alg_A_cons : forall α a,
    alg α
  -> alg_A a
  -> alg_A (α :: a).
Proof. intros. unfolds. simpl+. eapply alg_L_union; crush. Qed.
