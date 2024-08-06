Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Classes.Morphisms.

Require Import Preamble.Tacts.

Require Import Defs.HdmDefs.

Require Import Preamble.Tacts.

(*** Facts module *)
Module WFacts_fun_plus (Import E : DecidableType)(Import M : FSetExtra.WSfun E).
  Include WFacts_fun E M.
  Module Import Dec := WDecide_fun E M.

  (** subrelations *)
  #[export] Instance Equal_Subset_subrelation : subrelation Equal Subset.
  Proof. unfold subrelation. crush. Qed.
  #[export] Instance Equal_flip_Subset_subrelation : subrelation Equal (flip Subset).
  Proof. unfold subrelation. crush. Qed.
  #[export] Instance flip_Equal_Subset_subrelation : subrelation (flip Equal) Subset.
  Proof. unfold subrelation. crush. Qed.
  #[export] Instance flip_Equal_flip_Subset_subrelation : subrelation (flip Equal) (flip Subset).
  Proof. unfold subrelation. crush. Qed.

  (** Automatically assert that In x (singleton y) means x = y and subst *)
  Ltac simpl_singleton :=
    match goal with
        | [ H : In _ (singleton _) |- _ ]
            => rewrite singleton_iff in H; subst
    end.
  Ltac simpl_singleton_in H :=
    match type of H with
        | In _ (singleton _)
            => rewrite singleton_iff in H; subst
    end.

  (** Misc *)
  Ltac destr_union := progress (
    repeat (match goal with
      | [ H : In _ (union _ _) |- _ ]
        => apply union_iff in H; destruct H; simpl+ in H
    end)); try simpl_singleton.

  Fact eq_disj__l : forall L1 L2,
      L1 [=] L2
    -> L1 [<=] L2.
  Proof. intros. crush. Qed.
  Fact eq_disj__r : forall L1 L2,
      L1 [=] L2
    -> L2 [<=] L1.
  Proof. intros. crush. Qed.
  #[export] Hint Resolve eq_disj__l eq_disj__r : core.

  Fact diff_subset : forall L1 L2,
      L1 [<=] L2
    -> diff L1 L2 [=] empty.
  Proof. intros. fsetdec. Qed.
  #[export] Hint Resolve diff_subset : core.

  Lemma singleton_Subset : forall x L,
    singleton x [<=] L -> In x L.
  Proof. fsetdec. Qed.
  #[export] Hint Rewrite singleton_Subset : WFacts.

  (* #[export] Instance In_equiv_proper : Proper (Coq.Init.Logic.eq ==> Equal ==> impl) In. *)
  (* Proof. autounfold. fsetdec. Qed. *)

  (* Unsure if this also exports the unfold *)
  #[export] Hint Unfold disjoint : defs.

  (** Automatically rewrite In x empty to False*)
  Lemma empty_iff' : forall x, In x empty -> False. apply empty_iff. Qed.
  #[export] Hint Resolve empty_iff' : core.
  #[export] Hint Extern 1 =>
    match goal with
      | [ H : In _ empty |- _ ]
        => apply empty_iff' in H
    end : core.

  (** Random rewrites *)
  Lemma union_empty__l : forall L,
      union empty L [=] L.
  Proof. fsetdec. Qed.
  Lemma union_empty__r : forall L,
      union L empty [=] L.
  Proof. fsetdec. Qed.
  #[export] Hint Rewrite union_empty__l union_empty__r : core.

  (*** Disjoint *)
  Fact disjoint_Subset : forall L1 L1' L2 L2',
      disjoint L1 L2
    -> L1' [<=] L1
    -> L2' [<=] L2
    -> disjoint L1' L2'.
  Proof. intros. autounfold with defs in *. fsetdec. Qed.
  #[export] Hint Resolve disjoint_Subset : core.
  #[export] Instance disjoint_subset_proper : Proper (flip Subset ==> flip Subset ==> impl) disjoint. autounfold. crush. eauto. Qed.
  #[export] Instance disjoint_equal_proper : Proper (Equal ==> Equal ==> impl) disjoint. autounfold. intros. eauto. Qed.

  (** Simplify disjointness for singleton *)
  (* Fact disjoint_singleton : forall α L, *)
  (*     disjoint (singleton α) L *)
  (*   -> (In α L -> False). *)
  (* Proof. unfold disjoint. fsetdec. Qed. *)
  Fact disjoint_singleton : forall α L,
      disjoint (singleton α) L
    <-> (In α L -> False).
  Proof. unfold disjoint. split; fsetdec. Qed.
  #[export] Hint Rewrite disjoint_singleton : WFacts.

  (** Solve disjointness goal by looking up a disjointness hyp that has supersets of goal *)
  Ltac disj_sub :=
    match goal with
      | [ |- disjoint ?L1' ?L2' ]
        => match goal with
          | [ H : disjoint ?L1 ?L2 |- _ ] => eapply (disjoint_Subset L1 L1' L2 L2' H); solve [clfsetdec'+|fsetdec'+|crush]
         end
    end.
  Ltac disj_sub_in H :=
    match goal with
      | [ |- disjoint ?L1' ?L2' ] =>
          match type of H with
          | disjoint ?L1 ?L2 => eapply (disjoint_Subset L1 L1' L2 L2' H); solve [fsetdec'+|crush]
          end
  end.

  (** Facts *)
  Fact disj_symm : forall L1 L2,
      disjoint L1 L2
    -> disjoint L2 L1.
  Proof. unfold disjoint. intros. fsetdec. Qed.
  #[export] Hint Resolve disj_symm : med.
  #[export] Instance disjoint_symm : Symmetric disjoint.
  Proof. eauto with med. Qed.

  Lemma disj_union : forall L1 L2 L3,
      disjoint L1 L3
    -> disjoint L2 L3
    -> disjoint (union L1 L2) L3.
  Proof. intros. unfold disjoint in *. fsetdec. Qed.
  #[export] Hint Resolve disj_union : core.

  Lemma disj_union' : forall L1 L2 L3,
      disjoint L1 L2
    -> disjoint L1 L3
    -> disjoint L1 (union L2 L3).
  Proof. intros. eauto with med. Qed.
  #[export] Hint Resolve disj_union' : core.
End WFacts_fun_plus.

(** Manually export disjoint unfold *)
(* #[export] Hint Unfold AtomSetImpl.disjoint : defs. *)
(* #[export] Hint Unfold PairScSetI.disjoint  : defs. *)

Module Export atoms_facts  := WFacts_fun_plus TaggedAtom      AtomSetImpl.
Module Export T_facts      := WFacts_fun_plus DecT      TSetI.
Module Export Sc_facts     := WFacts_fun_plus DecSc     ScSetI.
Module Export Tm_facts     := WFacts_fun_plus DecTm     TmSetI.
Module Export PairT_facts  := WFacts_fun_plus DecPairT  PairTSetI.
Module Export PairSc_facts := WFacts_fun_plus DecPairSc PairScSetI.

Theorem compose_rewr : forall (A B C : Type) (g : B -> C) (f : A -> B) (x : A),
    (compose g f) x = g (f x).
Proof. crush. Qed.
#[export] Hint Rewrite compose_rewr : core buildins.

Theorem flip_rewr : forall (A B C : Type) (f : A -> B -> C) (b:B) (a:A),
    flip f b a = f a b.
Proof. crush. Qed.
#[export] Hint Rewrite flip_rewr : core buildins.

(* Theorem const_rewr : forall (A B : Type) (a:A) (b:B), *)
(*     const a b = a. *)
(* Proof. crush. Qed. *)
(* #[export] Hint Rewrite const_rewr : core buildins. *)

(* Require Import Coq.Classes.Morphisms. *)
(* #[export] Hint Unfold Proper respectful impl flip : core. *)
(* #[export] Hint Constructors PreOrder Equivalence : core. *)
(* #[export] Hint Unfold Transitive : core. *)

(* Lemma if_fequals : forall (S:Set) (X:Type) (C : X -> S) (p1 p2:Prop) (b:sumbool p1 p2) (e1 e2:X), *)
(*     (if b then C e1 else C e2) = C (if b then e1 else e2). *)
(* Proof. intros. destruct b; crush. Qed. *)
(* #[export] Hint Rewrite if_fequals : core. *)

(* Notation "[ ]" := nil (format "[ ]"). *)
(* Notation "[ x ]" := (one x). *)
(* Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..)) : list_scope. *)


Ltac destr_union := atoms_facts.destr_union || T_facts.destr_union || Sc_facts.destr_union || Tm_facts.destr_union || PairT_facts.destr_union || PairSc_facts.destr_union.
Ltac disj_sub := simpl+ in *; (atoms_facts.disj_sub || T_facts.disj_sub || Sc_facts.disj_sub || Tm_facts.disj_sub || PairT_facts.disj_sub || PairSc_facts.disj_sub).
Ltac disj_sub_in H := simpl+ in *; (atoms_facts.disj_sub_in H || T_facts.disj_sub_in H || Sc_facts.disj_sub_in H || Tm_facts.disj_sub_in H || PairT_facts.disj_sub_in H || PairSc_facts.disj_sub_in H).

Ltac disj_union :=
  match goal with
    | |- ?L ∐ _ =>
        match type of L with
          atoms => apply atoms_facts.disj_union
        end
  end.
Ltac disj_union' :=
  match goal with
    | |- ?L ∐ _ =>
        match type of L with
          atoms => apply atoms_facts.disj_union'
        end
  end.

(*** Disjoint *)
Lemma in_disj : forall α L1 L2,
    L1 ∐ L2
  -> α ∈ L1
  -> α ∈ L2
  -> False.
Proof. unfold AtomSetImpl.disjoint. intros. fsetdec. Qed.
Corollary in_disj1 : forall α L1 L2,
    L1 ∐ L2
  -> α ∈ L1
  -> α ∉ L2.
Proof. unfold not. exact in_disj. Qed.
Corollary in_disj2 : forall α L1 L2,
    L1 ∐ L2
  -> α ∈ L2
  -> α ∉ L1.
Proof. unfold not. eauto using in_disj. Qed.

Ltac in_disj :=
  match goal with
    | [ |- ?α ∉ ?L ] =>
        match goal with
        | [ H : ?L' ∐ L |- _ ] => eapply (in_disj1 α L' L H); clfsetdec+
        | [ H : L ∐ ?L' |- _ ] => eapply (in_disj2 α L L' H); clfsetdec+
        end
  end.

Fact empty_disj : forall L,
    empty ∐ L.
Proof. fsetdec+. Qed.
#[export] Hint Resolve empty_disj : core.
Corollary empty_disj' : forall L1 L2,
    L1 ≡ empty
  -> L1 ∐ L2.
Proof. fsetdec+. Qed.
#[export] Hint Resolve empty_disj empty_disj' : core.



(*** Random *)
Theorem union_subset_iff : forall L1 L2 L3,
    L1 [<=] L3
  -> L2 [<=] L3
  -> L1 \u L2 [<=] L3.
Proof. clfsetdec. Qed.

Lemma empty_subset : forall L,
    (∅) ⊆ L.
Proof. fsetdec. Qed.
#[export] Hint Resolve empty_subset : core.

Lemma subset_notin : forall L1 L2 x,
    L1 ⊆ L2 ∪ {{x}}
  -> x ∉ L1
  -> L1 ⊆ L2.
Proof. fsetdec. Qed.

Fact notin_union_iff : forall α L1 L2,
    α ∉ L1
  -> α ∉ L2
  -> α ∉ L1 ∪ L2.
Proof. intros. fsetdec. Qed.

Fact decide_in : forall α L,
    α ∈ L \/ (~ α ∈ L).
Proof. fsetdec. Qed.
Ltac decide_in α L := forwards [IN|NIL]: decide_in α L.

Lemma weird_open_sets_thing : forall L1 L2 L3 x,
    L1 ⊆ L2
  -> L2 ⊆ (L3 ∪ {{x}})
  -> x ∉ L1 -> L1 ⊆ L3.
Proof. intros. fsetdec. Qed.


(* (*** Tagged atoms *) *)
(* Notation tag_of := TaggedAtom.tag_of. *)

(* Definition algorithmic (x:atom) := is_true (tag_of x). *)
(* Definition declarative (x:atom) := ~ is_true (tag_of x). *)

(* Definition L_algorithmic (L:vars) := forall α, α ∈ L -> algorithmic α. *)
(* Definition L_declarative (L:vars) := forall α, α ∈ L -> declarative α. *)

(* Fact algorithmic_neq_declarative : forall α, *)
(*     algorithmic α *)
(*   -> declarative α *)
(*   -> False. *)
(* Proof. introv ALG DEC. unfolds in ALG. unfolds in DEC. crush. Qed. *)

(* Fact L_algorithmic_declarative_disjoint : forall L1 L2, *)
(*     L_algorithmic L1 *)
(*   -> L_declarative L2 *)
(*   -> L1 ∐ L2. *)
(* Proof. *)
(*   introv ALG DEC. unfolds. unfolds. split. 2:fsetdec. intro. *)
(*   specializes ALG a. specializes ALG. fsetdec. *)
(*   specializes DEC a. specializes DEC. fsetdec. *)
(*   false. *)
(* Qed. *)

