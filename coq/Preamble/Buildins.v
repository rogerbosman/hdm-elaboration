Set Warnings "-notation-overridden".
Require Import Coq.Program.Basics.
Require Import Cpdtlib.CpdtTactics.


Theorem compose_rewr : forall (A B C : Type) (g : B -> C) (f : A -> B) (x : A),
    (compose g f) x = g (f x).
Proof. crush. Qed.
#[export] Hint Rewrite compose_rewr : core buildins.

Theorem flip_rewr : forall (A B C : Type) (f : A -> B -> C) (b:B) (a:A),
    flip f b a = f a b.
Proof. crush. Qed.
#[export] Hint Rewrite flip_rewr : core buildins.

Theorem const_rewr : forall (A B : Type) (a:A) (b:B),
    const a b = a.
Proof. crush. Qed.
#[export] Hint Rewrite const_rewr : core buildins.

Require Import Coq.Classes.Morphisms.
#[export] Hint Unfold Proper respectful impl flip : core.
#[export] Hint Constructors PreOrder Equivalence : core.
#[export] Hint Unfold Transitive : core.

Lemma if_fequals : forall (S:Set) (X:Type) (C : X -> S) (p1 p2:Prop) (b:sumbool p1 p2) (e1 e2:X),
    (if b then C e1 else C e2) = C (if b then e1 else e2).
Proof. intros. destruct b; crush. Qed.
#[export] Hint Rewrite if_fequals : core.
