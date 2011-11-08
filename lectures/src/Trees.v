(* Copyright (c) 2011, Thorsten Altenkirch *)

(** %\chapter{%#<H0>#Trees%}%#</H0># *)
Section Trees.

Set Implicit Arguments.

Load Lists.
Infix "::" := cons (at level 60, right associativity).
Infix "++" := app (right associativity, at level 60).
Implicit Arguments nil [A].
Notation "m <= n" := (leq m n).

Inductive Tree (A : Set) : Set :=
  | leaf : Tree A
  | node : Tree A -> A -> Tree A -> Tree A.

Implicit Arguments leaf [A].

Fixpoint root (A : Set)(default : A)(t : Tree A) : A :=
  match t with 
  | leaf => default
  | node l a r => a
  end.

Fixpoint nleT (n : nat)(t : tree nat)

Fixpoint SortedTree (t : Tree nat) : Prop :=
  match t with
  | leaf => True
  | node l a r => root a l <= a /\ a <= root a r 
               /\ SortedTree l /\ SortedTree r
  end.

Fixpoint insertT (n : nat)(t : Tree nat) : Tree nat :=
  match t with
  | leaf => node leaf n leaf
  | node l m r => if leqb n m 
                  then node (insertT n l) m r
                  else node l m (insertT n r)
  end.

Fixpoint buildTree (l : list nat) : Tree nat :=
  match l with
  | nil => leaf
  | n :: ns => insertT n (buildTree ns)
  end.

Fixpoint destructTree (t : Tree nat) : list nat :=
  match t with
  | leaf => nil
  | node l m r => destructTree l ++ m :: destructTree r
  end.

Fixpoint tsort (l : list nat) : list nat :=
  destructTree (buildTree l).

Eval compute in tsort (4::2::3::1::nil).

Axiom CaseInsertT : forall (t : Tree nat)(n d : nat),
  root d (insertT n t) = n \/ root d (insertT n t) = root d t.

Lemma insertTSorted : forall (t : Tree nat)(n : nat),
  SortedTree t -> SortedTree (insertT n t).
intros t n.
induction t.
intro h.
simpl.
split.
apply le_refl.
split.
apply le_refl.
split. split. split.
intro h.
simpl.
simpl in h.
destruct h as [t1a h].
destruct h as [at2 h].
destruct h as [st1 st2].
case_eq (leqb n a).
intro na.
simpl.
split.
destruct (CaseInsertT t1 n a) as [h1 | h2].
rewrite h1.
apply leq1.
exact na.
rewrite h2.
exact t1a.
split.
exact at2.
split.
apply IHt1.
exact st1.
exact st2.
intro an.
simpl.
split.
exact t1a.
split.
destruct (CaseInsertT t2 n a) as [h1 | h2].
rewrite h1.
apply leqFalse.
exact an.
rewrite h2.
exact at2.
split.
exact st1.
apply IHt2.
exact st2.
Qed.

Lemma buildTreeSorted : forall ns : list nat, SortedTree (buildTree ns).
intro ns.
induction ns.
simpl.
split.
simpl.
apply insertTSorted.
exact IHns.
Qed.

Lemma destructTreeSorted : forall ns : Tree nat, 
  SortedTree ns -> Sorted (destructTree ns).
intro ns.
induction ns.
intro h.
simpl.
split.
intro h.
simpl.
simpl in h.



End Trees.

