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

Fixpoint EverywhereT (A : Set)(P : A -> Prop)(t : Tree A) {struct t} 
  : Prop :=
  match t with
  | leaf => True
  | node l a r => EverywhereT P l /\ P a /\ EverywhereT P r
  end.

Fixpoint SortedTree (t : Tree nat) : Prop :=
  match t with
  | leaf => True
  | node l a r => EverywhereT (fun x => x <= a) l
               /\ EverywhereT (fun x => a <= x) r
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

Lemma insertTeverywhere : 
  forall (P : nat -> Prop)(n : nat)(t : Tree nat),
    P n -> EverywhereT P t -> EverywhereT P (insertT n t).
intros P n t p.
induction t.
intro h.
simpl.
split. split. split. exact p. split.
intro h.
simpl in h.
destruct h as [et1 h]. destruct h as [pa et2].
simpl.
destruct (leqb n a).
simpl.
split.
apply IHt1.
exact et1.
split.
exact pa.
exact et2.
simpl.
split.
exact et1.
split.
exact pa.
apply IHt2.
exact et2.
Qed.


Lemma insertTSorted : forall (t : Tree nat)(n : nat),
  SortedTree t -> SortedTree (insertT n t).
intros t n.
induction t.
intro h.
simpl.
split. split. split. split. split. split. split.
intro h.
simpl in h.
destruct h as [et1 h]. destruct h as [et2 h].
destruct h as [st1 st2].
simpl.
case_eq (leqb n a).
intro na.
simpl.
split.
apply insertTeverywhere.
apply leq1. exact na.
exact et1.
split. exact et2.
split. apply IHt1. exact st1.
exact st2.
intro an.
simpl. split. apply et1.
split. apply insertTeverywhere.
apply leqFalse. exact an.
exact et2.
split. exact st1. apply IHt2. exact st2.
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

Fixpoint EverywhereL (A : Set)(P : A -> Prop)(l : list A) {struct l}
  : Prop :=
  match l with
  | nil => True
  | a :: l => P a /\ EverywhereL P l
  end.

Axiom everywhereDestruct : 
  forall (P : nat -> Prop)(t : Tree nat),
    EverywhereT P t -> EverywhereL P (destructTree t).

Lemma sortAppLem : forall (l1 l2 : list nat)(n : nat),
  Sorted l1 -> Sorted (n::l2) -> EverywhereL (fun x => x <= n) l1
  -> Sorted (l1 ++ n :: l2).
induction l1.
intros. exact H0.
intros.
simpl.
simpl in H1.
destruct H1 as [an el1].
split.
apply IHl1.
simpl in H.
destruct H as [sl1 al1].
exact sl1.
exact H0.
exact el1.



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

