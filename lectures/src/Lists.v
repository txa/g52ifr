(* Copyright (c) 2011, Thorsten Altenkirch *)

(** %\chapter{%#<H0>#Lists%}%#</H0># *)
Section Lists.

(** Lists are the ubiqitous datastructure in functional programming.*)
    
(** * Arithmetic for lists *)
Set Implicit Arguments.
Load Arith.

Inductive list (A : Set) : Set :=
 | nil : list A
 | cons : A -> list A -> list A.

Implicit Arguments nil [A].

Infix "::" := cons (at level 60, right associativity).

Definition l23 : list nat
  := 2 :: 3 :: nil.

Definition l123 : list nat
  := 1 :: l23.

Theorem nil_cons : forall (A:Set)(x:A) (l:list A), 
  nil <> x :: l.
intros.
discriminate.
Qed.

Definition tail (A:Set)(l : list A) : list A :=
  match l with
  | nil => nil
  | cons a l => l
  end.

Theorem cons_injective : 
  forall (A : Set)(a b : A)(l m : list A),
    a :: l = b :: m -> l = m.
intros A a b l m h.
fold (tail (cons a l)).
rewrite h.
unfold tail.
reflexivity.
Qed.
  
Definition head (A : Set)(x : A)(l : list A) : A :=
  match l with 
  | nil => x
  | a :: m => a
  end.

Theorem cons_injective' : 
  forall (A : Set)(a b : A)(l m : list A),
    a :: l = b :: m -> a = b.
intros A a b l m h.
fold (head a (a :: l)).
rewrite h.
unfold head.
reflexivity.
Qed.

Theorem ind_list : forall (A : Set)(P : list A -> Prop),
  P nil
  -> (forall (a:A)(l : list A), P l -> P (a :: l))
  -> forall l : list A, P l.
intros A P hnil hcons l.
induction l.
exact hnil.
apply hcons.
exact IHl.
Qed.

(** Append and other operations. *)

Fixpoint app (A : Set)(l m:list A) : list A :=
  match l with
  | nil => m
  | a :: l' => a :: (app l' m)
  end.

Infix "++" := app (right associativity, at level 60).

(** We show that [list A] with [++] and [nil] forms a monoid. Indeed the proofs are basically the same as for ([nat],[+],0). *)

Theorem app_nil_l : forall (A : Set)(l : list A),
  nil ++ l = l.
intros A l.
reflexivity.
Qed.

Theorem app_l_nil :  forall (A : Set)(l : list A),
  l ++ nil = l.
intros A l.
induction l.
reflexivity.
simpl.
rewrite IHl.
reflexivity.
Qed.

Theorem assoc_app : forall (A : Set)(l m n : list A),
  l ++ (m ++ n) = (l ++ m) ++ n.
intros A l m n.
induction l.
reflexivity.
simpl.
rewrite IHl.
reflexivity.
Qed.

(** 

While there are many similarities between [nat] and [list A] there are important differences. Commutativity 
[forall (A : Set)(l m : list A),
   l ++ m = m ++ l]
does not hold. Hence (list A,++,nil) is an example of a non-commutative monoid. Since we commutativity doesn't hold it makes sense to reverse a list. 

To define reverse, we first define the operation [snoc] which adds an element at the end of a given list.
*)

Fixpoint snoc (A:Set)
  (l : list A)(a : A) {struct l} : list A
  := match l with
     | nil => a :: nil
     | b :: m => b :: (snoc m a)
     end.

Fixpoint rev 
  (A:Set)(l : list A) : list A :=
  match l with
  | nil => nil
  | a :: l' => snoc (rev l') a 
  end.

Eval compute in rev l123.
Eval compute in rev (rev l123).

Lemma revsnoc : forall (A:Set)(l:list A)(a : A),
  rev (snoc l a) = a :: (rev l).
induction l.
simpl.
reflexivity.
intro b.
simpl.
rewrite IHl.
simpl.
reflexivity.
Qed.

Theorem revrev :  
  forall (A:Set)(l:list A),rev (rev l) = l.
induction l.
simpl.
reflexivity.
simpl.
rewrite revsnoc.
rewrite IHl.
reflexivity.
Qed.

(* 

  insertion sort

  Our next example is sorting: we want to sort a given lists according 
  to an given order. E.g. the list

  4 :: 2 :: 3 :: 1 :: nil

  should be sorted into

  1 :: 2 :: 3 :: 4 :: nil

  We will implement and verify "insertion sort". To keep things simple 
  we will sort lists of natural numbers wrt to the <= order. First we
  implement a boolean function which comapres two numbers:
*)

Fixpoint leqb (m n : nat) {struct m} : bool :=
  match m with
  | 0 => true
  | S m => match n with 
           | 0 => false
           | S n => leqb m n
           end
  end.

Eval compute in leqb 3 4.
Eval compute in leqb 4 3.

Notation "m <= n" := (leq m n).

Axiom leq1 : forall m n : nat, leqb m n = true -> m <= n.
Axiom leq2 : forall m n : nat,  m <= n -> leqb m n = true.

(*
   The main function of insertion sort is the function insert 
   which inserts a new element into an already sorted list:
*)

Fixpoint insert (n:nat)(ms : list nat) {struct ms} : list nat :=
  match ms with
  | nil => n::nil
  | m::ms' => if leqb n m
              then n::ms
              else m::(insert n ms')
  end.

Eval compute in insert 3 (1::2::4::nil).

(* Now sort builds a sorted list from any list by inserting each 
   element into the empty list.
*)

Fixpoint sort (ms : list nat) : list nat :=
  match ms with
  | nil => nil
  | m::ms' => insert m (sort ms')
  end.

Eval compute in sort (4::2::3::1::nil).

(* However, how do we know that sort will work for all lists?
   We are going to verify sort. First we have to define what 
   we mean by sorted. *)

Fixpoint Sorted (l : list nat) : Prop :=
  match l with
  | nil => True
  | a :: m => Sorted m /\ a <= head a m
  end.

Axiom total : forall m n : nat, m <= n \/ n <= m.

Lemma leqFalse : forall m n : nat, leqb m n = false -> n <= m.
intros m n h.
destruct (total m n) as [mn | nm].
assert (mnt : leqb m n = true).
apply leq2.
exact mn.
rewrite h in mnt.
discriminate mnt.
exact nm.
Qed.

Lemma insertSortCase : forall (n a : nat)(l : list nat),
  head a (insert n l) = n \/ head a (insert n l) = head a l.
intros n a l.
induction l.
left.
simpl.
reflexivity.
simpl.
destruct (leqb n a0).
left.
simpl.
reflexivity.
right.
simpl.
reflexivity.
Qed.

Lemma insertSorted : forall (n : nat)(l : list nat),
  Sorted l -> Sorted (insert n l).
intros n l.
induction l.
intro h.
simpl.
split.
split.
apply le_refl.
intro h.
simpl.
simpl in h.
destruct h as [sl al].
case_eq (leqb n a).
intro na.
simpl.
split.
split.
exact sl.
exact al.
apply leq1.
exact na.
intro na.
simpl.
split.
apply IHl.
exact sl.
destruct (insertSortCase n a l) as [H1 | H2].
rewrite H1.
apply leqFalse.
exact na.
rewrite H2.
exact al.
Qed.

(* using the previous lemma it is easy to prove our main theorem. *)
Theorem sortSorted : forall ms:list nat,Sorted (sort ms).
induction ms.
  (* case ms=nil: *)
  simpl.
  split.
  (* case a::ms *)
  simpl.
  apply insertSorted.
  exact IHms.
Qed.

(* Is this enough? No, we copuld have implemented a function with the 
   property sort_ok by always returning the empty list. Another 
   important property of a sorting function is that it returns a 
   permutation of the input. We define what a permutation is. Again to 
   simplify or discussion we only do this for list nat. 
*)



End Lists.

