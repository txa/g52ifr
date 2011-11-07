(* Copyright (c) 2011, Thorsten Altenkirch *)

(** %\chapter{%#<H0>#Lists%}%#</H0># *)
Section Lists.

(** Lists are the ubiqitous datastructure in functional programming, as you should know from Haskell.
    Given a set [A] we define [list A] to be the set of finite sequences of elements of [A]. E.g.
    the sequence [[1,2,3]] is an element of [list nat]. We can iterate this process and construct
    lists of lists, e.g. [[[1,2],[3]]] is an element of [list (list nat)]. However lists are uniform, that 
    is all elements need to have the same type so we cannot form a list like [[1,true]] or [[[1,2],3]].

    We are going to formally introduce lists using an _inductive definition_ which has a lot in 
    common with the definition of the natural numbers in the previous chapter. And indeed the theory of lists has a 
    lot in common with the theory of the natural number, so we can call this _list arithmetic_.
    *)
    
(** * Arithmetic for lists *)


Set Implicit Arguments.
Load Arith.

(** We define lists _inductively_. Given a set [A] a list over A is either
   the empty list [nil] or it is the result of putting an element [a] in fornt 
   of an already constructed list [l], we write [cons a l]. 
   [nil] and [cons] are _constructors_ of [list A], as [0] and [S] (successor) were
   constructors of [nat]. *)

Inductive list (A : Set) : Set :=
 | nil : list A
 | cons : A -> list A -> list A.

Implicit Arguments nil [A].

(** In functional programming [cons] is usually written as an infix operation. In Haskell this is
   [:] but since this symbol is used for member ship in Coq, we use [::] instead. Hence the meaning of [:] and [::] in Coq and Haskell are exactly swapped.*)

Infix "::" := cons (at level 60, right associativity).

(** As an example we can define the list [[2,3]] *)

Definition l23 : list nat
  := 2 :: 3 :: nil.

(** And by consing another [1] in front we obtain [[1,2,3]]. *)

Definition l123 : list nat
  := 1 :: l23.

(** We are going to prove some basic theorems about lists following the development 
   for natural numbers. There we showed that now successor of a natural number is [0]
   ([peano7]), here we show that no cons list is equal to the enmpty list.
*)

Theorem nil_cons : forall (A:Set)(x:A) (l:list A), 
  nil <> x :: l.
intros.
discriminate.
Qed.

(** The next peano axiom [peano8] expressed the injectivity of the successor.
   We have a similar statement for lists: if two cons lists are equal then
   their tail is equal. To prove this we define [tail] as we had define predecessor
   for numbers.  *)

Definition tail (A:Set)(l : list A) : list A :=
  match l with
  | nil => nil
  | cons a l => l
  end.

(** The proof follows exactly the one for [peano8]. *)

Theorem cons_injective : 
  forall (A : Set)(a b : A)(l m : list A),
    a :: l = b :: m -> l = m.
intros A a b l m h.
fold (tail (cons a l)).
rewrite h.
unfold tail.
reflexivity.
Qed.
  
(** However, unlike [S], [cons] has another argument, the head of the list. We can also show that it is
   injective in this argument, that is if two cons lists are eqaul thenthere head is equal.

   There is a slight problem in defining [head], we cannot (as in Haskell) define [head : list A -> A],
   because it could be that [A] is empty but there is still [nil : list A] and what should the head
   of this list be?

   To overcome this issue we define [head : A -> list A -> A] where the first argument is a _dummy argument_
   which is returned for the empty list.
*)

Definition head (A : Set)(x : A)(l : list A) : A :=
  match l with 
  | nil => x
  | a :: m => a
  end.

(** Once we have defined [head] the proof of injectivity is rather straightforward. *)

Theorem cons_injective' : 
  forall (A : Set)(a b : A)(l m : list A),
    a :: l = b :: m -> a = b.
intros A a b l m h.
fold (head a (a :: l)).
rewrite h.
unfold head.
reflexivity.
Qed.

(** As for natural numbers we have also an induction principle for lists: if a property
   is true for the empty list, and if it holds for a list [l] then it also holds
   for [cons a l] for any [a], then it holds for all lists. In Coq we use the same
   tactic [induction] to perform list indiuction. *)

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

(** * Lists form a monoid *)

(** Previously, we defined addition and multiplication for numbers. There is a
   very useful operation resembling addition for lists: append. We define 
   [app] by _structural recursion_ over lists.

   The idea is that to append a list to the empty list is just that list, and 
   to append a list to a cons list has the same head as the list and the tail 
   is obtained by recursively appending the list to the tail. *)

Fixpoint app (A : Set)(l m:list A) : list A :=
  match l with
  | nil => m
  | a :: l' => a :: (app l' m)
  end.

(** As in Haskell we use the inifx operation [++] to denote append. *)

Infix "++" := app (right associativity, at level 60).

(** As an example we construct the list [[2,3,1,2,3]] by appending 
   [[2,3]] and [[1,2,3]]. *)

Eval compute in (l23 ++ l123).

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

(** * Reverse *)

(** 

While there are many similarities between [nat] and [list A] there are important differences. Commutativity 
[l ++ m = m ++ l]
does not hold (what would be a counterexample?). Hence (list A,++,nil) is an example of a non-commutative monoid. Since we commutativity doesn't hold it makes sense to reverse a list (while it didn't make sense to reverse a number). 

To define reverse, we first define the operation [snoc] which adds an element at the end of a given list. This operation again is defined by primitive recursion.
*)

Fixpoint snoc (A:Set)
  (l : list A)(a : A) {struct l} : list A
  := match l with
     | nil => a :: nil
     | b :: m => b :: (snoc m a)
     end.

(** There is an alternative way to define [snoc] just by using [++]. Can you see how? *)

(** As an example we put [1] at the end of [[2,3]] *)

Eval compute in (snoc l23 1).

(** Using snoc it is easy to define [rev] by primitive recursion. 
   The reverse of an empty list is the empty list. To reverse a cons
   list, reverse its tail and then snoc the head to the end of the result.
*)

Fixpoint rev 
  (A:Set)(l : list A) : list A :=
  match l with
  | nil => nil
  | a :: l' => snoc (rev l') a 
  end.

(** This definition of [rev] is called _naive reverse_ and it is rather 
   inefficient. Can you see why? How can it be improved?
*)

(** Some examples. *)

Eval compute in rev l123.
Eval compute in rev (rev l123).

(** The 2nd example gives rise to a theorem about [rev],
   namely that to reverse twice is the identity ([rev (rev l) = l]).
   
   To prove it we first prove a lemma about [rev] and [snoc].
   How did we discover this lemma?
*)

Lemma revsnoc : forall (A:Set)(l:list A)(a : A),
  rev (snoc l a) = a :: (rev l).
intros A l a.

(** We proceed by induction over [l]. *)

induction l.
simpl.
reflexivity.
simpl.
rewrite IHl.
simpl.
reflexivity.
Qed.

(** And now we can prove the theorem. *)

Theorem revrev :  
  forall (A:Set)(l:list A),rev (rev l) = l.
intros A l.
induction l.
simpl.
reflexivity.
simpl.

(** And now it seems that [revsnoc] is exactly what we need.
   Lucky that we proved it already. *)

rewrite revsnoc.
rewrite IHl.
reflexivity.
Qed.

(** * Insertion sort *)

(**

  Our next example is sorting: we want to sort a given lists according 
  to an given order. E.g. the list

  [4 :: 2 :: 3 :: 1 :: nil]

  should be sorted into

  [1 :: 2 :: 3 :: 4 :: nil]

  We will implement and verify "insertion sort". To keep things simple 
  we will sort lists of natural numbers wrt to the <= order. First we
  implement a boolean function which compares two numbers:
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

(** We just assume that [leq] decided [<=]. I leave it as an 
   exercise to formally prove this, i.e. to replace the axioms
   by lemmas or theorems. *)

Axiom leq1 : forall m n : nat, leqb m n = true -> m <= n.
Axiom leq2 : forall m n : nat,  m <= n -> leqb m n = true.

(**
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

(**
   Now sort builds a sorted list from any list by inserting each 
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


(** Here is another assumption about [<=] I am not going to prove
   but leave as an exercise.
*)

Axiom total : forall m n : nat, m <= n \/ n <= m.

(** Our goal is to show that [insert] preserves sortedness, i.e.
    [Sorted l -> Sorted (insert n l)]. To prove this we need to
    lemmas. *)

(** The first one is useful in the case when the new element is not
   smaller than the current head. In this case we need to know that
   the head is smaller than the new element so that we can insert it
   later. *)
   
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

(** The other lemma is a little case analysis: the head of the result
   of [insert] is either the inserted element or the previous head. *)

Lemma insertSortCase : forall (n a : nat)(l : list nat),
  head a (insert n l) = n \/ head a (insert n l) = head a l.
intros n a l.

(** While we say [induction] we are not going to use the induction 
   hypothesis here. So we could have used [destruct] on lists here. *)

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

(** We are now able to prove the main lemma on [insert]. *)

Lemma insertSorted : forall (n : nat)(l : list nat),
  Sorted l -> Sorted (insert n l).
intros n l.

(** We prove the implication by induction. Why did we not do another [intro]? *)

induction l.

(** The case for the empty list is easy. *)

intro h.
simpl.
split.
split.
apply le_refl.

(** Now the cons case *)

intro h.
simpl.
simpl in h.
destruct h as [sl al].

(** We now analyze the result of the comparison. *)

case_eq (leqb n a).

(** First case [leqb n a = true], that is the element is put in front. *)

intro na.
simpl.
split.
split.
exact sl.
exact al.

(** Here we need the correctness of [leq] wrt [<=]. *)

apply leq1.
exact na.

(** Second case [leqb n a = false] so we insert [a] in the tail Here we need
   our lemmas. *)

intro na.
simpl.
split.
apply IHl.
exact sl.

(** Here we have to reason about the head of [insert n l], so 
   we use our lemma. *)

destruct (insertSortCase n a l) as [H1 | H2].

(** First case: it is the new element. *)

rewrite H1.
apply leqFalse.
exact na.

(** Second case: it is the old head. *)

rewrite H2.
exact al.
Qed.

(** using the previous lemma it is easy to prove our main theorem. *)

Theorem sortSorted : forall ms:list nat,Sorted (sort ms).
induction ms.

  (**  case ms=nil: *)

  simpl.
  split.

  (**  case a::ms *)

  simpl.
  apply insertSorted.
  exact IHms.
Qed.

(** Is this enough? No, we could have implemented a function with the 
   property sort_ok by always returning the empty list. Another 
   important property of a sorting function is that it returns a 
   permutation of the input. I leave this as an exercise.
*)



End Lists.

