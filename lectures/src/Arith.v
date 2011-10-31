(* Copyright (c) 2011, Thorsten Altenkirch *)

(** %\chapter{%#<H0>#Peano Arithmetic%}%#</H0># *)

Section Arith.

(** * The natural numbers *)

(** Guiseppe Peano defined the natural numbers as given by [0 : nat]
    and if [n] is a natural number then [S n : nat] is a natural number
    called the successor of [n]. Given this we can construct all the 
    natural numbers, e.g.
    - 1 = S 0
    - 2 = S 1 = S (S 0)
    - 3 = S 2 = S (S (S 0))
    Moreover these are all natural numbers (we say they are defined _inductively_).

    Peano went on to represent the fundamental properties of the natural 
    numbers as some axioms. Some of the axioms express general properties of 
    equality, which we have already seen. But the following three are 
    specific to the natural numbers. Indeed, they are provable propositions
    in Coq:

    - Axiom 7 : 0 is not the successor of any number.
      [forall n:nat, S n <> 0]
    - Axiom 8 : If two numbers have the same successor, then they are equal.
      [forall m n:nat, S m = S n -> m = n ]
    - Axiom 9 : If any property holds for 0, and is closed under successor, 
      then it holds 
      for all natural numbers (principle of induction).
      [forall P : nat -> Prop, P 0 
                      -> (forall m : nat, P m -> P (S m))
                      -> forall n : nat, P n]

    For illustration we are going to prove these principles:
*)
Lemma peano7 : forall n:nat, S n <> 0.
intro n.
intro h.
(** This is basically the same problem as proving [true <> false], we
    could apply the same technique here. To avoid repetetion we just
    use the [discriminate] tactic.
*)
discriminate h.
Qed.
  
(** To prove the next axiom, it is useful to define the inverse to
    S, the predecessor function P. We arbitrarily decide that the 
    predecessor of 0 is 0. *)

Definition P (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n => n
  end.
  
Lemma peano8 : forall m n:nat, S m = S n -> m = n.
intros m n h.
(** By folding with [P] we can change the current goal so that we can
    apply our hypothesis. *)
fold (P (S m)).
rewrite h.
(** And now we just have to unfold. simpl would have done the job too. *)
unfold P.
reflexivity.
Qed.

(** The 8th axiom says that the successor function is injective. 
    Can we prove the other direction too? 
    [forall m n:nat, m = n -> S m = S n]
    Does this tell us anything new
    about the successor function? *)

(** The proof of the induction axiom is rather boring. It just uses a tactic
    which is called [induction]... *)

Lemma peano9 : forall P : nat -> Prop, P 0 
                      -> (forall m : nat, P m -> P (S m))
                      -> forall n : nat, P n.
intros P h0 hS n.
induction n.
exact h0.
apply hS.
exact IHn.
Qed.

(** * Addition and multiplication *)

(** Peano defined the operations addition and multiplication.
    These are actually examples of functions defined by _primitive
    recursion_ a general scheme which can be used to define many 
    other functions. A function is definable by primitive recursion
    if we can give a case for 0 and reduce the computation for the
    value at [S n] to the value at [n]. In Coq we have to use the 
    keyword [fixpoint] instead of [definition] and we have to indicate
    on which argument we want to do primitive recursion.
*)

(** The idea is that we can define addition like this:
   - to add 0 to a number is just this number,
   - to add one more that n to a number is one more than adding
     n to the number.
*)

Fixpoint add (m n : nat) {struct m} : nat :=
  match m with
  | 0 => n
  | S m => S (add m n)
  end.

Eval compute in (add 2 3).

(** In the Coq library addition is defined using the usual infix
    notation [+]. *)

(** To define multiplication we use primitive recursion again. This time
    the idea is the following.
    - multiplying 0 with a number is just 0.
    - multiplying one more than n with a number is obtained by adding 
      the number to multiplying n with the number.
*)

Fixpoint mult (m n : nat) {struct m} : nat :=
  match m with
  | 0 => 0
  | S m => add n (mult m n)
  end.

Eval compute in (mult 2 3).

(** In the Coq library addition is defined using the usual infix
    notation [+] and [*] with the usual rules of precedence.
    From now on we shall use the library versions which are defined
    exactly in the same way as we have defined [add] and [mult] *)

(** * Algebraic properties *)

(** Addition and multiplication satisfy a number of important equations:
   - 0 is a neutral element for addition
     [0 + m = m] and [m + 0 = m]
   - Addition is associative.
     [m + (n + l) = (m + l) + n]
   - Addition is commutative.
     [m + n = n + m]
   - 1 is a neutral element for multiplication
     [1 * m = m] and [m * 1 = m]
   - Multiplication is associative.
     [m * (n * l) = (m * n) * l]
   - Multiplication is commutative.
     [m * n = n * m]
   - 0 is a null for multiplication.
     [m * 0 = 0] and [0 * m = 0]
   - Addition distributes over multiplication.
     [m * (n + l) = m * n + m * l]
     and
     [(m + n) * l = m * l + n * l]

   In the language of universal algebra, we say that 
   - (+,0) is a _commutative monoid_,
     because 0 is neutral, [+] is associative and commutative.
   - ( *,1) is a commutative monoid,
     because 1 is neutral, [*] is associative and commutative.
   - (+,0,*,1) is a _commutative semiring_ because
     (+,0) and ( *,1) are commutative monoids and
     [0] is a zero for multiplication and 
     addition distributes over multiplication. 

   We are going to prove that (+,0) is a commutative monoid 
   and leave the remaining properties as an exercise. *)
 
Lemma plus_O_n : forall n:nat, n = 0 + n.
(** This property is very easy to prove.
    Can you see why?
*)
intro n.
reflexivity.
Qed.

Lemma plus_n_O : forall n:nat, n = n + 0.
intro n.
(** This one cannot be proven by reflexivity.
    So we have to use induction. *)
induction n.
(** n = 0 
    This is easy. *)
simpl.
reflexivity.
(** We can simplify [S n + 0] using the definition of [+] *)
simpl.
rewrite<- IHn.
reflexivity.
Qed.


Lemma plus_assoc : forall (l m n:nat),l + (m + n) = (l + m) + n.
intros l m n.
(** There seems to be quite a choice what to do induction over:
    [l],[m],[n] but only one of them works. Why? *)
induction l.
simpl.
reflexivity.
simpl.
rewrite IHl.
reflexivity.
Qed.

(** To prove commutativity we first prove a lemma 
    we know already that [0 + m = m = m + 0]
    but what about [S m + n = S (m + n) = m + S n] ?
*)

Lemma plus_n_Sm : forall n m : nat, S (m + n) = m + S n.
intros.
induction m.
simpl.
reflexivity.
simpl.
rewrite IHm.
reflexivity.
Qed.

(** We are now ready to prove commutativity. *)

Lemma plus_comm : forall n m:nat, n + m = m + n.
intros.
induction n.
simpl.
apply plus_n_O.
simpl.
rewrite IHn.
apply plus_n_Sm.
Qed.

(** * Ordering the numbers *)

(** We define the relation [<=] on natural numbers by saying 
    that [m <= n] holds if there is a number [k] such that 
    [m = k + n]. *)

Definition leq (m n : nat) : Prop :=
  exists k : nat, m = k + n.

Notation "m <= n" := (leq m n).

(** We verify some basic properties of [<=]:
    - [<=] is reflexive.
      [forall n:nat, n <= n]
    - [<=] is transitive.
      [forall l m n:nat, l <= m -> m <= n -> l <= n]
    - [<=] is antisymmetric.
      [forall l m : nat, l <= m -> m <= l -> m = l]
*)

(** * Decidable properties *)

End Arith.