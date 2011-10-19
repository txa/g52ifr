(* Copyright (c) 2011, Thorsten Altenkirch *)

(** %\chapter{%#<H0>#FiniteSets%}%#</H0># *)

Section finset.

(** * Bool *)

(** We define [bool : Set] as a finite set with two elements:
    [true : bool] and [false : bool] *)

Inductive bool : Set :=
  | true : bool
  | false : bool.

(** We define the function [negb : bool -> bool] (boolean negation) by pattern
    matching using the [match] construct. *)

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

(** This should be familiar from g51fun - in Haskell [match]
    is called [case]. Indeed Haskell offers a more convenient
    syntax for top-level pattern.

    We can evaluate the function using the slightly lengthy phrase
    [Eval compute in (...)]:
*)

Eval compute in (negb true).
(** The evaluator replaces
    
   [negb true]

   with

   [match true with
    | true => false
    | false => true
    end.]

    which in turn evaluates to

    [false]
*)
Eval compute in negb (negb true).
(** We know already that [negb true] evaluates to
    [false] hence [negb (negb true)] evaluates to
    [negb false] which in turn evaluates to [true].
*)

(** Other boolean functions can be defined just as easily: *)

Definition andb(b c:bool) : bool :=
  if b then c else false.

Definition orb (b c : bool) : bool :=
  if b then true else c.

(** It is maybe a good point to remark that Booleans are part
    of Coq's library and can be imported using

    [Require Import Coq.Bool.Bool.]

    which defines all the abive and much more and indeeds
    introduces the abbreviations && and || for andb and orb.
*)

(** We can now use predicate logic to show properties of 
    boolean functions. As a first example we show that the
    function [negb] is _idempotent_, that is 

    [forall b :bool, negb (negb b) = b]

    To prove this, the only additional thing we have to know
    is that we can analyze a boolean variable [b : bool] using
    [destruct b] which creates a case for [b = true] and one
    for [b = false]. 
*)

Lemma negb_idem : forall b :bool, negb (negb b) = b.
intro b.
destruct b.
(** Case for [b = true] *)
(** Our goal is negb (negb true) = true. 
    As we have already seen [negb (negb true)] evaluates
    to true. Hence this goal can be proven using [reflexivity].
    Indeed, we can make this visible by using [simpl].
*)
simpl.
reflexivity.
(** Case for [b = false] *)
(** This case is exactly the same as before. *)
simpl.
reflexivity.
Qed.

(** There is a shorter way to write this proof by using [;]
    instead of [,] after [destruct]. We can also omit the 
    [simpl] which we only use for cosmetic reasons. *)

Lemma negb_idem' : forall b :bool, negb (negb b) = b.
intro b.
destruct b;
  reflexivity.
Qed.

(** Indeed, proving equalities of boolean functions is very
    straightforward. All we need is to analyze all cases 
    and then use refl. For example to prove that [andb] is
    commutative, i.e.

    [forall x y : bool, andb x y = andb y x]
    
    (we use the abbrevation: [forall x y : A,...] is the 
    same as [forall x:A,forall y:A, ...].
*)

Lemma andb_comm : forall x y : bool, andb x y = andb y x.
intros x y.
destruct x;
  (destruct y; 
     reflexivity).
Qed.

(** We can also prove other properties of [bool] not directly
    related to the functions, for example, we know that every
    boolean is either true or false. That is 
    
    [forall b : bool, b = true \/ b = false]

    This is easy to prove:
*)

Lemma true_or_false : forall b : bool, b = true \/ b = false.
intro b.
destruct b.
(** b = true *)
left.
reflexivity.
(** b = false *)
right.
reflexivity.
Qed.

(** Next we want to prove something which doesn't involve any
    quantifiers, namely

    [~ (true = false) ]

    This is not so easy, we need a little trick. We need to embed
    [bool] into [Prop], mapping [true] to [True] and [false] to 
    [False]. This is achieved via the function Istrue:*)

Definition Istrue (b : bool) : Prop := 
  match b with
  | true => True
  | false => False
  end.

Lemma diff_true_false : 
      ~ (true = false).
intro h.
(** We now need to use a new tactic to replace
    [False] by [IsTrue False]. This is possible
    because [IsTrue False] evaluates to [false].
    We are using [fold] which is the inverse to 
    [unfold] which we have seen earlier. *)
fold (Istrue false).
(** Now we can simply apply the equation [h] backwards. *)
rewrite<- h.
(** Now by unfolding we can replace [Istrue true] by [True] *)
unfold Istrue.
(** Which is easy to prove.*)
split.
Qed.

