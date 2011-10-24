(* Copyright (c) 2011, Thorsten Altenkirch *)

(** %\chapter{%#<H0>#Bool%}%#</H0># *)

Section Bool.

(** * Defining bool and operations *)

(** We define [bool : Set] as a finite set with two elements:
    [true : bool] and [false : bool]. In set theoretic notation
    we would write [bool] = { [true] , [false] }. 
*)

(*
In Coq we write: 
[
Inductive bool : Set :=
  | true : bool
  | false: bool.
]
*)

(** The function [negb : bool -> bool] (boolean negation) can be defined by pattern
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

(** The Coq prelude also defines the infix operators
   && and || for andb and orb respectively, with && having
   higher precedence than ||. Note however, that you cannot
   use ! (for negb) since this is used for other purposes in Coq.
*)

(** * Reasoning about Bool *)

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

Lemma true_or_false : forall b : bool, 
       b = true \/ b = false.
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

(** Actually there is a tactic [discriminate] which implements 
    this proof and which allows us to prove directly that any 
    two different constructors (like [true] and [false]) are
    different. We shall use [discriminate] in future.
*)

(** * Reflection *)

(** We notice that there is a logical operator [/\] which acts
    on [Prop] and a boolean operator [andb] (or [&&]) which acts
    on [bool]. How are the two related?

    We can use [/\] to specify [andb], namely we say that
    [andb x y = true] is equivalent to [x = true] and [y = true]. 
    That is we prove:

*)

Lemma and_ok : forall x y : bool, 
  andb x y = true <-> x = true /\ y = true.
intros x y.
split.

(** [->] *)

destruct x.

(** x=true*)

intro h.
split.
reflexivity.
simpl in h.
exact h.

(** Why did the last step work? *)

(** x = false *)

intro h.
simpl in h.
discriminate h.

(** [<-] *)

intro h.
destruct h as [hx hy].
rewrite hx.
exact hy.

Qed.

End Bool.







