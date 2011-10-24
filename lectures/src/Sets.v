(* Copyright (c) 2011, Thorsten Altenkirch *)

(** %\chapter{%#<H0>#How to make sets%}%#</H0># *)

Section Sets.

(** Some magic incantations... *)
Open Scope type_scope.
Set Implicit Arguments.

(** * Finite Sets *)

(** As we have defined [bool] we can define other finite sets 
    just by enumerating the elements.
    
    Im Mathematics (and conventional Set Theory), we just write
    C = { c1, c2 , .. , cn } for a finite set.

    In Coq we write
    [Inductive C : Set := 
    | c1 : C
    | c2 : C
    ...
    | cn : Set. ]

    As a special example we define the empty set:
*)
    
Inductive empty_set : Set := .

(** As an example for finite sets, we consider the game of chess.
    We need to define the colours, the different type of pieces,
    and the coordinates. *)

Inductive Colour : Set :=
  | white: Colour
  | black : Colour.

Inductive Rank : Set :=
  | pawn : Rank
  | rook : Rank
  | knight : Rank
  | bishop : Rank
  | queen : Rank
  | king : Rank.

Inductive XCoord : Set :=
  | xa : XCoord
  | xb : XCoord
  | xc : XCoord
  | xd : XCoord
  | xe : XCoord
  | xf : XCoord
  | xg : XCoord
  | xh : XCoord.

Inductive YCoord : Set :=
  | y1 : YCoord
  | y2 : YCoord
  | y3 : YCoord
  | y4 : YCoord
  | y5 : YCoord
  | y6 : YCoord
  | y7 : YCoord
  | y8 : YCoord.

(** In practice it is not such a good idea to use different
    sets for the x and y coordinates. We use this here for 
    illustration and it does reflect the chess notation
    like e2 - e4 for moving the pawn in front of the king.
*)

(** We can define operations on finite sets using the [match]
    construct we have already seen for book. As an example
    we define the operation 
    [oneUp : YCoord -> YCoord]
    which increases the y coordinates by 1. We have to decide
    what to do when we reach the 8th row. Here we just get
    stuck. There are better solutions we will see later.
*)

Definition oneUp (y : YCoord) : YCoord :=
  match y with
  | y1 => y2
  | y2 => y3
  | y3 => y4
  | y4 => y5
  | y5 => y6
  | y6 => y7
  | y7 => y8
  | y8 => y8
  end.

(** * Products *)

(** Given to sets [A B : Set] we define a new set 
    [A * B : Set] which is called the _product_ of 
    [A] and [B]. It is the set of pairs [(a,b)] where
    [a : A] and [b : B]. In Coq we define
*)

Inductive prod(A B : Set) : Set :=
  | pair : A -> B -> prod A B.


Notation "A * B" := (prod A B) : type_scope.
Notation "( a , b )" := (pair a b).


(** As an example we define the set of chess pieces
    and coordinates: *)

Definition Piece : Set := Colour * Rank.

Definition Coord : Set := XCoord * YCoord.

(** And for illustration construct some elements: *)

Definition blackKnight : Piece := (black , knight).

Definition e2 : Coord := (xe , y2).

(** On Products we have some generic operations called
    _projections_ which extract the components of a product.
*)

(* Why can't I use A*B here ? 
Definition fst(A B : Set)(p : A * B) : A :=
   match p with
   | (a , b) => a
   end. *)

Definition fst(A B : Set)(p : A * B) : A :=
   match p with
   | (a , b) => a
   end.

Definition snd(A B : Set)(p : A * B) : B :=
   match p with
   | pair a b => b
   end.

(** A general theorem about products is that if we take
    apart an element using projections and then put it 
    back together again we get the same element. In predicate
    logic this is:

    [forall p : A * B, (fst p , snd p) = p]

    This is called _surjective pairing_. In the actual
    statement in Coq we also have to quantify over the 
    sets involved (which technically gets us into the realm
    of higher order logic - but we shall ignore this).
*)

Lemma surjective_pairing : forall A B : Set, 
  forall p : prod A B, (fst p , snd p) = p.
intros A B p.
(** The actual proof is rather easy.
    All that we need to know is that we can take apart 
    a product the same way as we have taken apart conjunctions.
*)
destruct p as [a b].
(** Can you simplify this goal in your head?
    Yes simpl will do the job but why?
*)
reflexivity.
Qed.

(** Question: If |A| and |B| are finite sets with |m| and
   |n| elements respectively, how many elements are in 
   |A * B|?
*)

(** * Disjoint union *)

(** Given to sets [A B : Set] we define a new set 
    [A + B : Set] which is called the _disjoint union_ of 
    [A] and [B]. Elements of [A + B] are either [inl a]
    where [a : A] or [inr b] where [b : B]. Here [inl]
    stands for "inject left" and [inr] stands for 
    "inject right".

    It is important not to confuse [+] with the union of 
    sets. The disjoint union of [bool] with [bool] has 4 elements
    because [inl true] is different from [inr true] while 
    in the union of bool with bool there are only 2 elements since
    there is only one copy of [true]. Actually, the union of
    sets does not exist in Coq.
  
    We define [+] in Coq:
*)
Inductive sum (A B:Set) : Set :=
  | inl : A -> sum A B
  | inr : B -> sum A B.

Notation "x + y" := (sum x y) : type_scope.

(** We have to tell Coq to figure out the sets itself. *)
Implicit Arguments inl [A B].
Implicit Arguments inr [A B].

(** As an example we use disjoint union to define the set
    field which can either be a piece or empty. The second
    case is represented by a set with just one element called
    [Empty] which has just one element [empty].
*)

Inductive Empty : Set :=
  | empty : Empty.

Definition Field : Set := Piece + Empty.

(** some examples *)

Definition blackKnightHere : Field := inl blackKnight.

Definition emptyField : Field := inr empty.

(** As an example of a defined operation we define [swap]
    which maps elements of [A + B] to [B + A] by mapping
    [inl] to [inr] and vice versa. *)

Definition swap(A B : Set)(x : A + B) : B + A :=
  match x with 
  | inl a => inr a
  | inr b => inl b
  end.

(** The same question as for products: If [A] has 
   [m] elements and [B] has [n] elements, how many 
   elements are in [A + B}? 
*)

(** Disjoint unions are sometimes called _coproducts_
    because there are in a sense the mirror image 
    of products. To make this precise we need the language
    of category theory, which is beyond this course.
    However, if you are curious look up Category Theory
    on wikipedia.
*)

(** * Function sets *)
                
(** Given to sets [A B : Set] we define a new set 
    [A -> B : Set], the set of functions form [A] 
    to [B]. We have already seen one way to define
    functions, whenever we have defined an operation
    we have actually defined a function. However, as
    you have already seen in Haskell, we can define
    functions directly using lambda abstraction. The
    syntax is [fun (x : A) => b] where [b] is an expression
    in [B] which may refer to [x].

    As an example instead of defining [negb] as an
    operation we could also have used [fun]:
*)

Definition negb : bool -> bool
  := fun (b : bool) => match b with
                       | true => false
                       | false => true
                       end.

(** The [fun] notation enables us to define 
    _higher order functions_, i.e. functions which 
    take functions as arguments. An example is the 
    function [isConst] which determines wether a given
    function [f : bool -> bool] is constant. 

Definition isConst 
*) 