(* Copyright (c) 2011, Thorsten Altenkirch *)

(** %\chapter{%#<H0>#How to make sets%}%#</H0># *)

Section Sets.

(** Some magic incantations... *)

Open Scope type_scope.
Set Implicit Arguments.
Implicit Arguments inl [A B].
Implicit Arguments inr [A B].


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
    | cn : C. ]

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
    stuck. 
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

(** Given two sets [A B : Set] we define a new set 
    [A * B : Set] which is called the _product_ of 
    [A] and [B]. It is the set of pairs [(a,b)] where
    [a : A] and [b : B].
*)

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

Definition fst(A B : Set)(p : A * B) : A :=
   match p with
   | (a , b) => a
   end.


Definition snd(A B : Set)(p : A * B) : B :=
   match p with
   | (a , b) => b
   end.

Eval compute in fst blackKnight.
Eval compute in snd blackKnight.

Eval compute in (fst blackKnight,snd blackKnight).

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
simpl.
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

(** Given two sets [A B : Set] we define a new set 
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
    sets does not exist in Coq. *)


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
   elements are in [A + B]? 
*)

(** Disjoint unions are sometimes called _coproducts_
    because there are in a sense the mirror image 
    of products. To make this precise we need the language
    of category theory, which is beyond this course.
    However, if you are curious look up Category Theory
    on wikipedia.
*)

(** * Function sets *)
                
(** Given two sets [A B : Set] we define a new set 
    [A -> B : Set], the set of functions form [A] 
    to [B]. We have already seen one way to define
    functions, whenever we have defined an operation
    we have actually defined a function. However, as
    you have already seen in Haskell, we can define
    functions directly using lambda abstraction. The
    syntax is [fun x => b] where [b] is an expression
    in [B] which may refer to [x : A].*)

(** In the case of our chess example we can use functions to define
   a chess board as a function form [Coord] to [Field], 
   this function would give us the content of a field for 
   any coordinate. *)

Definition Board : Set := Coord -> Field.

(** A particular simple example is the empty board: *)

Definition EmptyBoard : Board := fun x => emptyField.

(** I leave it as an exercise to construct the initial board for a
chess game. *)


(**
    As another example instead of defining [negb] as an
    operation we could also have used [fun]:
*)

Definition negb' : bool -> bool
  := fun (b : bool) => match b with
                       | true => false
                       | false => true
                       end.

(** Using [fun] is especially useful when we are dealing with _higher
   order functions_, i.e. function which take functions as
   arguments. As an example let us define the function [isConst] which
   determines wether a given function [f : bool -> bool] is
   constant. *)

Open Scope bool_scope.

Definition isConst (f : bool -> bool) : bool :=
  (f true) && (f false) || negb (f true) && negb (f false).

(** What will Coq answer when asked to evaluate the terms below. 
    In three cases we are using [fun] to construct the argument.
    Could we have done this in the 1st case as well?
 *)

Eval compute in isConst negb.
Eval compute in isConst (fun x => false).
Eval compute in isConst (fun x => true).
Eval compute in isConst (fun x => x).

(** Are there any other cases to consider ? *)

(** In general, if [A],[B] are finite sets with [m] and [n] elements,
   how many elements are in [A -> B]? Actually we need to assume the
   axiom of extensionality to get the right answer. This axiom states that any 
   two functions which are equal for all arguments are equal.
   *)

Axiom ext : forall (A B : Set)(f g : A -> B), (forall x:A,f x = g x) -> f = g.

(** * The Curry Howard Correspondence *)

(** There is a close correspondence between sets and propositions.  We
   may translate a proposition by the set of its proofs. The question
   wether a proposition holds corresponds then to finding an element
   which lives in the corresponding set. Indeed, this is what Coq's proof objects 
   are based upon. For propositional logic the translation works as follows:
   - conjunction ([/\]) is translated as product ([*]),
   - disjunction ([\/]) is translated as disjoint union ([+]),
   - implication ([->]) is translated as function set ([->]).
   I leave it to you to figure out what to translate [True] and [False] with.

   As an example we consider the currying theorm for propositional logic. 
   Applying the translation we obtain:
*)

Definition curry (A B C : Set) : ((A * B -> C) -> (A -> B -> C)) :=
  fun f => fun a => fun b => f (a , b).

Definition curry' (A B C : Set) : (A -> B -> C) -> (A * B -> C) :=
  fun g => fun p => g (fst p) (snd p).

(** Indeed, [curry] and [curry'] do not just witness a logical equivalence
   but they constitute an _isomorphism_. That is if we go back and forth we end up 
   with the lement we started. We will need the axiom of extensionality.
   To make this precise we get: *)

Lemma curryIso1 : forall A B C : Set, forall f : A * B -> C,
  f = (curry' (curry f)).
intros A B C f.
apply ext.
intro p.
destruct p.
reflexivity.
Qed.

Lemma curryIso2 :  forall A B C : Set, forall g : A -> B -> C,
  g = (curry (curry' g)).
intros A B C g.
apply ext.
intro a.
apply ext.
intro b.
reflexivity.
Qed.

End Sets.