(* Copyright (c) 2011, Thorsten Altenkirch *)

(** %\chapter{Predicate Logic}% *)
Section pred.

(** Predicate logic extends propositional logic: we can talk about 
    sets of things, e.g. numbers and define properties, called
    predicates. We will soon define some useful sets and ways to
    define sets but for the moment, we will use set variables as we
    have used propositional variables before.

    In Coq we can declare set variables the same way as we have
    declared propositional variables:
*)

Variables Students Modules : Set.

(** Thus we have declared Students and Modules to be variables for
    sets. While we have chosen the names so that we have a certain
    ideas what they stand for, logically they are arbitrary. That is
    any tautology using set variable remains true if we substitute the
    set variables with any conrete set (e.g. natural numbers or
    booleans, etc).

    Next we also assume some predicate variables, we let Clever
    and Funny be properties of Stduents.
*)

Variables Clever Funny : Students -> Prop

(** Coq views these predicates as functions from [Students] to [Prop]. That
    is if we have an element of [Students], e.g. [jim : Students], we can apply [Clever] to a by
    writing [Clever jim] to express that [jim] is clever.

    However, the same caveat as before applies; [Clever] and [Funny] are
    just variables, anything we prove holds for any other predicate
    (in particulr we could replace [Clever] by [Stupid] and [Funny] by
    [Boring], assumung that [Funny Boring : Students -> Prop].

    We can also have properties relating several elements, possibly of
    different sets, these are usually called _relations_. We introduce 
    a relation [Attends], relating [Students] and [Modules] by:
*)

Variable Attends : Students -> Modules -> Prop

(** If we assume that [g52ifr : Modules] we can form the proposition
    [Attends jim g52ifr] expressing that [jim] attends [g52ifr].
*)

(** * Universal quantification *)

(** To say all elements of A have the property P, we write
    [forall x:A, P x] more general we can form [forall x:A, PP]
    where [PP] is a proposition possibly containing the variable [x]. 
    Another example is [forall x:A,P x -> Q x] meaning that any
    element of [A] that has the property [P] will also have the
    property [Q]. 

    As an example we show that if all elements of [A] have the
    property [P] and that if whenever an element of [A] has the
    property 