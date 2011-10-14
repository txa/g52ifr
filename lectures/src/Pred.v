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

Variables A B : Set.

(** Thus we have declared A and B to be variables for sets. For
    example think of A=the set of students and B= the set of
    modules. That is any tautology using set variable remains true if
    we substitute the set variables with any conrete set (e.g. natural
    numbers or booleans, etc).

    Next we also assume some predicate variables, we let P
    and Q be properties of A (e.g. P x may mean P is clever
    and Q x means x is funny.
*)

Variables P Q : A -> Prop.

(** Coq views these predicates as functions from [A] to [Prop]. That
    is if we have an element of [A], e.g. [a : A], we can apply [P] to a by
    writing [P a] to express that [a] has the property [P].

    We can also have properties relating several elements, possibly of
    different sets, these are usually called _relations_. We introduce 
    a relation [R], relating [A] and [B] by:
*)

Variable R : A -> B -> Prop.

(** E.g. R could be the relation "attends" and we would write 
    "R jim g52ifr" to express that Jim attends g52ifr.
*)

(** * Universal quantification *)

(** To say all elements of A have the property P, we write
    [forall x:A, P x] more general we can form [forall x:A, PP]
    where [PP] is a proposition possibly containing the variable [x]. 
    Another example is [forall x:A,P x -> Q x] meaning that any
    element of [A] that has the property [P] will also have the
    property [Q]. In our example that would mean that any clever
    student is also funny.

    As an example we show that if all elements of [A] have the
    property [P] and that if whenever an element of [A] has the
    property [P] has also the property [Q] then all alements of [A]
    have the property [Q]. That is if all students are clever, and every 
    clever student is funny, then all students are funny. In predicate
    logic we write [(forall x:A,P x) -> (forall x:A,P x -> Q x) -> forall x:A, P x].

    We introduce some new syntactic cinventions: the scope of an forall
    always goes as far as possible. That is we read [forall x:A,P x /\ Q]
    as [forall x:A, (P x /\ Q)]. Given this could we have saved any parentheses
    in the example above without changing the meaning?

    As before we use introduction and elimination steps. Maybe surprisingly
    the tactics for implication and universal quantification are the same.
    The reason is that in Coq's internal language implication and universal quantification 
    are actually the same.
*)

Lemma AllMono : (forall x:A,P x) -> (forall x:A,P x -> Q x) -> forall x:A, Q x.
intros H1 H2.
(** To prove [forall x:A,Q x] assume that there is an element [a:A] and prove [Q a]
    We use [intro a] to do this.
.*)
intro a.
(** If we know [H2 : forall x:A,P x -> Q x] and we want to prove [Q a] we can use 
    [apply H2] to instantiate the assumption to [P a -> Q a] and at the same 
    time eliminate the implication so that it is left to prove [P a].
*)
apply H2.
(** Now if we know [H1 : forall x:A,P x] and we want to show [P a], we use
    [apply H1] to prove it. After this the goal is completed. *)
apply H1.
(** In the last step we only instantiated the universal quantifier. *)
Qed.

(** 
So to summarize:
   - introduction for [forall]
     To show [forall x:A,P x] we say [intro a] which introduces an assumption [a:A]
     and it is left to show [P] where each free occurence of [x] is replaced by [a].
   - elimination for [forall]
     We only describe the simplest case: If we know [H : forall x:A,P] and we want to 
     show P where [x] is replaced by [a] we use [apply H] to prove [P a]. 

When I say that each free occurence of [x] in the proposition [P] is replaced by [a],
I mean that occurences of [x] which are in the scope of another quantifier (these are clalled bound) are not affected. E.g.
if [P] is [Q x /\ forall x:A,R x x] then the only free occurence of [x] is the one in [Q x]. That is we obtain [Q a  /\ forall x:A,R x x]. The occurences of [x] in [forall x:A,R x x] are bound.

We can also use [intros] here. That is if the current goal is [forall x:A,P x -> Q x] then 
[intros x P] will introduce the assumptions [x:A] and [H:P x].

The general case for [apply] is a bit hard to describe. Basically apply may introduce several
subgoals if the assumption has a prefix of [forall] and [->]. E.g. if we have assumed
[H : forall x:A,forall y:B,P x -> Q y -> R x y] and our current goal is [R a b] then
[apply H] will instantiate [x] with [a] and [y] with [b] and generate the new goals 
[Q b] and [R a b].

Next we are going to show that [forall] _commutes with_ [/\]. That is
we are going to show [(forall x:A,P x /\ Q x) <-> (forall x:A, P x) /\ (forall x:A, Q x)]
that is "all students are clever and funny" is equivalent to "all students are clever"
and "all students are funny". 
*)

Lemma AllAndCom : (forall x:A,P x /\ Q x) <-> (forall x:A, P x) /\ (forall x:A, Q x).
split.
(** Proving [->] *)
intro H.
split.
intro a.
assert (pq : P a /\ Q a).
apply H.
destruct pq as [p q].
exact p.
intro a.
assert (pq : P a /\ Q a).
apply H.
destruct pq as [p q].
exact q.
(** Proving [<-] *)
intro H.
destruct H as [p q].
intro a.
split.
apply p.
apply q.
Qed.

(** This proof is quite lengthy and I even had to use [assert]. You are welcome to find a shorter proof (but without using any more sophisticated tactics). *)

(** Another question: Does [forall] also commute with [\/]? That is does 
    [(forall x:A,P x \/ Q x) <-> (forall x:A, P x) \/ (forall x:A, Q x)]
    hold? If not, how can you show that?
*)

(** * Existential quantification *)

(** To say that there is an element of A having the property P, we write
    [exists x:A, P x] more general we can form [exists x:A, PP]
    where [PP] is a proposition possibly containing the variable [x]. 
    Another example is [exists x:A,P x /\ Q x] meaning that there
    is an element of [A] that has the property [P] and the
    property [Q]. In our example that would mean that 
    there is a student who is both clever and funny.

    As an example we show that if there is an element of [A] having the
    property [P] and that if whenever an element of [A] has the
    property [P] has also the property [Q] then there is an elements of [A]
    having the property [Q]. That is if there is a clever student, and every 
    clever student is funny, then there is a funny student. In predicate
    logic we write [(exists x:A,P x) -> (forall x:A,P x -> Q x) -> exists x:A, P x].

    Btw, we are not changing the 2nd quantifier, it stays [forall]. What would happen
    if we would replace it by [exists]

    The syntactic conventions for [exists] are the same as for [forall]: the scope of an [exists]
    always goes as far as possible. That is we read [exists x:A,P x /\ Q]
    as [exists x:A, (P x /\ Q)]. 

    The tactics for existential quatification are similar to the ones for conjunction. 
    To prove an existential statement [exists x:A,PP] we use [exists a] where
    [a : A] is our _witness_. We then have to prove [PP] where each free occurence of [x]
    is replaced by [a]. To use an assumption [H : exists x:A,PP] we employ 
    [destruct H as [a p]] which destructs [H] into [a : A] and [p : PP'] where [PP'] is [PP] 
    where all free occurences of [x] have been replaced by [a].
*)

Lemma ExistsMono : (exists x:A,P x) -> (forall x:A,P x -> Q x) -> exists x:A, Q x.
intros H1 H2.
(** We first eliminate or assumption. *)
destruct H1 as [a p].
(** And now we introduce the existential. *)
exists a.
apply H2.
(** In the last step we instantiated a universal quantifier. *)
exact p.
Qed.











