(* Copyright (c) 2011, Thorsten Altenkirch *)

(** %\chapter{%#<H0>#Predicate Logic%}%#</H0># *)

Section pred.

(** Predicate logic extends propositional logic: we can talk about 
    sets of things, e.g. numbers and define properties, called
    predicates and relations. We will soon define some useful sets and ways to
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
    and Q x means x is funny).
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
    logic we write [(forall x:A,P x) -> (forall x:A,P x -> Q x) -> forall x:A, Q x].

    We introduce some new syntactic conventions: the scope of an forall
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
    We use [intro a] to do this. *)

intro a.

(** If we know [H2 : forall x:A,P x -> Q x] and we want to prove [Q a] we can use 
    [apply H2] to instantiate the assumption to [P a -> Q a] and at the same 
    time eliminate the implication so that it is left to prove [P a]. *)

apply H2.

(** Now if we know [H1 : forall x:A,P x] and we want to show [P a], we use
    [apply H1] to prove it. After this the goal is completed. *)

apply H1.

(** In the last step we only instantiated the universal quantifier. *)

Qed.

(** 
So to summarize:
   - introduction for [forall]:
     To show [forall x:A,P x] we say [intro a] which introduces an assumption [a:A]
     and it is left to show [P] where each free occurence of [x] is replaced by [a].
   - elimination for [forall]:
     We only describe the simplest case: If we know [H : forall x:A,P] and we want to 
     show P where [x] is replaced by [a] we use [apply H] to prove [P a]. 

When I say that each free occurence of [x] in the proposition [P] is replaced by [a],
I mean that occurences of [x] which are in the scope of another quantifier (these are called bound) are not affected. E.g.
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

(** This proof is quite lengthy and I even had to use [assert]. There is a shorter proof, if we use [edestruct] instead of [destruct].  
     The "e" version of tactics introduce metavariables (visible as ?x) which are instantiated 
    when we are using them. See the Coq reference manual for details.

    I only do the [->] direction using [edestruct], the other one stays the same.
*)

Lemma AllAndComE : (forall x:A,P x /\ Q x) -> (forall x:A, P x) /\ (forall x:A, Q x).

(** Proving [->] *)

intro H.
split.
intro a.
edestruct H as [p q].
apply p.
intro a.
edestruct H as [p q].
apply q.
Qed.

(** Question: Does [forall] also commute with [\/]? That is does 
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
    logic we write [(exists x:A,P x) -> (forall x:A,P x -> Q x) -> exists x:A, Q x].

    Btw, we are not changing the 2nd quantifier, it stays [forall]. What would happen
    if we would replace it by [exists]?

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

(** 
So to summarize:
   - introduction for [exists]
     To show [exists x:A,P] we say [exists a] where [a : A] is any expression of type [a].
     It remains to show [P] where any free occurence of [x] is replaced by [a].
   - elimination for [exists]
     If we know [H : exists x:A,P] we can use [destruct H as [a p]] which destructs [H]
     intwo two assumptions: [a : A] and [p : P'] where [P'] is obtained from [P] by
     replacing all free occurences of [x] in [P] by [a].

Next we are going to show that [exists] _commutes with_ [\/]. That is
we are going to show [(exists x:A,P x \/ Q x) <-> (exists x:A, P x) \/ (exits x:A, Q x)]
that is "there is a student who is clever or funny" is equivalent to "there is a clever student
or there is a funny student".
*)

Lemma ExOrCom : (exists x:A,P x \/ Q x) <-> (exists x:A, P x) \/ (exists x:A, Q x).
split.

(** Proving [->] *)

intro H.

(** It would be too early to use the introduction rules now.
    We first need to analyze the assumptions. This is a common
    situation. *)

destruct H as [a pq].
destruct pq as [p | q].

(** First case [P a]. *)

left.
exists a.
exact p.

(** Second case [Q a]. *)

right.
exists a.
exact q.

(** Proving [<-] *)

intro H.
destruct H as [p | q].

(** First case [exists x:A,P x] *)

destruct p as [a p].
exists a.
left.
exact p.

(** Second case [exists x:A,Q x] *)

destruct q as [a q].
exists a.
right.
exact q.
Qed.

(** * Another Currying Theorem *)

(** There is also a currying theorem in predicate logic which exploits 
    the relation between [->] and [forall] on the one hand and 
    [/\] and exists on the other. That is we can show that 
    [forall x:A,P x -> S] is equivalent to [(exists x:A,P x) -> S].
    Intuitively, think of [S] to be "the lecturer is happy". Then
    the left hand side can be translated as "If there is any student
    who is clever, then the lecturer is happy" and the right hand side
    as "If there exists a student who is clever, then the lecturer is happy".
    The relation to the propositional currying theorem can be seen, when we
    replace [forall] by [->] and [exists] by [/\].
    
    To prove this tautology we assume an additional proposition.
*)

Variable S : Prop.

Lemma Curry : (forall x:A,P x -> S) <-> ((exists x:A,P x) -> S).
split.

(** proving [->] *)

intro H.
intro p.
destruct p as [a p].

(** With our limited knowledge of Coq's tactic language we need
    to instantiate [H] using [assert]. There are better ways 
    to do this... We will see later.*)

assert (H' : P a -> S).
apply H.
apply H'.
exact p.

(** proving [<-]. *)

intro H.
intros a p.
apply H.
exists a.
exact p.
Qed.

(** As before the explicit instantiation using [assert] can be avoided by using the "e" version of a tactic. In
    this case it is [eapply]. Again, I refer to the Coq reference manual for details. I only do one direction, the other one stays the same.*)

Lemma CurryE : (forall x:A,P x -> S) -> ((exists x:A,P x) -> S).

(** proving [->] *)

intro H.
intro p.
destruct p as [a p].
eapply H.
apply p.
Qed.

(** * Equality *)

(** Predicate logic comes with one generic relation which is defined for 
    all sets: equality ([=]). Given two expressions [a,b : A] we write 
    [a = b : Prop] for the proposition that [a] and [b] are equal,
    that is they describe the same object. 

    How can we prove an equality? That is what is the introduction rule for equality? 
    We can prove that every expression is [a : A] is equal to itself [a = a]
    using the tactic [reflexivity]. How can we use an assumption
    [H : a = b]? That is how can we eliminate equality? If we want to
    prove a goal [P] which contains the expression [a] we can use
    [rewrite H] to _rewrite_ all those [a]s into [b]s.

    To demonstrate how to use these tactics we show that equality is
    an _equivalence relation_ that is, it is:
    - reflexive ([forall a:A, a = a])
    - symmetric ([forall a b:A, a=b -> b=a])
    - transitive ([forall a b c:A, a=b -> b=c -> a=c].
*)

Lemma eq_refl : forall a:A, a = a.
intro a.

(** Here we just invoke the reflexivity tactic. *)

reflexivity.
Qed.

Lemma eq_sym : forall a b:A, a=b -> b=a.
intros a b H.

(** Here we use rewrite to reduce the goal. *)

rewrite H.
reflexivity.
Qed.

Lemma eq_trans : forall a b c:A, a=b -> b=c -> a=c.
intros a b c ab bc.
rewrite ab.
exact bc.
Qed.


(** Do you know any other equivalence relations? *)

(* There are some other tactics which are useful when working with equality. We will see their
    uses later.
    - [rewrite<-], like rewrite but rewrites form right to left. That is, if the 
      goal is [H : a = b] then [rewrite<- H] then changes all occurences of [b] in
      the current goal into [a].
    - [pattern] massages the current goal so that the focus is on a certain subterm.
      This is important, if there are several occurences of the term to be reqritten but 
      we want to change only one. So [pattern t] restricts the effect of [rewrite] or
      [rewrite<-] to the subterm [t].
*)    


(** * Classical Predicate Logic *)

(** The principle of the excluded middle [classic P : P \/ ~P] has many important 
    applications in predicate logic. As an example we show that [exists x:A,P x]
    is equivalent to [~ forall x:A, ~ P x]. 

    Instead of using [classic] directly we use the derivable principle
    [NNPP : ~ ~ P -> P] which is also defined in [Coq.Logic.Classical].
*)

Require Import Coq.Logic.Classical.

Lemma ex_from_forall : (exists x:A, P x) <-> ~ forall x:A, ~ P x.
split.

(** proving [->] *)

intro ex.
intro H.
destruct ex as [a p].
assert (npa : ~ (P a)).
apply H.
apply npa.
exact p.

(** proving [<-] *)

intro H.
apply NNPP.
(** Instead of proving [exists x:A,P x] which is hard,
    we show [~~ exists x:A,P x] which is easier. *)
intro nex.
apply H.
intros a p.
apply nex.
exists a.
exact p.
Qed.










