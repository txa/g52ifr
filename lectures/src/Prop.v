
(* Copyright (c) 2011, Thorsten Altenkirch *)

(** %\chapter{%#<H0>#Propositional Logic%}%#</H0># *)

Section prop.

(** 
A proposition is a definitive statement which we may be able to
prove. In Coq we write [P : Prop] to express that [P] is a
proposition. 

We will later introduce ways to construct interesting propositions, but in the moment
we will use propositional variables instead. We declare in Coq:
*) 

Variables P Q R : Prop.

(**
 This means that the [P],[Q],[R] are atomic propositions which may
be substituted by any concrete propositions. In the moment it is helpful to think of them as statements 
like "The sun is shining" or "We go to the zoo." *)

(** We are going to introduce a number of connectives and logical constants to construct propositions:
- Implication [->], read [P -> Q] as if [P] then [Q].
- Conjunction [/\], read [P /\ Q] as [P] and [Q].
- Disjunction [\/], read [P \/ Q] as [P] or [Q].
- [False], read [False] as "Pigs can fly".
- [True], read [True] as "It sometimes rains in England."
- Negation [~], read [~ P] as not [P]. We define [~ P] as [P -> False].
- Equivalence, [<->], read [P <-> Q] as [P] is equivalent to [Q]. We define [P <-> Q] as [(P -> Q) /\ (Q -> P)].

As in algebra we use parentheses to group logical expressions. To save parentheses there are a number of conventions:
- Implication is right associative, i.e. we read [P -> Q -> R] as [P -> (Q -> R)].
- Implication and equivalence bind weaker than conjunction and disjunction. E.g. we read [P \/ Q -> R] as [(P \/ Q) -> R]. 
- Conjunction binds stronger than disjunction. E.g. we read [P /\ Q \/ R] as [(P /\ Q) \/ R].
- Negation binds stronger than all the other connectives, e.g. we read [~ P /\ Q] as [(~ P) /\ Q].

This is not a complete specification. If in doubt use parentheses.
*)

(** We will now discuss how to prove propositions in Coq. If we are
proving a statement containing propositional variables then this means
that the statement is true for all replacements of the variables with
actual propositions. We say it is a tautology. 
*)

(** * Our first proof *)

(** We start with a very simple tautology [P -> P], i.e. if [P] then [P]. 
To start a proof we write:*)

Lemma I : P -> P.

(** It is useful to run the source of this document in Coq to see what
happens.  Coq enters a proof state and shows what we are going to prove
under what assumptions. In the moment our assumptions are that
[P],[Q],[R] are propositions and our goal is [P -> P].  To
prove an implication we add the left hand side to the assumptions and
continue to prove the right hand side - this is done using the [intro]
tactic. We also choose a name for the assumption, let's call it [p].
*)

intro p.

(** This changes the proof state: we now have to prove [P] but we also
have a new assumption [p : P]. We can finish the proof by using this
assumption. In Coq this can done by using the [exact] tactic. *)

exact p.

(** This finishes the proof. We only have to instruct Coq to save the 
proof under the name we have indicated in the beginning, in this case [I].
*)

Qed.

(** Qed stands for "Quod erat demonstrandum". This is Latin for "What was to be shown." *)

(** * Using assumptions. *)

(** Next we will prove another tautology, namely 
[(P -> Q) -> (Q -> R) -> P -> R].
Try to understand why this is intuitively true for any propositions [P],[Q] and [R].

To prove this in Coq we need to know how to use an implication which we have assumed.
This can be done using the [apply] tactic: if we have assumed [P -> Q] and we want to 
prove [Q] then we can use the assumption to reduce (hopefully) the problem to proving
[P]. Clearly, using this step is only sensible if [P] is actually easier to prove
than [Q]. Step through the next proof to see how this works in practice!
*)

Lemma C : (P -> Q) -> (Q -> R) -> P -> R.

(** We have to prove an implication, hence we will be using [intro].
Because [->] is right associative the proposition can be written as
[(P -> Q) -> ((Q -> R) -> P -> R)]. Hence we are going to assume [P -> Q].
*)

intro pq. 

(** we continue assuming... *)

intro qr.
intro p.

(** Now we have three assumptions [P -> Q], [Q -> R] and [P]. 
It remains to prove [R]. We cannot use [intro] any more because our goal is not 
an implication. Instead we need to use our assumptions. The only assumption which 
could help us to prove [R] is [Q -> R]. We use the [apply] tactic. *)

apply qr.

(** Apply uses [Q -> R] to reduce the problem to prove [R] to the problem to prove [Q].
Which in turn can be further reduced to proving [P] using [P -> Q].
*)

apply pq.

(** And now it only remains to prove [P] which is one of our assumptions - hence we can use [exact] again. 
*)
exact p.
Qed.

(** * Introduction and Elimination *)

(** We observe that there are two types of proof steps (tactics):
- introduction: How can we prove a proposition? In the case of an implication this is [intro]. To prove [P -> Q], we assume [P] and prove [Q].
- elimination: How can we use an assumption? In the case of implication this is [apply]. If we know [P -> Q] and we want to prove [Q] it is sufficient to prove [P].
Actually [apply] is a bit more general: if we know [P1 -> P2 -> ... -> Pn -> Q] and we want to prove [Q] then it is sufficient to prove [P1],[P2],...,[Pn].

Indeed the distinction of introduction and elimination
steps is applicable to all the connectives we are going to
encounter. This is a fundamental symmetry in reasoning.
*)

(** There is also a 3rd kind of steps: structural steps.
    An example is [exact] which we can use when we want to refer to an assumption.
    We can also use [assumption] then we don't even have to give the name of the assumption. *)

(** If we want to combine several [intro] steps we can use [intros]. We can also use [intros] without parameters in which case Coq does
    as many [intro] as possible and invents the names itself.*)

(** * Conjunction *)

(** How to prove a conjunction? To prove [P /\ Q] we need to prove [P] and [Q]. This is achieved using the [split] tactic. We look at a simple example. *)

Lemma pair : P -> Q -> P /\ Q.

(** On the top level we have to prove an implication. *)

intros p q.

(** now to prove [P /\ Q] we use [split]. *)

split.

(** This creates two subgoals. We do the first *)

exact p.

(** And then the 2nd *)

exact q.
Qed.


(** How do we use an assumption [P /\ Q]. We use [destruct] to split it into two assumptions. 
    As an example we prove that [P /\ Q -> Q /\ P].
*)

Lemma andCom : P /\ Q -> Q /\ P.
intro pq.
destruct pq as [p q].
split.

(** Now we need to use the assumption [P /\ Q]. We destruct it into two assumptions: [P] and [Q].
[destruct] allows us to name the new assumptions. *)

exact q.
exact p.
Qed.

(** Can you see a shorter proof of the same theorem ? *)

(** To summarize for conjunction we have:
- introduction: [split]: to prove [P /\ Q] we prove both [P] and [Q].
- elimination: [destruct]: to prove something from [P /\ Q] we prove it from assuming both [P] and [Q].
*)

(** * The currying theorem *)

(** Maybe you have already noticed that a statement like [P -> Q -> R]
basically means that [R] can be proved from assuming both [P] and [Q].
Indeed, it is equivalent to [P /\ Q -> R]. We can show this formally by using 
[<->] for the first time.

All the steps we have already explained so I won't comment. It is a good idea to step through the proof using Coq.
*)

Lemma curry : (P /\ Q -> R) <-> (P -> Q -> R).
unfold iff.
split.
intros H p q.
apply H.
split.
exact p.
exact q.
intros pqr pq.
apply pqr.
destruct pq as [p q].
exact p.
destruct pq as [p q].
exact q.
Qed.

(** I call this the currying theorem, because this is the logical counterpart of currying in functional programming: i.e. that a function with several parameters can be reduced to a function which returns a function. So in Haskell addition has the type [Int -> Int -> Int]. *)

(** * Disjunction *)

(** To prove a disjunction like [P \/ Q] we can either prove [P] or [Q]. This is done via the tactics [left] and [right]. As an example we prove [P -> P \/ Q]. *)

Lemma inl : P -> P \/ Q.
intros p.

(** Clearly, here we have to use [left]. *)

left.
exact p.
Qed.

(** To use a disjunction [P \/ Q] to prove something we have to prove it from both [P] and [Q]. The tactic we use is also called [destruct] but in this case [destruct] creates two subgoals. This can be compared to case analysis in functional programming. Indeed we can prove the following theorem. *)

Lemma case : P \/ Q -> (P -> R) -> (Q -> R) -> R.
intros pq pr qr.
destruct pq as [p | q].

(** The syntax for [destruct] for disjunction is different if we want to name the assumption we have to separate them with [|]. Indeed each of them will be visible in a different part of the proof. 
First we assume [P].*)

apply pr.
exact p.

(** And then we assume [Q] *)

apply qr.
exact q.
Qed.

(** So again to summarize: For disjunction we have:
- introduction: there are two ways to prove a disjunction [P \/ Q]. We use [left] to prove it from [P] and [right] to prove it from [Q]. 
- elimination: If we have assumed [P \/ Q] then we can use [destruct] to prove our current goal from assuming [P] and from assuming [Q].
*)

(** * Distributivity *)

(** As an example of how to combine the proof steps for conjunction
and disjunction we show that distributivity holds, i.e. [P /\ (Q \/
R)] is logically equivalent to [(P /\ Q) \/ (P /\ R)]. This is
reminiscent of the principle in algebra that [x * (y + z) = x * y + x * z]. 
*)

Lemma andOrDistr : P /\ (Q \/ R) 
              <-> (P /\ Q) \/ (P /\ R).
split.
intro pqr.
destruct pqr as [p qr].
destruct qr as [q | r].
left.
split.
exact p.
exact q.
right.
split.
exact p.
exact r.
intro pqpr.
destruct pqpr as [pq | pr].
split.
destruct pq as [p q].
exact p.
left.
destruct pq as [p q].
exact q.
destruct pr as [p r].
split.
exact p.
right.
exact r.
Qed.

(** As before: to understand the working of this script it is advisable to step through it using Coq. *)

(** * True and False *)

(** [True] is just a conjunction with no arguments as opposed to [/\] which has two. Similarity [False] is a disjunction with no arguments. As a consequence we already know the proof rules for [True] and [False].

We can prove [True] without any assumptions.
*)

Lemma triv : True.
split.

(** Here we split but instead of two subgoals we get none. *)

Qed.

(** On the other had we can prove anything from [False]. This is called "ex falso quod libet" in Latin.
*)

Lemma exFalso : False -> P.
intro f.
destruct f.

(** Here instead of two subgoals we get none. *)

Qed.

(** In terms of introduction and elimination steps we may summarize:
   - True: There is one introduction rule but no elimination.
   - False: There is one elimination rule but no introduction.
*)

(** * Negation *)

(** [~ P] is defined as [P -> False]. Using this we can establish some basic theorems about negation. First we show that we cannot have both [P] and [~ P], that is we prove [~ (P /\ ~ P)].
*)

Lemma incons : ~ ( P /\ ~ P).
unfold not.
intro h.
destruct h as [p np].
apply np.
exact p.
Qed.


(** Another example is to show that [P] implies [~ ~ P]. *)

Lemma p2nnp : P -> ~ ~ P.
unfold not.
intros p np.
apply np.
exact p.
Qed.

(*
Lemma nnp2p : ~ ~ P -> P.
unfold not.
intro nnp.
assert (f : False).
apply nnp.
intro p.
*)

(** * Classical Reasoning *)

(** You may expect that we can also prove the other direction [~ ~ P -> P] and that indeed [P <-> ~ ~ P]. 
    We can reason that [P] is either [True] or [False] and in both cases [~ ~ P] will be the same. However,
    this reasoning is not possible using the principles we have introduced so far. The reason is that Coq is based
    on intuitionistic logic, and the above proposition is not provable intuitionistically.

    However, we can use an additional axiom, which corresponds to the principle that every proposition is either [True] 
    or [False], this is the Principle of the Excluded Middle [P \/ ~ P]. In Coq this can be achieved by: *)

Require Import Coq.Logic.Classical.

(** This means we are now using Classical Logic instead of Intuitionistic Logic. The only difference is that we have an
    axiom [classic] which proves the principle of the excluded middle for any proposition. We can use this to prove 
    [~ ~ P -> P]. *)

Lemma nnpp : ~~P -> P.
intro nnp.

(** Here we use a particular instance of [classic] for [P]. *)

destruct (classic P) as [p | np].

(** First case [P] holds *)

exact p.

(** 2nd case [~ P] holds. Here we appeal to [exFalso]. *)

apply exFalso.

(** Notice that we have shown [exFalso] only for [P]. We should have shown it for any proposition but this would 
   involve quantification over all propositions and we haven't done this yet. *)

apply nnp.
exact np.
Qed.

(** Unless stated otherwise we will try to prove propositions intuitionsitically, that is without using [classic].
   An intuitionistic proof provides a positive reason why something is true, while a classical proof may be
   quite indirect and not so easily acceptable intuitively. Another advantage of intuitionistic reasoning is that it
   is constructive, that is whenever we prove the existence of a certain object we can also explicitly construct it.
   This is not true in intuitionistic logic. Moreover, in intuitionistic logic we can make differences which disappear
   when using classical logic. For example we can explicit state when a property is decidable, i.e. can be computed 
   by a computer program. 
*)

(** * The cut rule *)

(** This is a good point to introduce another structural rule: the cut rule.
    Cutting a proof means to introduce an intermediate goal, then you prove 
    your current goal from this intermediate goal, and you prove theintermediate goal.
    This is particularly useful when you use the intermediate goal several times.

    In Coq this can be achieved by using [assert]. [assert h : H] introduces [H] as a new 
    subgoal and after you have proven this you can use an assumption [h : H] to prove
    your original goal.

    The following (artificial) example demonstrates the use of [assert].
 *)

Lemma usecut : (P /\ ~P) -> Q.
intro pnp.
(** If we had a generic version of [exFalso] we could use this.
    Instead we can introduce [False] as an intermediate goal. *)
assert (f : False).
(** which is easy to prove *)
destruct pnp as [p np].
apply np.
exact p.
(** and using [False] it is easy to prove [Q]. *)
destruct f.
Qed.

(** This example also shows that sometimes we have to cut (i.e. use [assert]) to prove something.
*)      