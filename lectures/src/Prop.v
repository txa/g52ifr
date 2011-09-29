(* Copyright (c) 2011, Thorsten Altenkirch *)

(** %\chapter{Propositional Logic}% *)
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
- [True], read [True] as "This is obvious."
- Negation [~], read [~ P] as not [P]. We define [~ P] as [P -> False].
- Equivalence, [<->], read [P <-> Q] as [P] is equivalent to [Q]. We define [P <-> Q] as [(P -> Q) /\ (Q -> P)].

As in algebra we use parentheses to group logical expressions. To save parentheses there are a number of conventions:
- Implication is left associative, i.e. we read [P -> Q -> R] as [P -> (Q -> R)].
- Implication and equivalence bind weaker than conjunction and disjunction. E.g. we read [P \/ Q -> R] as [(P \/ Q) -> R]. 
- Conjunction binds stronger than disjunction. E.g. we read [P /\ Q \/ R] as [(P /\ Q) \/ R].
- Negation binds stronger than all the other connectives, e.g. we read [~ P /\ Q] as [(~ P) /\ Q].

This is not a complete specification. If in doubt use parentheses.
*)

(** We will now discuss how to prove something in Coq. If we are
proving a statement containing propositional variables then this means
that the statement is true for all replacements of the variables with
actual propositions. We say it is a tautology. 
*)

(** * Implication *)

(** We start with a very simple tautology [P -> P], i.e. if [P] then [P]. 
To start a proof we write:*)

Lemma I : P -> P.

(** It is useful to run the source of this document in Coq to see what
happens.  Coq enters a proofstate and shows what we are going to prove
under what assumptions. In the moment our assumptions are that
[P],[Q],[R] are propositions and that we want to prove [P -> P].  To
prove an implication we add the left hand side to the assumptions and
continue to prove the right hand side - this is dine using the [intro]
tactic. We can also choose a name for the assumption, let's call it [p].
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


(** Next we will prove another tautology, namely 
[(P -> Q) -> (Q -> R) -> P -> R]
*)




