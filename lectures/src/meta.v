(* Copyright (c) 2011, Thorsten Altenkirch *)

(** %\chapter{%#<H1>#Coq in Coq%}%#</H1># *)
Section Meta.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.

Set Implicit Arguments.

(** This chapter is about using Coq to reason about its own logic. 
   This was the title of a paper by Bruno Barras who managed to 
   develop the theory of Coq inside Coq. 

   Obviously, we won't be able to do this here so we are going to
   focus on a more modest goal: we are limiting ourselves to
   propositional logic and to keep things short we will look 
   at propositional logic with implication only.

   We are going to develop this logic inside coq using _natural
   deduction_. This is very close to the atcual Coq proof objects.

   An alternative would be to use _combinatory logic_. We are going to
   compare these two approaches and we will show that they are equivalent.
*)

(** * Formulas as trees *)

(** We are representing logical formulas as trees. Variables are 
   just representined as strings.
*)

Inductive Formula : Set :=
  | Var : string -> Formula
  | Impl : Formula -> Formula -> Formula.

Notation "x ==> y"  := (Impl x y) (at level 30, right associativity).

(** As examples we are going to use three propositions, all
    of them are tautologies. Two of them will show up as the 
    basic combinators of combinatoric logic later. *)

(** The identity combinator "I". *)

Definition I (P : Formula) : Formula := P ==> P.

(** The _constant_ combinator "K". *)

Definition K (P Q : Formula) : Formula := P ==> Q ==> P.

(** The (mysterious) combinator "S". *)

Definition S (P Q R : Formula) : Formula := 
  (P ==> Q ==> R)
  ==> (P ==> Q)
  ==> P ==> R.

(** We represent Hypotheses as a list of formula. *)

Definition Hyps : Set := list Formula.

(** * Natural deduction *)

(** We are ging to represent the proposition that a formula [P]
   is provable from a list of assumptions [Hs] as 
   [ND_Proof Hs P]. This is an inductive definition, the
   constructors are nodes in the proof tree. 
*)

Inductive ND_Proof : Hyps -> Formula -> Prop :=
(** The first constructor [nd_ass] allows us to use the last 
    hypothesis from our list of hypotheses (which appears at the
    head of the list). *)

| nd_ass : forall (Hs : Hyps)(P : Formula),
             ND_Proof (P :: Hs) P
(** To be able to access earlier hypothesis we use [nd_weak]
   which allows us to ignore the last hypothesis (i.e. the head of 
   the list). *)

| nd_weak : forall (Hs : Hyps)(P Q : Formula),
             ND_Proof Hs P -> ND_Proof (Q :: Hs) P
(** The next constructor [nd_intro] corresponds to the intro 
   tactic in coq: to prove [P ==> Q] we assume [P], i.e. we add it 
   to the list of assumptions, and continue to prove [Q].
*)

| nd_intro : forall (Hs : Hyps)(P Q : Formula),
             ND_Proof (P :: Hs) Q -> ND_Proof Hs (P ==> Q)
(** The elimination for application is slightly different from 
   the one in Coq which is hard to state precisely. The rule [nd_apply]
   corresponds to _modens ponens_: if you can prove [P ==> Q]
   and also [P] then you can also prove [Q].
*)

| nd_apply : forall (Hs : Hyps)(P Q : Formula),
             ND_Proof Hs (P ==> Q) -> ND_Proof Hs P -> ND_Proof Hs Q.


(** As examples we are going to prove that the examples [I],[K] 
   and [S] are provable. *)

(** The proof for [I] follows almost exactly the proof of 
   the same tautology in Coq. *)

Lemma nd_I : forall (Hs : Hyps)(P : Formula),  
                  ND_Proof Hs (I P).
intros Hs P.
unfold I.
apply nd_intro.
apply nd_ass.
Qed.

(** To prove [K] we need to use [weak]. *)

Lemma nd_K : forall (Hs : Hyps)(P Q : Formula), 
                   ND_Proof Hs (K P Q).
intros Hs P Q.
unfold K.
apply nd_intro.
apply nd_intro.
apply nd_weak.
apply nd_ass.
Qed.

(** The proof of [S] uses [nd_apply]. It also shows that 
   modens ponens isn't so suitable to interactive proof,
   because we need some hindsight how to apply it. 
*)

Lemma nd_S : forall (Hs : Hyps)(P Q R : Formula), 
                   ND_Proof Hs (S P Q R).
intros Hs P Q R.
unfold S.
apply nd_intro.
apply nd_intro.
apply nd_intro.
eapply nd_apply. eapply nd_apply.
apply nd_weak. apply nd_weak. apply nd_ass.
apply nd_ass. 
eapply nd_apply.
apply nd_weak. apply nd_ass.
apply nd_ass.
Qed.

(** * Combinatory logic. *)

(** Combinatory logic (also sometimes called "Hilbert style logic")
   is based on the maybe surprising observation that we can replace
   [nd_intro] by adding [K] and [S] as axioms. This leads
   to a variable free representation of logic. However, to
   be able to compare natural deduction and combinatory logic we 
   will consider combinatory logic with variables here. However,
   if the list of hypotheses is empty we will never need variables
   unlike natural deduction where the [nd_intro] rule introduces variables.
*)

(** We define [CL_Proof Hs P] to mean that [P] is provable from [Hs] in 
   combinatory logic. *)

Inductive CL_Proof : Hyps -> Formula -> Prop :=

(** The rules relating to hypothesis are exactly the same as the
    ones for natural deduction. *)

| cl_ass : forall (Hs : Hyps)(P : Formula),
             CL_Proof (P :: Hs) P
| cl_weak : forall (Hs : Hyps)(P Q : Formula),
             CL_Proof Hs P -> CL_Proof (Q :: Hs) P

(** We are adding proofs for K and S as axioms. *)

| cl_K : forall (Hs : Hyps)(P Q : Formula),
             CL_Proof Hs (K P Q)
| cl_S : forall (Hs : Hyps)(P Q R: Formula),
             CL_Proof Hs (S P Q R)

(** Modus ponens [cl_apply] is the same rule as for natural deduction. *)

| cl_apply : forall (Hs : Hyps)(P Q : Formula),
             CL_Proof Hs (P ==> Q) -> CL_Proof Hs P -> CL_Proof Hs Q.


(** We can actually prove [I] from [S] and [K]. *)

Lemma cl_I : forall (Hs : Hyps)(P : Formula), 
         CL_Proof Hs (I P).
intros Hs P.
unfold I.
eapply cl_apply.
eapply cl_apply.
apply cl_S.
apply cl_K.

(** We need to instantiate one of the meta variables by hand.
    This is how we do this in Coq - please check the manual. *)

instantiate (1:= P ==> P ).
apply cl_K.
Qed.

(** Since we did already prove [K] and [S] using natural
   deduction, we can show that every proof in combinatory logic
   can be turned into one in natural deduction. We prove this 
   by induction over the derivation trees. 

   Basically we are showing that each node in an CL proof tree
   can be replaced by a ND tree by replacing the axioms [K]
   and [S] by the corresponding proofs.
*)

Lemma cl2nd : forall (Hs : Hyps)(P : Formula), 
                CL_Proof Hs P -> ND_Proof Hs P.
intros Hs P H.

(** Since the derivation trees are _depndent_, i.e. they depend on 
   the choice of hypotheses and proposition we need to invoke
   the tactic [dependent induction]. *)

dependent induction H.

(** We have now to provide a translation for each case. *)

(** [ass_cl] is translated by [nd_ass]. *)

apply nd_ass.

(** And [weak_cl] by [nd_weak]. Here we have to use the
    induction hypothesis to recursively translate the rest
    of the proof. *)

apply nd_weak.
exact IHCL_Proof.

(** [cl_K] is translated as [nd_K]. Here on axiom is replaced 
    by a small proof tree. *)

apply nd_K.

(** [cl_S] is translated as [nd_S]. *)

apply nd_S.

(** [cl_apply] is translated by [nd_apply]. Since there are two subproofs
    we have to translate them recursively by using the induction hypotheses. 
*)

eapply nd_apply.
apply IHCL_Proof1.
apply IHCL_Proof2.
Qed.

(** * The deduction theorem *)

(** The main ingredient to prove the other direction of the
   equivalence, i.e.  that it is possible to simulate natural
   deduction proofs in combinatory logic, is to show that combinatory
   logic is closed under the [intro] rule. This is usually called _the
   deduction theorem_. *)


Lemma cl_intro : forall (Hs : Hyps)(P Q : Formula),
             CL_Proof (P :: Hs) Q -> CL_Proof Hs (P ==> Q).
intros Hs P Q H.

(** to prove this we need to perform an induction over the proof tree
    showing [CL_Proof (P :: Hs) Q]. *)

dependent induction H.

(** The case for [cl_ass] can be proven using the identity proof
    [cl_I] which we have already derived. *)

apply cl_I.

(** In the case for [cl_weak] we need to use [cl_K]. *)

eapply cl_apply.
apply cl_K.
exact H.

(** The case for [cl_K] can be derived by using [cl_K] once to
    ignore the argument and a 2nd time to provide the constant
    to be actually used.
*)

eapply cl_apply.
apply cl_K.
apply cl_K.

(** The case for [cl_S] is similar only that we use [cl_S] the 2nd time. *)

eapply cl_apply.
apply cl_K.
apply cl_S.

(** The case for [cl_app] is the most interesting one. It finally lifts the
   mystery about [S]. It is actually what we need to translate this 
   case, ie. to shift abstraction over an application. *)

eapply cl_apply.
eapply cl_apply.
apply cl_S.
apply IHCL_Proof1.
reflexivity.
apply IHCL_Proof2.
reflexivity.
Qed.

(** * Equivalence of natural deduction and combinatory logic. *)

(** We have now all the ingredients together to show that natural deduction
    and combinatory logic prove exactly the same propositions. *)


(** To prove the other direction we only need to appeal to the
   deduction theorem [cl_intro] when translating [nd_intro. *)

Lemma nd2cl : forall (Hs : Hyps)(P : Formula), 
                ND_Proof Hs P -> CL_Proof Hs P.
intros Hs P H.
dependent induction H.
apply cl_ass.
apply cl_weak. exact IHND_Proof.
apply cl_intro. exact IHND_Proof.
eapply cl_apply.
apply IHND_Proof1.
exact IHND_Proof2.
Qed.

(** The final theorem *)

Theorem ndcl : forall (Hs : Hyps)(P : Formula), 
                ND_Proof Hs P <-> CL_Proof Hs P.
intros Hs P.
split.
apply nd2cl.
apply cl2nd.
Qed.



