(* Copyright (c) 2011, Thorsten Altenkirch *)

(** %\chapter{%#<H0>#Coq in Coq%}%#</H0># *)
Section Meta.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Set Implicit Arguments.


Inductive Formula : Set :=
  | Var : string -> Formula
  | Impl : Formula -> Formula -> Formula.

Notation "x ==> y"  := (Impl x y) (at level 30, right associativity).

Definition I (P : Formula) : Formula := P ==> P.

Definition K (P Q : Formula) : Formula := P ==> Q ==> P.

Definition S (P Q R : Formula) : Formula := 
  (P ==> Q ==> R)
  ==> (P ==> Q)
  ==> P ==> R.

(*
Definition I : Formula := Var "P" ==> Var "P".

Definition K : Formula := Var "P" ==> Var "Q" ==> Var "P".

Definition S : Formula := 
  (Var "P" ==> Var "Q" ==> Var "R")
  ==> (Var "P" ==> Var "Q")
  ==> Var "P" ==> Var "R".
*)

Definition Hypotheses : Set := list Formula.

Inductive ND_Proof : Hypotheses -> Formula -> Prop :=
| ass : forall (Hs : Hypotheses)(A : Formula),
             ND_Proof (A :: Hs) A
| weak : forall (Hs : Hypotheses)(A B : Formula),
             ND_Proof Hs A -> ND_Proof (B :: Hs) A
| intro : forall (Hs : Hypotheses)(A B : Formula),
             ND_Proof (A :: Hs) B -> ND_Proof Hs (A ==> B)
| apply : forall (Hs : Hypotheses)(A B : Formula),
             ND_Proof Hs (A ==> B) -> ND_Proof Hs A -> ND_Proof Hs B.

Lemma proveI : forall (Hs : Hypotheses)(P : Formula),  
                  ND_Proof Hs (I P).
intros Hs P.
unfold I.
apply intro.
apply ass.
Qed.

Lemma proveK : forall (Hs : Hypotheses)(P Q : Formula), 
                   ND_Proof Hs (K P Q).
intros Hs P Q.
unfold K.
apply intro.
apply intro.
apply weak.
apply ass.
Qed.

Lemma proveS : forall (Hs : Hypotheses)(P Q R : Formula), 
                   ND_Proof Hs (S P Q R).
intros Hs P Q R.
unfold S.
apply intro.
apply intro.
apply intro.
eapply apply. eapply apply.
apply weak. apply weak. apply ass.
apply ass. 
eapply apply.
apply weak. apply ass.
apply ass.
Qed.

Inductive CL_Proof : Hypotheses -> Formula -> Prop :=
| ass' : forall (Hs : Hypotheses)(P : Formula),
             CL_Proof (P :: Hs) P
| weak' : forall (Hs : Hypotheses)(P Q : Formula),
             CL_Proof Hs P -> CL_Proof (Q :: Hs) P
| proveK' : forall (Hs : Hypotheses)(P Q : Formula),
             CL_Proof Hs (K P Q)
| proveS' : forall (Hs : Hypotheses)(P Q R: Formula),
             CL_Proof Hs (S P Q R)
| apply' : forall (Hs : Hypotheses)(P Q : Formula),
             CL_Proof Hs (P ==> Q) -> CL_Proof Hs P -> CL_Proof Hs Q.

Lemma proveI' : forall (Hs : Hypotheses)(P : Formula), 
         CL_Proof Hs (I P).
intros Hs P.
unfold I.
eapply apply'.
eapply apply'.
apply proveS'.
apply proveK'.
instantiate (1:= P ==> P ).
apply proveK'.
Qed.

Lemma intro' : forall (Hs Hs' : Hypotheses)(P Q : Formula),
             CL_Proof (P :: Hs) Q -> Hs' = Hs -> CL_Proof Hs (P ==> Q).
intros Hs P Q' Q H e.
induction H.


Require Coq.Program.Equality.

Lemma intro' : forall (Hs : Hypotheses)(P Q : Formula),
             CL_Proof (P :: Hs) Q -> CL_Proof Hs (P ==> Q).
intros Hs P Q H.
dependent induction H.


assert (forall (Hs':Hypotheses)(P' Q':Formula),
  Hs = Hs' -> P = P' -> Q = Q' -> CL_Proof Hs' (P' ==> Q')).
induction H.


induction H.



inversion H.
apply proveI'.
eapply apply'.
apply proveK'.
exact H3.
eapply apply'.
apply proveK'.
apply proveK'.
eapply apply'.
apply proveK'.
apply proveS'.



