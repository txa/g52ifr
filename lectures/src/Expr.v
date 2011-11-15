(* Copyright (c) 2011, Thorsten Altenkirch *)

(** %\chapter{%#<H1>#Compiling expressions%}%#</H1># *)
Section Expr.

(** We are going to use the standard library for lists. *)

Require Import Coq.Lists.List.

Set Implicit Arguments.

(** * Evaluating expressions. *)

(** 
   We define a simple language of expressions over natural numbers:
   only containing numeric constants and addition. This is already a
   useful abstraction over the one-dimensional view of a program as a
   sequence of symbols, i.e. we don't care about precedence or
   balanced bracktes.

   However, this means that at some point we'd have to implement a
   parser and verify it. 
*)


Inductive Expr : Set :=
  | Const : nat -> Expr
  | Plus : Expr -> Expr -> Expr.

(**
   The expression "(3 + 5) + 2" is represented by the following tree:
*)

Definition e1 : Expr := Plus (Plus (Const 3) (Const 5)) (Const 2).

(**
   We give a "denotational" semantics to our expressions by
   recursively assigning a value (their denotation). This process is
   called evaluation - hence the function is called [eval]. It is
   defined by structural recursion over the structure of the
   expression tree.
*)

Fixpoint eval (e:Expr) {struct e} : nat :=
  match e with
  | Const n => n
  | Plus e1 e2 => (eval e1) + (eval e2)
  end.

(** Let's evaluate our example expression: *)

Eval compute in (eval e1).

(** * A stack machine *)

(**
   We are going to describe how to calculate the value of an
   expression on a simple stack machine - thus giving rise to an
   "operational semantics". 

   First we specify the operation of our machine, there are only two
   operations :
*)

Inductive Op : Set :=
  | Push : nat -> Op
    (* pushes a constant on the stack *)
  | PlusC : Op.
    (* addition, repalces the top two elements of the stack by their
       sum. *)

(* Machine code is a list of operations: *)
Definition Code := list Op.
(* A stack is a list of natural numbers: *)
Definition Stack := list nat.

(**
   We define recursively how to execute code wrt any given stack. This
   function proceeds by linear recursion over the stack and could be
   easily implemented as a "machine".

*)
 
Fixpoint runAux (st:Stack)(p:Code) {struct p} : nat := match p with
    | nil => match st with
             | nil => 0
             | n :: st' => n
             end
    | op :: p' =>
        match op with
        | Push n => runAux (n :: st) p'
        | PlusC => match st with
                   | nil => 0
                   | n :: nil => 0
                   | n1 :: n2 :: st' =>
                       runAux ((n1 + n2) :: st') p'
                   end
        end
    end.


(** We run a piece of code by starting with the empty stack. *)

Definition run (p:Code) : nat := runAux nil p.

Definition c1 : Code 
  := Push 2 :: Push 3 :: PlusC :: nil.

Eval compute in (run c1).

(** A simple compiler *)

(**
   We implement a simple compiler which translates an expression into
   code for the stack machine.

   A naive implementation looks like this:

*)

Fixpoint compile_naive (e:Expr) {struct e} : list Op :=
  match e with
  | Const n => (Push n) :: nil
  | Plus e1 e2 => (compile_naive e2)++
                  (compile_naive e1)++
                  (PlusC::nil)

  (** Why do we need to do this in this order? *)

  end.

(** 
   A better alternative both in terms of efficiency and verification 
   is a "continuation based" compiler. We compile an expression e wrt
   a continuation p, some code which is going to be run after it.
*)

Fixpoint compileAux (e:Expr) (p:Code) {struct e} : Code := match e with
   | Const n => Push n :: p
   | Plus e1 e2 => compileAux e2 
                     (compileAux e1 (PlusC :: p))
   end.

(** The top level compiler just uses the empty continuation. *)

Definition compile (e:Expr) : Code := compileAux e nil.

(** Test the compiler *)

Eval compute in compile e1.

(** And run the compiled code: *)

Eval compute in run (compile e1).

(** * Compiler correctness *)

(**
   Compiler correctness means that the operational semantics of the
   compiled code agrees with its denotational semantics.

   forall e:Expr, run (compile e) = eval e.

   However, to prove this we have to show a more general lemma about
   the auxilliary functions.
   
*)

Lemma compileLem : 
forall (e:Expr)(p:Code)(st:Stack),
  runAux st (compileAux e p) = 
  runAux ((eval e)::st) p.
intro e.
induction e.
intros p st.
simpl.
reflexivity.
intros p st.
simpl.
rewrite IHe2.
rewrite IHe1.
simpl.
reflexivity.
Qed.

(** The main theorem is a simple application of the previous lemma: *)

Theorem compileOk : forall e:Expr, 
  run (compile e) = eval e.
intro e.
unfold run.
unfold compile.
rewrite compileLem.
simpl.
reflexivity.
Qed.

End Expr.