(* Copyright (c) 2011, Thorsten Altenkirch *)

(** %\chapter{%#<H0>#Lists%}%#</H0># *)
Section Lists.

(** Lists are the ubiqitous datastructure in functional programming.*)
    
(** * Arithmetic for lists *)
Set Implicit Arguments.

Inductive list (A : Set) : Set :=
 | nil : list A
 | cons : A -> list A -> list A.

Implicit Arguments nil [A].

Infix "::" := cons (at level 60, right associativity).

Definition l23 : list nat
  := 2 :: 3 :: nil.

Definition l123 : list nat
  := 1 :: l23.

Theorem nil_cons : forall (A:Set)(x:A) (l:list A), 
  nil <> x :: l.
intros.
discriminate.
Qed.

Definition tail (A:Set)(l : list A) : list A :=
  match l with
  | nil => nil
  | cons a l => l
  end.

Theorem cons_injective : 
  forall (A : Set)(a b : A)(l m : list A),
    a :: l = b :: m -> l = m.
intros A a b l m h.
fold (tail (cons a l)).
rewrite h.
unfold tail.
reflexivity.
Qed.
  
Definition head (A : Set)(x : A)(l : list A) : A :=
  match l with 
  | nil => x
  | a :: m => a
  end.

Theorem cons_injective' : 
  forall (A : Set)(a b : A)(l m : list A),
    a :: l = b :: m -> a = b.
intros A a b l m h.
fold (head a (a :: l)).
rewrite h.
unfold head.
reflexivity.
Qed.

Theorem ind_list : forall (A : Set)(P : list A -> Prop),
  P nil
  -> (forall (a:A)(l : list A), P l -> P (a :: l))
  -> forall l : list A, P l.
intros A P hnil hcons l.
induction l.
exact hnil.
apply hcons.
exact IHl.
Qed.

(** Append and other operations. *)

Fixpoint app (A : Set)(l m:list A) : list A :=
  match l with
  | nil => m
  | a :: l' => a :: (app l' m)
  end.

Infix "++" := app (right associativity, at level 60).

(** We show that [list A] with [++] and [nil] forms a monoid. Indeed the proofs are basically the same as for ([nat],[+],0). *)

Theorem app_nil_l : forall (A : Set)(l : list A),
  nil ++ l = l.
intros A l.
reflexivity.
Qed.

Theorem app_l_nil :  forall (A : Set)(l : list A),
  l ++ nil = l.
intros A l.
induction l.
reflexivity.
simpl.
rewrite IHl.
reflexivity.
Qed.

Theorem assoc_app : forall (A : Set)(l m n : list A),
  l ++ (m ++ n) = (l ++ m) ++ n.
intros A l m n.
induction l.
reflexivity.
simpl.
rewrite IHl.
reflexivity.
Qed.

(** 

While there are many similarities between [nat] and [list A] there are important differences. Commutativity 
[forall (A : Set)(l m : list A),
   l ++ m = m ++ l]
does not hold. Hence (list A,++,nil) is an example of a non-commutative monoid. Since we commutativity doesn't hold it makes sense to reverse a list. 

To define reverse, we first define the operation [snoc] which adds an element at the end of a given list.
*)

Fixpoint snoc (A:Set)
  (l : list A)(a : A) {struct l} : list A
  := match l with
     | nil => a :: nil
     | b :: m => b :: (snoc m a)
     end.

Fixpoint rev 
  (A:Set)(l : list A) : list A :=
  match l with
  | nil => nil
  | a :: l' => snoc (rev l') a 
  end.

Eval compute in rev l123.
Eval compute in rev (rev l123).

Lemma revsnoc : forall (A:Set)(l:list A)(a : A),
  rev (snoc l a) = a :: (rev l).
induction l.
simpl.
reflexivity.
intro b.
simpl.
rewrite IHl.
simpl.
reflexivity.
Qed.

Theorem revrev :  
  forall (A:Set)(l:list A),rev (rev l) = l.
induction l.
simpl.
reflexivity.
simpl.
rewrite revsnoc.
rewrite IHl.
reflexivity.
Qed.

(* 

  insertion sort

  Our next example is sorting: we want to sort a given lists according 
  to an given order. E.g. the list

  4 :: 2 :: 3 :: 1 :: nil

  should be sorted into

  1 :: 2 :: 3 :: 4 :: nil

  We will implement and verify "insertion sort". To keep things simple 
  we will sort lists of natural numbers wrt to the <= order. First we
  implement a boolean function which comapres two numbers:
*)

Fixpoint leqb (m n : nat) {struct m} : bool :=
  match m with
  | 0 => true
  | S m => match n with 
           | 0 => false
           | S n => leqb m n
           end
  end.

Eval compute in leqb 3 4.
Eval compute in leqb 4 3.

(*
   The main function of insertion sort is the function insert 
   which inserts a new element into an already sorted list:
*)

Fixpoint insert (n:nat)(ms : list nat) {struct ms} : list nat :=
  match ms with
  | nil => n::nil
  | m::ms' => if leqb n m
              then n::ms
              else m::(insert n ms')
  end.

Eval compute in insert 3 (1::2::4::nil).

(* Now sort builds a sorted list from any list by inserting each 
   element into the empty list.
*)

Fixpoint sort (ms : list nat) : list nat :=
  match ms with
  | nil => nil
  | m::ms' => insert m (sort ms')
  end.

Eval compute in sort (4::2::3::1::nil).

(* However, how do we know that sort will work for all lists?
   We are going to verify sort. First we have to define what 
   we mean by sorted. *)

Definition leqb_hd (n:nat)(ms : list nat) : bool :=
  match ms with
  | nil => true
  | m::ms' => leqb n m
  end.

Open Scope bool_scope.

Fixpoint sorted (ms:list nat) : bool :=
  match ms with
  | nil => true
  | m::ms' => leqb_hd m ms' && sorted ms'
  end.

Eval compute in sorted (4::2::3::1::nil).
Eval compute in sorted (sort (4::2::3::1::nil)).

(* to understand the proof, we continue with insert_lem below. When 
   trying to prove insert_lem it turns out we need the following 
   two auxilliary lemmas.
*)

Lemma leqb_total : forall m n:nat, leqb m n=false -> leqb n m = true.
induction m.
  intros.
  inversion H.
  intro n.
  case n.
  intros.
  reflexivity.
  intros.
  simpl. 
  apply IHm.
  simpl in H.
  assumption.
Qed.

Lemma insert_hd_lem : forall (a m:nat)(ms:list nat), 
  leqb_hd a ms=true -> leqb a m=true -> leqb_hd a (insert m ms) =true.
  intros a m ms.
  case ms.
    intros.
    simpl.
    assumption.
    (* cons *)
    intros n l.
    simpl.
    intros.
    destruct (leqb m n).
    simpl.
    assumption.
    simpl.
    assumption.
Qed.

(* insert_lem expresses that if we insert an element into a sorted 
   list, we obtain a sorted list.
*)

Lemma insert_lem : forall (m:nat)(ms:list nat), 
  sorted ms=true -> sorted (insert m ms)=true.
(* we proceed by induction over ms: *)
induction ms.
  (* case : ms = nil *)
  intros.
  simpl.
  reflexivity.
  (* case: m:ms *)
  intro s_a_ms.
  simpl.
  case_eq (leqb m a).
    (* leqb m a = true *)
    intro leqb_m_a.
    simpl.
    change ((leqb m a) && (sorted (a::ms)) = true).
    rewrite leqb_m_a.
    rewrite s_a_ms.
    reflexivity.
    (* leqb m a = false *)
    intro nleqb_m_a.
    simpl.
    simpl in s_a_ms.
    apply andb_true_intro.
    cut (leqb_hd a ms=true /\ sorted ms = true).
    intros.
    destruct H as [l s].
    split.
    apply insert_hd_lem.
    exact l.
    apply leqb_total.
    exact nleqb_m_a.
    apply IHms.
    exact s.
    apply andb_prop.
    exact s_a_ms.
Qed.
    
(* using the previous lemma it is easy to prove our main theorem. *)
Theorem sort_ok : forall ms:list nat,sorted (sort ms)=true.
induction ms.
  (* case ms=nil: *)
  reflexivity.
  (* case a::ms *)
  simpl.
  apply insert_lem.
  exact IHms.
Qed.

(* Is this enough? No, we copuld have implemented a function with the 
   property sort_ok by always returning the empty list. Another 
   important property of a sorting function is that it returns a 
   permutation of the input. We define what a permutation is. Again to 
   simplify or discussion we only do this for list nat. 
*)

(* 

   Permutations

   A list is a permutation of another list if every element appears 
   the same number of times. Hence we define the function count:
*)

Fixpoint count (n:nat)(ms:list nat) {struct ms} : nat :=
  match ms with
  | nil => 0
  | m::ms' => let cn := count n ms' 
              in if eqnat n m then S cn else cn
  end.

Eval compute in count 1 (2::1::1::nil).
Eval compute in count 2 (2::1::1::nil).

Definition Perm (ns ms:list nat) := forall n:nat,count n ns=count n ms.

(* we establish some basic property of Perm, which will be useful 
   later: *)

Lemma refl_perm : forall ns:list nat,Perm ns ns.
unfold Perm.
intros.
reflexivity.
Qed.

Lemma trans_perm : forall ls ms ns:list nat,Perm ls ms -> Perm ms ns -> Perm ls ns.
unfold Perm.
intros.
  transitivity (count n ms).
  apply H.
  apply H0.
Qed.

Lemma cons_perm : forall (n:nat)(ms ns:list nat),Perm ms ns -> Perm (n::ms) (n::ns).
unfold Perm.
intros.
  simpl.
  rewrite H.
  case (eqnat n0 n).
    reflexivity.
    reflexivity.
Qed.
  
(* perm for sort *)

Lemma insert_perm : forall (ns:list nat)(n:nat), Perm (n::ns) (insert n ns).
induction ns.
  intros.
  apply refl_perm.
  intros.
  simpl.
  case (leqb n a).
    apply refl_perm.
    eapply trans_perm.
    instantiate (1 := a::n::ns).
    unfold Perm.
    intros.
    simpl.
    case (eqnat n0 n).
      case (eqnat n0 a).
      reflexivity.
      reflexivity.
      case (eqnat n0 a).
      reflexivity.
      reflexivity.
    apply cons_perm.
    apply IHns.
Qed.

Theorem sort_perm : forall ms:list nat,Perm ms (sort ms).
induction ms.
  apply refl_perm.
  eapply trans_perm.
    apply cons_perm.
    apply IHms.
    simpl.
    apply insert_perm.
Qed.

End Lists.

