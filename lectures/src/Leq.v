Section Leq.

Load Arith.
Notation "m <= n" := (leq m n).

Fixpoint leqb (m n : nat) {struct m} : bool :=
  match m with
  | 0 => true
  | S m => match n with 
           | 0 => false
           | S n => leqb m n
           end
  end.

Axiom leq1 : forall m n : nat, leqb m n = true -> m <= n.
Axiom leq2 : forall m n : nat,  m <= n -> leqb m n = true.

Theorem total : forall m n : nat, m <= n \/ n <= m.
intro m.
induction m.
intro n.
left.
exists n.
simpl.
apply plus_n_O.
intro n.
induction n.
right.
exists (S m).
apply plus_n_O.
destruct (IHm n) as [l | r].
left.
destruct l as [k p].
unfold leq.
exists k.
rewrite p.
rewrite<- plus_n_Sm.
reflexivity.
right.
destruct r as [k p].
exists k.
rewrite p.
rewrite<- plus_n_Sm.
reflexivity.
Qed.





