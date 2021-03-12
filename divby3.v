Require Import Coq.Arith.PeanoNat.
Require Import Lia.

Fixpoint x(n:nat) : nat :=
 match n with
 |0 => 0
 |S k => match k with
         |0 => 1 (*n = 1*)
         |1 => 1 (*n = 2*)
         |S j => (x k) + 2 * (x j)
         end
 end.

Lemma ch3div3_caseSS : forall j:nat, x (S (S (S j))) = (x (S (S j))) + (x (S j)) + (x (S j)).
intros.
unfold x.
progress fold x.
unfold "*".
remember (match j with
| 0 => 1
| S _ =>
    match j with
    | S (S _ as j0) => x j + (x j0 + (x j0 + 0))
    | _ => 1
    end + (x j + (x j + 0))
end ) as a.
remember (match j with
 | S (S _ as j0) => x j + (x j0 + (x j0 + 0))
 | _ => 1
 end) as b.
rewrite Nat.add_0_r.
rewrite Nat.add_assoc.
easy.
Defined.

Lemma ch3div3_lemma : forall n:nat, {a : nat & 3 * a = (x (3 * n))}.
intros.
destruct n.
exists 0; easy.
destruct n.
exists 1; easy.
induction n.
exists 7; easy.
destruct IHn as [a e].
simpl in *.
Search Nat.add.
repeat (try rewrite Nat.add_0_r in *;
        try rewrite plus_Sn_m in *;
        try rewrite <- plus_n_Sm in *).
repeat rewrite Nat.add_assoc in *.
remember (S (n + n + n)) as j.
progress repeat rewrite (ch3div3_caseSS) in *.
remember (x (S j)) as C.
remember (x (S (S j))) as D.
exists (10 * C + 11 * D + 2 * a).
simpl.
repeat rewrite Nat.add_assoc in *.
repeat (try rewrite Nat.add_0_r).
repeat rewrite (Nat.add_comm _ a).
progress repeat rewrite (Nat.add_assoc).
progress rewrite e.
progress repeat rewrite <- (Nat.add_assoc).
progress repeat apply Nat.add_cancel_l.
progress repeat rewrite (Nat.add_assoc).
progress rewrite e.
progress repeat rewrite <- (Nat.add_assoc).
progress repeat apply Nat.add_cancel_l.
progress repeat rewrite (Nat.add_assoc).
progress repeat apply Nat.add_cancel_r.
progress repeat rewrite <- (Nat.add_assoc).
progress repeat rewrite (Nat.add_comm C).
progress repeat rewrite <- (Nat.add_assoc).
progress repeat apply Nat.add_cancel_l.
trivial.
Defined.

Theorem ch3div3_1 : forall n:nat, {a : nat & 3 * a = n} -> {a : nat & 3 * a = (x n)}.
intros.
destruct H as [a ?e].
rewrite <- e.
destruct (ch3div3_lemma a) as [b ?e].
exists b.
apply e0.
Defined.

Theorem ch3div3_2 : forall n:nat, {a : nat & 3 * a = (x n)} -> {a : nat & 3 * a = n}.

