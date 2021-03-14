Require Import Coq.Arith.PeanoNat.

Definition power := 
fix power (n m : nat) {struct m} : nat := match m with
                                        | 0 => 1
                                        | S p => n * power n p
                                        end.

Notation "x ^ y" := (power x y).

Theorem power_thrm : forall b c a:nat, a ^ (b + c) = (a ^ b) * (a ^ c).
induction b.
all: induction c.
all: intro a.
all: simpl.
all: try easy.
rewrite <- plus_n_O.
rewrite <- (mult_n_Sm _ 0).
rewrite <- mult_n_O.
simpl.
easy.
rewrite <- plus_n_Sm.
simpl.
rewrite IHb.
Search "*".
repeat rewrite Nat.mul_assoc.
rewrite (Nat.mul_comm (a * (a ^ b)) a).
repeat rewrite Nat.mul_assoc.
trivial.
Optimize Proof.
Defined.