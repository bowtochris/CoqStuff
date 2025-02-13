Require Import Coq.Arith.PeanoNat.

Definition twin_odd(p:nat * nat) : Prop := let n := fst p in
                                           let m := snd p in
                                           Nat.Odd n /\ Nat.Odd m /\ n < m /\ forall k, n < k < m -> ~ Nat.Odd k.

Example three_five : twin_odd (3, 5).
repeat split.
all: simpl.
exists 1; simpl; easy.
exists 2; simpl; easy.
repeat (tryif constructor 1 then easy else constructor 2).
intros.
destruct H.
intro H1.
destruct k.
inversion H.
destruct k.
inversion H.
inversion H3.
destruct k.
inversion H.
inversion H3.
inversion H5.
destruct k.
inversion H.
inversion H3.
inversion H5.
inversion H7.
destruct k.
eapply (Nat.Even_Odd_False 4 _ H1).
clear H.
clear H1.
induction k.
apply (Nat.lt_irrefl _ H0).
apply IHk.
apply (Nat.lt_succ_l _ _ H0).
Unshelve.
exists 2; simpl; easy.
Defined.

Definition infinitelyManyP{T:Type}(P:T -> Prop) := {f:nat -> T & forall n:nat, P (f n) /\ forall a b:nat, f a = f b -> a = b}.

Theorem infinitelyManyTwinOdds : infinitelyManyP twin_odd.
exists (fun x:nat => (2 * x + 1, 2 * (S x) + 1)).
intro.
split.
unfold twin_odd.
unfold fst.
unfold snd.
repeat split.
exists n; easy.
exists (S n); easy.
apply Nat.add_lt_mono_r.
apply Nat.mul_lt_mono_pos_l.
repeat (tryif constructor 1 then easy else constructor 2).
repeat (tryif constructor 1 then easy else constructor 2).
intros.
destruct H.
intro F.
inversion F.
symmetry in H1.
destruct H1.
eremember ((proj2 (Nat.mul_lt_mono_pos_l _ _ _ _)) (proj2 (Nat.add_lt_mono_r _ _ _) H)).
eremember ((proj2 (Nat.mul_lt_mono_pos_l _ _ _ _)) (proj2 (Nat.add_lt_mono_r _ _ _) H0)).
destruct (Nat.lt_exists_pred _ _ l) as [z].
destruct H1.
symmetry in H1.
destruct H1.
unfold "<" in l.
remember (Nat.le_lt_trans _ _ _ l l0).
apply (Nat.lt_irrefl _ l1).
intros.
remember (proj1 ((proj1 (pair_equal_spec _ _ _ _ )) H)).
eapply ((proj1 (Nat.mul_cancel_l _ _ _ _)) ((proj1 (Nat.add_cancel_r _ _ _)) e)).
Unshelve.
3: easy.
1,2: repeat (tryif constructor 1 then easy else constructor 2).
Defined.
