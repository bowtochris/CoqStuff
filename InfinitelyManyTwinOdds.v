Require Import Coq.Arith.PeanoNat.

Definition consecutive_odd(p:nat * nat) : Prop := let n := fst p in
                                           let m := snd p in
                                           Nat.Odd n /\ Nat.Odd m /\ n < m /\ forall k, n < k < m -> ~ Nat.Odd k.

Definition twin_odd(p:nat * nat) : Prop := let n := fst p in
                                           let m := snd p in
                                           Nat.Odd n /\ Nat.Odd m /\ n + 2 = m.

Lemma tight_lt : forall n m, n < m < n + 2 -> m = n + 1.
intro n.
induction n.
all: intros m H.
simpl in *.
destruct m.
easy.
destruct m.
easy.
destruct H.
destruct (Nat.nlt_0_r _ ((proj2 (Nat.succ_lt_mono _ _)) ((proj2 (Nat.succ_lt_mono _ _)) H0))).
destruct m.
destruct H.
destruct (Nat.nlt_0_r _ H).
destruct H.
simpl in H0.
Search S "<".
rewrite (let f := (fun a b => fun H:(S a < S b) => (proj2 (Nat.succ_lt_mono _ _ )) H) in IHn m (conj (f _ _ H) (f _ _ H0))).
simpl.
easy.
Defined.

Lemma consecutive_odd_iff_twin_odd : forall p, consecutive_odd p <-> twin_odd p.
intros.
destruct p as [n m].
unfold consecutive_odd; unfold twin_odd.
split.
all: intro H.
all: repeat (destruct H as [?H H]).
all: repeat split.
all: simpl in *.
all: try easy.
destruct (Nat.lt_trichotomy (n + 2) m).
destruct H0.
assert ((fun m : nat => n + 2 = 2 * m + 1) (x + 1)).
rewrite H0.
rewrite Nat.mul_add_distr_l.
rewrite Nat.add_shuffle0.
easy.
destruct ((H (n + 2) (conj (Nat.lt_add_pos_r 2 n Nat.lt_0_2) H3)) (ex_intro _ (x + 1) H4)).
destruct H3.
apply H3.
destruct (eq_sym (tight_lt _ _ (conj H2 H3))).
rewrite Nat.add_comm in H1.
simpl in H1.
destruct (Nat.Even_Odd_False _ ((proj2 (Nat.Even_succ _)) H0) H1).
apply (Nat.lt_add_pos_r 2 n Nat.lt_0_2).
intros.
destruct (eq_sym (tight_lt _ _ H)).
rewrite Nat.add_comm.
simpl.
intro F.
Search Nat.Even Nat.Odd.
apply (Nat.Even_Odd_False _ ((proj2 (Nat.Even_succ _)) H0) F).
Defined.

Example three_five : consecutive_odd (3, 5).
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

Theorem infinitelyManyTwinOdds : infinitelyManyP consecutive_odd.
exists (fun x:nat => (2 * x + 1, 2 * (S x) + 1)).
intro.
split.
unfold consecutive_odd.
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
