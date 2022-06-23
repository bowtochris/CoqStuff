Require Import Coq.Lists.List.

Definition gameStrat(T:Type) : Type := (T -> list T) * (T -> list T).

Definition winningStrat{T:Type}(G : gameStrat T) : Prop :=
let f := fst G in
let g := snd G in
forall x y:T, (In x (f y)) \/ (In y (g x)).

Fixpoint list_le_nat(n:nat) : list nat :=
match n with
|0 => 0 :: nil
|S k => S k :: list_le_nat k
end.

Lemma natStrat : gameStrat nat.
split.
all: apply list_le_nat.
Defined.

Lemma nat_le_list_le : forall x y : nat, le x y -> In x (list_le_nat y).
intros.
cbv.
induction H.
destruct x; constructor 1; reflexivity.
constructor 2.
apply IHle.
Defined.

Lemma natWins : winningStrat natStrat.
unfold winningStrat. 
intros x y.
destruct (PeanoNat.Nat.le_ge_cases x y).
constructor 1.
apply nat_le_list_le.
apply H.
constructor 2.
apply nat_le_list_le.
apply H.
Defined.

Definition isCountable(T:Type) := {f:T -> nat & {g:nat -> T & (forall x:_, x = f (g x)) * (forall x:_, x = g (f x))}}%type.

Lemma countStrat : forall T:Type, isCountable T -> gameStrat T.
intros.
destruct X as [f [g [Hf Hg]]].
split.
all: apply (fun q:T => map g (list_le_nat (f q))).
Defined.

Lemma nat_le_list_le_count :  forall T:Type, forall f : T -> nat, forall g : nat -> T, forall Hf : forall x : nat, x = f (g x), forall Hg : forall x : T, x = g (f x), forall x y : T, le (f x) (f y) -> In x (map g (list_le_nat (f y))).
intros.
unfold map.
unfold list_le_nat.
induction H.
destruct (f x) eqn:e ; constructor 1.
1,2: rewrite <- e.
1,2: symmetry; apply Hg.
constructor 2.
apply IHle.
Defined.

Lemma countWins : forall T:Type, forall H:isCountable T, winningStrat (countStrat T H).
intros T X.
destruct X as [f [g [Hf Hg]]].
unfold winningStrat.
simpl. 
intros x y.
destruct (PeanoNat.Nat.le_ge_cases (f x) (f y)).
constructor 1.
apply (nat_le_list_le_count _ _ _ Hf Hg).
apply H.
constructor 2.
apply (nat_le_list_le_count _ _ _ Hf Hg).
apply H.
Defined.

Require Import Coq.Arith.Even.
Require Import Coq.Arith.Div2.

Lemma double_div : forall n, n = (PeanoNat.Nat.div2 (PeanoNat.Nat.double n)).
induction n.
simpl.
trivial.
simpl.
rewrite PeanoNat.Nat.add_comm.
simpl.
unfold double in IHn.
rewrite <- IHn.
trivial.
Defined.

Lemma not_odd_double : forall n, ~ odd (PeanoNat.Nat.double n).
induction n.
cbv.
intros.
inversion H.
intro H.
unfold double in H.
unfold double in IHn.
simpl in H.
rewrite PeanoNat.Nat.add_comm in H.
simpl in H.
inversion H.
inversion H1.
apply (IHn H3).
Defined.

Definition countableSum : forall A B:Type, isCountable A -> isCountable B -> isCountable (A+B).
intros.
destruct X as [f [g [Hf Hg]]].
destruct X0 as [h [k [Hh Hk]]].
exists (fun s:A+B => match s with
                     |inl a => double (f a)
                     |inr b => S (double (h b))
                     end).

exists (fun n:nat => match even_odd_dec n with
                                        | left e => inl (g (div2 n))
                                        | right o => inr (k (div2 (pred n)))
                                        end).

split.

intro x.
destruct (even_odd_dec x).
rewrite <- Hf.
apply even_double.
apply e.
rewrite <- Hh.
rewrite <- even_double.
destruct o.
rewrite PeanoNat.Nat.pred_succ.
reflexivity.
destruct o.
rewrite PeanoNat.Nat.pred_succ.
apply H.

intros.
destruct x.
destruct (even_odd_dec (PeanoNat.Nat.double (f a))).
rewrite <- double_div.
rewrite <- Hg.
trivial.
destruct (not_odd_double _ o).

destruct (even_odd_dec (S (PeanoNat.Nat.double (h b)))).
inversion e.
destruct (not_odd_double _ H0).
rewrite PeanoNat.Nat.pred_succ.
rewrite <- double_div.
rewrite <- Hk.
trivial.
Defined.

Require Import Coq.Arith.Arith.

Fixpoint filter_up_to_n(n:nat)(P:nat -> bool) : list nat :=
let x := 
 match n with
 |0 => nil
 |S k => filter_up_to_n k P
 end
 in
 match P n with
 |true => n :: x
 |false => x
 end.

Fixpoint least_up_to_n(n:nat)(P:nat -> bool) : option nat :=
let x := 
 match n with
 |0 => None
 |S k => least_up_to_n k P
 end
 in
match x with
|Some y => Some y
|None => match P n with
         |true => Some n
         |false => None
         end
end.

Definition sqrt (n:nat) : nat := match least_up_to_n n (fun x:nat => n <? x * x) with
                                 |Some y => pred y
                                 |None => 0
                                 end.

Compute sqrt 1000.

(*
Definition pairing : nat * nat -> nat := fun p => match p with
                                                            |(j, i) => div2 ((i * i) + (3 * i) + (2 * i * j) + j + (j * j))
                     end.

Definition pair_inv : nat -> nat * nat :=
fun z:nat => 
let w := div2 (pred (sqrt (S (8 * z)))) in
let t := div2 (w * w + w) in
let y := z - t in
let x := w - y in
(x, y).
*)

Fixpoint pair_inv(n:nat) : nat * nat :=
match n with
|0 => (0, 0)
|S k => match pair_inv k with
        |(S k, b) => (k, S b)
        |(0, b) => (S b, 0)
        end
end.

Fixpoint pairing_0 (n:nat) : nat :=
match n with
|0 => 0
|S a => (S (a + (pairing_0 a)))
end.

Fixpoint pairing_unc (a b:nat) : nat :=
match b with
|0 => pairing_0 a
|S m => S (pairing_unc (S a) m)
end.


Definition pairing : nat * nat -> nat := fun p => match p with
                                                            |(i, j) => pairing_unc i j
                     end.

Compute pair_inv (pairing (22, 33)).
Compute pair_inv (pairing (1, 57)).
Compute pair_inv (pairing (57, 1)).
Compute pairing (pair_inv 31337).
Compute pairing (pair_inv 1345).
Compute pairing (pair_inv 666).

Lemma pairing_lemma_S : forall n, forall a, pairing (a, S n) = S n + a + S (pairing (a, n)).
induction n.
intros.
destruct a.
trivial.
simpl.
auto with *.
intros.
simpl in *.
repeat rewrite IHn.
remember (pairing_unc a n) as b.
repeat (rewrite (PeanoNat.Nat.add_comm _ (S _)); simpl).
rewrite (PeanoNat.Nat.add_comm n a).
rewrite (PeanoNat.Nat.add_comm (a + n) _).
reflexivity.
Defined.

Lemma pairing_lemma_a : forall n, pairing (0, n) = n + pairing_0 n.
intros.
induction n.
trivial.
unfold pairing_0.
fold pairing_0.
rewrite <- IHn.
rewrite pairing_lemma_S.
auto with *.
Defined.

Lemma pairing_lemma_b : forall n, pairing (n, 0) = pairing_0 n.
trivial.
Defined.

Lemma pairing_lemma2 : forall a b, 0 = (pairing (a, b)) -> (a, b) = (0, 0).
intros.
destruct b. destruct a.
trivial.
simpl in H.
inversion H.
simpl in H.
inversion H.
Defined.

Lemma f_cancel : forall A B:Type, forall f:A -> B, forall a a':A, a = a' -> f a = f a'.
intros.
destruct H; reflexivity.
Defined.

Lemma div_lemma : forall a b, a = double b-> div2 a = b.
intros.
rewrite H.
symmetry.
apply double_div.
Defined.

Lemma even_lemma : forall a, even (a + a * a).
intros.
destruct (even_odd_dec a).
apply even_even_plus.
3: apply odd_even_plus.
all: try easy.
apply even_mult_r.
apply e.
apply odd_mult.
all: apply o.
Defined.

Lemma even_lemma2 : forall b, even (b + b + b + b + b + b * b).
intros.
destruct (even_odd_dec b).
repeat apply even_even_plus.
7: apply odd_even_plus.
all: try easy.
apply even_mult_r.
apply e.
2: apply odd_mult.
2, 3: apply o.
apply odd_plus_r.
rewrite <- PeanoNat.Nat.add_assoc.
apply even_even_plus.
1,2:apply odd_even_plus.
all: apply o.
Defined.

Lemma even_lemma3 : forall a b, even (b + b + b + b + b + b * b + a + b + a * b + b + a * b + a + a + a + a + a * a).
intros.
destruct (even_odd_dec a);
destruct (even_odd_dec b).
repeat apply even_even_plus.
all: try apply e.
all: try apply e0.
1,2,3,4:apply even_mult_r.
all: try apply e.
all: try apply e0.
all: repeat rewrite <- (PeanoNat.Nat.add_assoc).

apply odd_even_plus.
apply o.
apply odd_plus_l.
apply o.
apply odd_even_plus.
apply o.
apply odd_plus_l.
apply o.
apply odd_even_plus.
apply o.
apply odd_plus_l.
apply odd_mult.
1,2: apply o.
apply even_even_plus.
apply e.
apply odd_even_plus.
apply o.
apply odd_plus_r.
apply even_mult_l.
apply e.
apply odd_plus_l.
apply o.
apply even_even_plus.
apply even_mult_l.
apply e.
apply even_even_plus.
apply e.
apply even_even_plus.
apply e.
apply even_even_plus.
apply e.
apply even_lemma.

apply even_even_plus.
apply e.
apply even_even_plus.
apply e.
apply even_even_plus.
apply e.
apply even_even_plus.
apply e.
apply even_even_plus.
apply e.
apply even_even_plus.
apply even_mult_l.
apply e.
apply odd_even_plus.
apply o.
apply odd_plus_r.
apply e.
apply odd_plus_r.
apply even_mult_r.
apply e.
apply odd_plus_r.
apply e.
apply odd_plus_r.
apply even_mult_r.
apply e.
apply odd_plus_l.
apply o.
apply odd_even_plus.
apply o.
apply odd_plus_l.
apply o.
apply even_lemma.

apply odd_even_plus.
apply o0.
apply odd_plus_l.
apply o0.
apply odd_even_plus.
apply o0.
apply odd_plus_l.
apply o0.
apply odd_even_plus.
apply o0.
apply odd_plus_l.
apply odd_mult.
1,2: apply o0.
apply odd_even_plus.
apply o.
apply odd_plus_l.
apply o0.
apply odd_even_plus.
apply odd_mult.
apply o.
apply o0.
apply odd_plus_l.
apply o0.
apply odd_even_plus.
apply odd_mult.
apply o.
apply o0.
apply odd_plus_l.
apply o.
apply odd_even_plus.
apply o.
apply odd_plus_l.
apply o.
apply even_lemma.
Defined.

Lemma even_lemma4 : forall a, even (a + a * S a + a).
intros.
destruct (even_odd_dec a).

apply even_even_plus.
apply even_even_plus.
apply e.
apply even_mult_l.
1,2: apply e.

apply odd_even_plus.
apply odd_plus_l.
apply o.
apply even_mult_r.
constructor 2.
1,2: apply o.
Defined.

Require Import Psatz.

Ltac fix_arith := 
repeat (
  ((try rewrite (PeanoNat.Nat.add_comm _ 0)); simpl);
  ((try rewrite (PeanoNat.Nat.add_comm _ (S _))); simpl);
  ((try rewrite (PeanoNat.Nat.mul_comm _ 0)); simpl);
  ((try rewrite (PeanoNat.Nat.mul_comm _ (S _))); simpl);
  ((try rewrite (PeanoNat.Nat.mul_add_distr_l); simpl));
  ((try rewrite (PeanoNat.Nat.mul_add_distr_r); simpl));
  ((try rewrite (PeanoNat.Nat.add_assoc)); simpl);
  ((try rewrite (PeanoNat.Nat.mul_assoc)); simpl);
idtac).

Lemma pairing_lemma31 : forall b a, div2 ((b * b) + (3 * b) + (2 * b * a) + a + (a * a)) = (pairing_unc a b).
induction b; induction a; simpl in *.
easy.
all: fix_arith.
rewrite <- IHa.
apply f_cancel.
apply div_lemma.
rewrite double_plus.
rewrite <- even_double.
unfold double.
lia.
apply even_lemma.
fix_arith.
rewrite <- IHb.
apply f_cancel.
symmetry.
apply div_lemma.
simpl.
rewrite double_S.
rewrite <- even_double.
fix_arith.
lia.

apply even_lemma2.

rewrite <- IHb.
apply f_cancel.
symmetry.
apply div_lemma.
simpl.
repeat rewrite double_S.
rewrite <- even_double.
fix_arith.
repeat rewrite (PeanoNat.Nat.mul_comm b a).
repeat apply f_cancel.
repeat rewrite (PeanoNat.Nat.add_comm _ (b * b)).
repeat rewrite <- (PeanoNat.Nat.add_assoc).
repeat apply (f_cancel _ _ (fun x:nat => (b * b) + x)).
fix_arith.

repeat rewrite (PeanoNat.Nat.add_comm _ (a * b)).
repeat rewrite <- (PeanoNat.Nat.add_assoc).
repeat apply (f_cancel _ _ (fun x:nat => (a * b) + x)).
fix_arith.

repeat rewrite (PeanoNat.Nat.add_comm _ (a * a)).
repeat rewrite <- (PeanoNat.Nat.add_assoc).
repeat apply (f_cancel _ _ (fun x:nat => (a * a) + x)).
fix_arith.

repeat rewrite <- (PeanoNat.Nat.add_assoc).
rewrite (PeanoNat.Nat.add_comm b (b + (b + (b + (b + (a + (b + (b + (a + (a + (a + a))))))))))).
rewrite (PeanoNat.Nat.add_comm b (b + (b + (b + (a + (b + (b + (a + (a + (a + a)))))))))).
rewrite (PeanoNat.Nat.add_comm b (b + (b + (a + (b + (b + (a + (a + (a + a))))))))).
rewrite (PeanoNat.Nat.add_comm b (b + (a + (b + (b + (a + (a + (a + a)))))))).
rewrite (PeanoNat.Nat.add_comm b (a + (b + (b + (a + (a + (a + a))))))).
repeat rewrite <- (PeanoNat.Nat.add_assoc).
apply (f_cancel _ _ (fun x:nat => a + x)).
rewrite (PeanoNat.Nat.add_comm b (b + (a + (a + (a + (a + (b + (b + (b + (b + b)))))))))).
rewrite (PeanoNat.Nat.add_comm b (a + (a + (a + (a + (b + (b + (b + (b + b))))))))).
repeat rewrite <- (PeanoNat.Nat.add_assoc).
repeat apply (f_cancel _ _ (fun x:nat => a + x)).
repeat apply (f_cancel _ _ (fun x:nat => b + x)).
trivial.

apply even_lemma3.
Defined.

Lemma pairing_lemma3 : forall a b n, (S n) = (pairing (a, b)) -> (((b = 0) * (n = (pairing (0, pred a)))) + ({c:nat & b = S c} * (n = (pairing (S a, pred b))))).
intros.
destruct b.
constructor 1.
2: constructor 2.
all:split.
trivial.
2: exists b; trivial.
all: unfold pairing in *.
all: repeat rewrite <- pairing_lemma31 in *.
all: symmetry.
all: symmetry in H.
all: apply div_lemma.
all: simpl.
simpl in H.
destruct a.
simpl in *.
inversion H.
simpl in *.
fix_arith.
rewrite PeanoNat.Nat.add_comm in H.
simpl in H.
inversion H.
rewrite <- even_double.
lia.
apply even_lemma4.

assert (H0 : (S b * S b + 3 * S b + 2 * S b * a + a + a * a) = double (S n)).
rewrite <- H.
rewrite <- even_double.
lia.
shelve.
rewrite double_S in H0.
simpl in H0.
inversion H0.
generalize H2.
clear H2.
fix_arith.
intro H2.
inversion H2.
lia.
Unshelve.

fix_arith.
constructor 2.
constructor 1.
constructor 2.
constructor 1.
destruct (even_odd_dec a); destruct (even_odd_dec b).
all: try destruct o as [c].
all: try destruct o0 as [d].
all: fix_arith.
2,3,4:repeat (constructor 2; constructor 1).
all: repeat (apply even_even_plus).
all: try apply even_mult_l.
all: try apply e0.
all: try apply e.
all: try apply H0.
all: try apply H1.
Defined.

Lemma natPairing : isCountable (nat*nat).
exists pairing.
exists pair_inv.
split; intros.
induction x.
trivial.
simpl.
destruct (pair_inv x) eqn:E.
destruct n.
2: (simpl in *;
auto with *;
easy).
destruct n0.
(simpl in *;
auto with *;
easy).
rewrite pairing_lemma_b.
rewrite pairing_lemma_a in IHx.
rewrite IHx.
simpl.
auto with *.
destruct x as [a b].
remember (pairing (a, b)).
generalize Heqn.
generalize b.
generalize a.
clear a b Heqn.
induction n.
intros.
cbv.
apply (pairing_lemma2 _ _ Heqn).
intros.
simpl.
destruct (pair_inv n) as [c d] eqn:E.
assert (H := pairing_lemma3 _ _ _ Heqn).
destruct H.
all: destruct p.
assert (H := IHn _ _ e0).
inversion H.
destruct (eq_sym e).
destruct a.
simpl.
simpl in Heqn.
inversion Heqn.
simpl.
reflexivity.
assert (H := IHn _ _ e).
inversion H.
destruct s.
rewrite e0.
rewrite e0 in Heqn.
rewrite e0 in e.
rewrite e0 in H.
rewrite e0 in H2.
clear b e0.
simpl in *.
reflexivity.
Defined.

Definition countablePairing : forall A B:Type, isCountable A -> isCountable B -> isCountable (A*B).
destruct natPairing as [p [q [Hp Hq]]].
intros.
destruct X as [f [g [Hf Hg]]].
destruct X0 as [h [k [Hh Hk]]].
exists (fun x:A*B => match x with
                     |(a, b) => let i := f a in
                                let j := h b in
                                p (i, j)
                     end).
exists (fun n:nat => match q n with
                     |(a, b) => let i := g a in
                                let j := k b in
                                (i, j)
                     end).
split; intros.
destruct (q x) eqn:E.
simpl.
rewrite <- Hf.
rewrite <- Hh.
rewrite <- E.
apply Hp.
destruct x.
simpl.
rewrite <- Hq.
rewrite <- Hg.
rewrite <- Hk.
reflexivity.
Defined.

Definition countableOption : forall A:Type, isCountable A -> isCountable (option A).
intros.
destruct X as [f [g [Hf Hg]]].
exists (fun x:option A => match x with
                            |None => 0                         
                            |Some a => S (f a)
                          end).
exists (fun n:nat => match n with
                     |0 => None
                     |S k => Some (g k)
                     end).
split; intros; destruct x.
2: rewrite <- Hf.
3: rewrite <- Hg.
all: reflexivity.
Defined.

Require Import Coq.QArith.QArith.

Lemma countablePos : isCountable positive.
exists (fun x:positive => pred (Pos.to_nat x)).
exists (fun x:nat => Pos.of_nat (S x)).
split; intros.
rewrite Nat2Pos.id.
simpl.
reflexivity.
intro H; inversion H.
rewrite <- (S_pred_pos (Pos.to_nat x)).
rewrite Pos2Nat.id.
reflexivity.
destruct x.
1,2:transitivity (Pos.to_nat 1).
1,3,5:cbv.
1,2,3:constructor 1.
all:apply Pos2Nat.inj_lt.
constructor 1.
constructor 1.
Defined.

Lemma countableQ : isCountable Q.
destruct (countablePairing _ _ (countableOption _ (countableSum _ _ countablePos countablePos)) countablePos) as [p [q [Hp Hq]]].
exists (fun x:Q => match x with
                     |(Zpos a) # b => p (Some (inl a), b)
                     |(Zneg a) # b => p (Some (inr a), b)
                     |0 # b => p (None, b)
                     end).
exists (fun n:nat => match q n with
                     |(Some (inl a), b) => (Zpos a) # b
                     |(Some (inr a), b) => (Zneg a) # b
                     |(None, b) => 0 # b
                     end).
split; intros.
destruct (q x) eqn:E.
destruct o.
destruct s.
1,2,3:rewrite <- E; apply Hp.
destruct x.
destruct Qnum.
all: rewrite <- Hq; reflexivity.
Defined.

Theorem Qwins : exists S : gameStrat Q, winningStrat S.
exists (countStrat Q countableQ).
apply countWins.
Defined.
