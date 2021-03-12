Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Import Psatz.

Definition divides(a b:nat) := {k:nat & a * k = b}.
Definition isPrime(n:nat) := forall a b:nat, (divides n (a * b)) -> ((divides n a)+(divides n b)).

Definition add_comm
     : forall n m : nat, n + m = m + n.
intro n.
destruct n.
all: intro m.
2: generalize n; clear n.
all: induction m.
reflexivity.
simpl.
rewrite <- IHm.
simpl; reflexivity.
simpl.
induction n.
reflexivity.
simpl.
rewrite IHn.
reflexivity.
intro n.
simpl.
rewrite <- IHm.
simpl.
induction n.
simpl.
reflexivity.
rewrite IHm.
simpl.
rewrite IHn.
rewrite <- IHm.
simpl.
reflexivity.
Defined.

Lemma add_comm_assoc : forall a b c:nat, (a + (b + c)) = (b + (a + c)).
intro a.
induction a.
all: simpl; try reflexivity.
intros b c.
rewrite (add_comm b (S _)).
simpl.
rewrite <- (add_comm b (_ + _)).
rewrite IHa.
reflexivity.
Defined.

Lemma add_assoc : forall a b c:nat, (a + (b + c)) = a + b + c.
intro a.
induction a.
all: simpl; try reflexivity.
intros b c.
rewrite IHa.
reflexivity.
Defined.

Definition mul_comm
     : forall n m : nat, n * m = m * n.
intro n.
destruct n.
all: intro m.
2: generalize n; clear n.
all: induction m.
reflexivity.
simpl.
rewrite <- IHm.
simpl; reflexivity.
simpl.
induction n.
reflexivity.
simpl.
apply IHn.
intro n.
transitivity ((S n * m) + (S n)).
2: transitivity ((m * (S n)) + (S n)).
2: rewrite IHm; reflexivity.
all: simpl.
all: repeat rewrite (add_comm _ (S _)).
all: simpl.
2:reflexivity.
induction n.
all: simpl.
reflexivity.
repeat rewrite (add_comm _ (S _)).
rewrite IHn.
repeat rewrite (add_comm _ (S _)).
simpl.
rewrite (add_comm _ m).
rewrite add_comm_assoc.
reflexivity.
Defined.

Inductive Even : nat -> Type :=
|EO : Even 0
|ES : forall n:nat, Odd n -> Even (S n)
with Odd : nat -> Type :=
|OS : forall n:nat, Even n -> Odd (S n).


Fixpoint twoDividesEven1(n:nat)(H:Even n) : (divides 2 n) :=
match H with
 | EO => existT (fun k : nat => 2 * k = 0) 0 eq_refl
 | ES n0 o =>
     match o with
     | OS n1 e =>
         let (x, e0) := twoDividesEven1 n1 e in
         existT (fun k : nat => 2 * k = S (S n1)) (S x)
           (eq_ind_r (fun n2 : nat => n2 = S (S n1))
              (eq_ind_r (fun n2 : nat => S (S n2) = S (S n1))
                 (eq_ind_r (fun n2 : nat => S (S n2) = S (S n1)) eq_refl e0) (mul_comm x 2))
              (mul_comm 2 (S x)))
     end
 end.

Fixpoint twoDividesEven2(n:nat)(H:divides 2 n) : (Even n).
destruct H.
induction e.
induction x.
constructor 1.
simpl.
repeat progress (try rewrite (add_comm _ 0); simpl;
                 try rewrite (add_comm _ (S _)); simpl).
constructor 2.
constructor 1.
simpl in IHx.
repeat progress (try rewrite (add_comm _ 0) in IHx; simpl in IHx;
                 try rewrite (add_comm _ (S _)) in IHx; simpl in IHx).
apply IHx.
Defined.

Lemma EvenOrOddS : forall n:nat, (Even n + Odd n) -> (Even (S n) + Odd (S n)).
intros.
destruct H.
constructor 2.
constructor 1.
apply e.
constructor 1.
constructor 2.
apply o.
Defined.


Fixpoint EvenOrOdd(n:nat) : Even n + Odd n :=
match n with
 | 0 => inl EO
 | S k => EvenOrOddS _ (EvenOrOdd k)
end.

Lemma add_commS : forall n m:nat, S (S (n + m)) = S n + S m.
simpl.
intros.
rewrite (add_comm _ (S _)).
simpl.
rewrite (add_comm n m).
reflexivity.
Defined.


Lemma timesS : forall a b:nat, S ((a * b) + a + b) = (S a) * (S b).
simpl.
intros.
rewrite (mul_comm _ (S _)).
simpl.
rewrite (mul_comm b a).
rewrite (add_comm _ (a * b)).
rewrite (add_comm_assoc ).
rewrite (add_comm b a).
rewrite (add_assoc ).
reflexivity.
Defined.

Fixpoint OddEvenPlus{a b:nat}(Ha : Even a)(Hb : Odd b) {struct Hb}: (Odd (a + b)) := 
match Ha with
 |EO => @eq_rect nat b Odd Hb (0 + b) eq_refl
 |ES n o => match Hb with
            |OS m e => 
                   eq_rect _ _ (@eq_rect nat (S (S (m + n))) Odd (OS (S (m + n)) (ES (m + n) (EvenOddPlus e o))) (S (S (n + m)))
    (f_equal S (f_equal S (add_comm m n)))) _ (add_commS _ _)
            end
end
with EvenOddPlus{a b:nat}(Ha : Even a)(Hb : Odd b) {struct Ha}: (Odd (a + b)) := 
match Ha with
 |EO => @eq_rect nat b Odd Hb (0 + b) eq_refl
 |ES n o => match Hb with
            |OS m e => 
                   eq_rect _ _ (@eq_rect nat (S (S (m + n))) Odd (OS (S (m + n)) (ES (m + n) (OddEvenPlus e o))) (S (S (n + m)))
    (f_equal S (f_equal S (add_comm m n)))) _ (add_commS _ _)
            end
end.

Definition EvenTimes{a:nat}(b:nat)(Ha : Even a) : (Even (a * b)).
apply twoDividesEven2.
destruct (twoDividesEven1 _ Ha).
induction e.
exists (x * b).
simpl.
repeat (rewrite (add_comm _ 0); simpl).
repeat (rewrite (mul_comm _ b); simpl).
induction b.
all: simpl.
reflexivity.
rewrite add_comm_assoc.
rewrite <- add_assoc.
rewrite IHb.
repeat rewrite add_assoc.
reflexivity.
Defined.

Fixpoint EvenEvenPlus{a b:nat}(Ha : Even a)(Hb : Even b) {struct Ha}: (Even (a + b)) :=
match Ha with
 |EO => @eq_rect nat b Even Hb (0 + b) eq_refl
 |ES n On => match Hb with
             |EO => let p : (S n) = (S n) + 0 := eq_sym (add_comm (S n) 0) in
                    @eq_rect nat (S n) Even (ES _ On) ((S n) + 0) p
             |ES m Om => let p : (S (S (n + m))) = (S n + S m) := add_commS _ _ in
                          eq_rect _ Even (ES _ (OS _ (OddOddPlus On Om))) _ p
             end
end
with
OddOddPlus{a b:nat}(Ha : Odd a)(Hb : Odd b) {struct Ha}: (Even (a + b)) :=
match Ha with
 |OS n En => match Hb with
             |OS m Em => let p : (S (S (n + m))) = (S n + S m) := add_commS _ _ in
                          eq_rect _ Even (ES _ (OS _ (EvenEvenPlus En Em))) _ p
             end
end.

Definition OddOddTimes{a b:nat}(Ha : Odd a)(Hb : Odd b) : (Odd (a * b)) := 
match Ha with
|OS n En => match Hb with
            |OS m Em => let p : S _ = _ := timesS _ _ in  
                        eq_rect _ Odd (OS _ (EvenEvenPlus (EvenEvenPlus (EvenTimes _ En) En) Em)) _ p
            end
end.

Lemma NotBothEvenOdd : forall n:nat, Even n -> Odd n -> False.
induction n.
all: intros.
inversion H0.
inversion H.
inversion H0.
induction H3.
induction H1.
apply (IHn H4 H2).
Defined.

Theorem twoIsPrime : isPrime 2.
intros a b X.
destruct (EvenOrOdd a).
constructor 1.
apply (twoDividesEven1 _ e).
constructor 2.
destruct (EvenOrOdd b).
apply (twoDividesEven1 _ e).
assert (EX := twoDividesEven2 _ X).
assert (OX := OddOddTimes o o0).
destruct (NotBothEvenOdd _ EX OX).
Defined.

(*Definition Prime := @sigT nat isPrime.*)
Definition Prime := {n:nat & isPrime n}.

Example TwoPrime : Prime := existT isPrime 2 twoIsPrime.

Theorem Grothendieck : (isPrime 51) -> False.
unfold isPrime.
simpl.
intro H.
destruct (H 3 17 (existT _ 1 eq_refl)) as [[k ?H]|[k ?H]].
all: induction k.
all: simpl in H0.
all: try repeat rewrite (add_comm _ (S _)) in H0.
all: inversion H0.
Defined.


Theorem rootPrime : forall p:nat, (forall n:nat, ((S (S (n))) * (S (S (n)))) <= p -> (divides (S (S (n))) p) -> False) -> (isPrime p).
Proof with (simpl in *; try ((constructor 1; (lia || nia || psatz nat 2)) || (constructor 2; (lia || nia || psatz nat 2)))).
unfold isPrime, divides.
intros.
destruct H0.
all: destruct a...
all: destruct b...
all: destruct x...
all: try induction a...
all: try induction b...
all: try induction x...
all: rewrite (mul_comm p _) in e...
all: induction e...
