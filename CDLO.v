Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relations.
Require Import Coq.Arith.EqNat.

Record CDLO :=
{
  lt : relation nat;
  strict_lt : StrictOrder lt;
  dense_lt : forall x y:nat, lt x y -> {z:nat & lt x z /\ lt z y};
  unbounded_above : forall x:nat, {y:nat & lt x y};
  unbounded_below : forall x:nat, {y:nat & lt y x}
}.

Lemma least : forall A:Type, (forall n m : A, {n = m} + {n <> m}) -> forall f:nat -> A, forall a:A, forall n:nat, option {k:nat & k < n /\ f k = a}.
intros.
induction n.
apply None.
destruct IHn as [[k [H0 H1]]|].
constructor 1.
exists k.
split; auto with *.
destruct (X (f n) a).
constructor 1.
exists n.
split; auto with *.
constructor 2.
Optimize Proof.
Show Proof.
Defined.


Lemma option_nat_eq_dec : forall n m : option nat, {n = m} + {n <> m}.
intros.
destruct n.
all: destruct m.
all: (constructor 2; intro H; inversion H; easy) || (constructor 1; easy) || (try destruct (PeanoNat.Nat.eq_dec n n0) as [H|H]; tryif rewrite H then (constructor 1; easy) else (constructor 2; intro H'; inversion H'; easy)).
Optimize Proof.
Defined.

Lemma BackAndForth : forall P Q:CDLO, forall i:nat, (nat -> option nat) * (nat -> option nat).
intros P Q i.
destruct P as [ltP].
destruct Q as [ltQ].
destruct strict_lt0.
destruct strict_lt1.
cbv in *.
induction i.
split.
constructor 2.
constructor 2.
destruct IHi as [f g].
split.
intro x.
destruct (f x) eqn:Ef.
constructor 1.
apply n.
destruct (least _ option_nat_eq_dec g (Some x) x) as [[k [H0 H1]]|].
apply (Some k).
apply None.
intro x.
destruct (g x) eqn:Ef.
constructor 1.
apply n.
destruct (least _ option_nat_eq_dec f (Some x) x) as [[k [H0 H1]]|].
apply (Some k).
apply None.
Optimize Proof.
Defined.

Definition BackAndForth_fst (P Q:CDLO) (i:nat) : (nat -> option nat) := fst (BackAndForth P Q i).
Definition BackAndForth_snd (P Q:CDLO) (i:nat) : (nat -> option nat) := snd (BackAndForth P Q i).


