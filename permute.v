Require Import Coq.Lists.List.
Require Import Coq.Structures.Orders.

Inductive Permutation{X:Type} : list X -> list X -> Prop :=
|perm_refl : forall l:list X, Permutation l l
|perm_sym : forall a b:list X, Permutation a b -> Permutation b a
|perm_trans : forall a b c:list X, Permutation b c -> Permutation a b -> Permutation a c
|perm_cons : forall a b:list X, forall x:X, Permutation a b -> Permutation (x :: a) (x :: b)
|perm_swap : forall a:list X, forall x y:X, Permutation (x :: y :: a) (y :: x :: a).

Lemma Permute_len : forall X:Type, forall a b:list X, Permutation a b -> (length a) = (length b).
intros.
induction H.
all: try (simpl; auto with *).
transitivity (length b).
all: try auto with *.
Defined.

Lemma Permute_append : forall X:Type, forall a a' b b':list X, Permutation a a' -> Permutation b b' -> Permutation (a ++ b) (a' ++ b').
intros X a a' b b' H.
generalize b b'.
clear b b'.
induction H.
all: simpl.
all: intros.
all: try (simpl; auto with *).
all: (repeat (try apply perm_refl; try apply perm_cons; try apply perm_swap)); try progress (apply perm_sym; simpl; auto with *; apply perm_sym); simpl; auto with *.
induction l.
all: try (simpl; auto with *).
all: (repeat (try apply perm_refl; try apply perm_cons; try apply perm_swap)); try progress (apply perm_sym; simpl; auto with *; apply perm_sym); simpl; auto with *.
all: tryif (rename b into a') then (try rename b0 into b) else idtac.
apply perm_sym.
apply IHPermutation.
apply perm_sym.
apply H0.
apply (perm_trans _ (a' ++ b)).
apply IHPermutation1.
apply H1.
apply IHPermutation2.
apply perm_refl.
apply (perm_trans _ (y :: x :: a ++ a')).
repeat apply perm_cons.
2: apply perm_swap.
induction a.
all: try (simpl; auto with *).
all: (repeat (try apply perm_refl; try apply perm_cons; try apply perm_swap)); try progress (apply perm_sym; simpl; auto with *; apply perm_sym); simpl; auto with *.
Defined.

Lemma Permute_In : forall X:Type, forall x:X, forall a a':list X, Permutation a a' -> ((In x a) <-> (In x a')).
intros.
generalize x.
clear x.
induction H.
all: try (simpl; auto with *).
all: try split.
all: intros.
all: try (simpl; auto with *).
all: ((try apply IHPermutation; try apply IHPermutation0; try apply IHPermutation1; try apply IHPermutation2; try apply perm_refl; try apply perm_cons; try apply perm_swap)); try progress (apply perm_sym; simpl; auto with *; apply perm_sym); simpl; auto with *.
apply IHPermutation1.
apply H1.
all: repeat match goal with
    | [ H : _ \/ _ |- _ ] => destruct H
  end.
all: try (simpl; auto with *).
all: repeat constructor 2.
all: try apply IHPermutation.
all: try apply H0.
Defined.





