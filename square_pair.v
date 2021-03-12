Require Import Program Arith List.

Fixpoint the_first_n_odd_numbers(n:nat) : list nat :=
match n with
  |0 => nil
  |S k => (S (2 * k)) :: (the_first_n_odd_numbers k)
end.
Open Scope list.
Example tf5on : the_first_n_odd_numbers 5 = (9 :: 7 :: 5 :: 3 :: 1 :: nil).
compute; trivial.
Defined.


Fixpoint sum(x:list nat) : nat :=
match x with
  |nil => 0
  |y :: xs => y + (sum xs)
end.

Fixpoint getLast{A:Type}(x:list A) : (list A) * (option A) :=
match x with
  |nil => (nil, None)
  |y :: nil => (nil, Some y)
  |y :: xs => let p := getLast xs in
               (y :: fst p, snd p)
end.

Lemma list_pair_matching : forall A:Type, forall B B': (list A) -> Type, forall F: B nil, forall F': B' nil, forall G:(forall y:A, forall ys:list A, B (y :: ys)), forall G':(forall y:A, forall ys:list A, B' (y :: ys)), forall xs:list A, 
   (match xs with
    |nil => (F, F')
    |y :: ys => (G y ys, G' y ys)
    end) = (match xs with
    |nil => F
    |y :: ys => G y ys
    end,match xs with
    |nil => F'
    |y :: ys => G' y ys
    end).
intros.
destruct xs.
all: trivial.
Defined.

Lemma length_lemma : forall n0:_, forall xs:_,
                     (fix length (l : list nat) : nat := match l with
                                       | nil => 0
                                       | _ :: l' => S (length l')
                                       end) (fst (getLast (n0 :: xs))) =
                     (fix length (l : list nat) : nat := match l with
                                       | nil => 0
                                       | _ :: l' => S (length l')
                                       end) xs.
intros.
generalize n0.
clear n0.
induction xs.
simpl.
trivial.
simpl in *.
rewrite IHxs.
trivial.
Defined.

Program Fixpoint pairUp(x:list nat)  {measure (length x)}: list (nat * nat) :=
match x with
  |nil => nil
  |y :: nil => (y, 0) :: nil
  |y :: xs => let p := getLast xs in
               match p with
                |(ys, None) => nil (*impossible*)
                |(ys, Some z) => (y, z) :: (pairUp ys)
                end
end.

Next Obligation.
clear H.
destruct xs.
simpl in *.
inversion Heq_p.
unfold getLast in Heq_p.
rewrite (list_pair_matching nat (fun _:_ => list nat) (fun _:_ => option nat) nil (Some n) _ _ xs) in Heq_p.
inversion Heq_p.
fold (@getLast nat) in *.
destruct xs.
all: unfold length in *.
auto with *.
rewrite length_lemma.
auto with *.
Defined.

Fixpoint doublesHelper (n m:nat) : list nat :=
match n with
  |0 => nil
  |1 => m :: nil
  |S (S k) => (2 * m) :: (doublesHelper k m)
end.

Definition doubles(n:nat) := doublesHelper n n.
Example d5 : doubles 5 = (10 :: 10 :: 5 :: nil).
compute; trivial.
Defined.

Theorem pairUpSum : forall n:nat, (map (fun p:_ => match p with |(a,b) => a + b end) (pairUp (the_first_n_odd_numbers n))) = doubles n.
Proof with simpl.
intro n.
destruct n.
compute...
trivial.
destruct n.
compute.
trivial.
compute.
repeat rewrite (Nat.add_comm _ 0)...
repeat rewrite (Nat.add_comm _ (S _))...
induction n...
trivial.


Theorem squareThm : forall n:nat, (sum (the_first_n_odd_numbers n)) = n*n.