Axiom fun_ext : forall A:Type, forall B:A -> Type, forall f g:(forall a:A, B a), (f = g) = (forall a:A, f a = g a).

Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Open Scope nat_scope.
Open Scope R.
Theorem fixed_inter : forall f:R -> R, (forall x:R, (0 <= x) -> (x <= 1) ->
                                        (continuity_pt f x /\ (0 <= (f x)) /\ ((f x) <= 1))) -> {x0:R & (x0 = f x0) /\ (0 <= x0) /\ (x0 <= 1)}.
Proof with simpl in *; try easy.
intros.
assert (Hf : (((fun i : nat => f ((fun n : nat => Nat.iter n f ((INR 1) / (INR 2))) i))) = ((fun i : nat => ((fun n : nat => Nat.iter (n + 1) f ((INR 1) / (INR 2))) i))))).
rewrite fun_ext.
intro n.
rewrite Nat.add_comm.
simpl.
trivial.
assert (Hf_ineq : forall n:nat, 0 <= (Nat.iter n f ((INR 1) / (INR 2))) <= 1).
induction n.
simpl.
lra.
simpl.
apply H.
apply IHn.
apply IHn.
destruct (R_complete (fun n:nat => Nat.iter n f ((INR 1) / (INR 2)))).
shelve.
eassert (H0 := @Rle_cv_lim (fun _:_ => 0) _ 0 _ _ _ u).
eassert (H1 := @Rle_cv_lim _ (fun _:_ => 1) _ 1 _ u _).
assert (Hlim := continuity_seq f _ _ (proj1 (H x H0 H1 )) u).
exists x.
all: repeat split.
cbv beta in Hlim.
rewrite Hf in Hlim.
apply (UL_sequence _ _ _ u (CV_shift _ 1 _ Hlim)).
all: auto with *.
Unshelve.
all: try apply Hf_ineq.
all: intro eps.
all: intros.
shelve.
all: exists 0%nat.
all: intros.
all: rewrite R_dist_eq.
all: trivial; auto with *; easy.
Unshelve.
unfold continuity_pt in H...
unfold continue_in in H...
unfold limit1_in in H...
unfold limit_in in H...
unfold D_x in H...
unfold no_cond in H...
unfold R_dist in H...

