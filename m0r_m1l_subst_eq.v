Lemma mul_0_r : forall n : nat, n * 0 = 0.
induction n; simpl.
trivial.
apply IHn.
Optimize Proof.
Defined.

Print mul_0_r.
(*
fun n : nat =>
nat_ind (fun n0 : nat => n0 * 0 = 0) eq_refl (fun (n0 : nat) (IHn : n0 * 0 = 0) => IHn) n
*)

Lemma mul_1_l : forall n : nat, 1 * n = n.
simpl.
induction n; simpl.
trivial.
rewrite IHn.
trivial.
Optimize Proof.
Defined.

Print mul_1_l.

(*
nat_ind (fun n0 : nat => n0 + 0 = n0) eq_refl
  (fun (n0 : nat) (IHn : n0 + 0 = n0) => eq_ind_r (fun n1 : nat => S n1 = S n0) eq_refl IHn) n
*)

Theorem m0r_m1l_subst_eq : (mul_0_r 1) = (mul_1_l 0).
simpl.
trivial.
Optimize Proof.
Defined.

Print m0r_m1l_subst_eq.

(*eq_refl*)