Require Import Coq.Reals.Reals.

Open Scope R.

Theorem HamkinsQverheard9thGradeProblem : forall x:R, x > 0 -> (x + (1/x)) >= 2.
intros.
unfold Rdiv.
rewrite Rmult_1_l.
rewrite <- (Rmult_1_l (x + / x)).
rewrite <- (Rmult_1_l 2).
rewrite Rmult_plus_distr_l.
rewrite <- (Rinv_r x).
rewrite (Rmult_comm x (/ x)).
repeat rewrite (Rmult_assoc (/ x)).
rewrite <- (Rmult_plus_distr_l (/ x)).
apply Rmult_ge_compat_l.
apply (Rgt_ge _ _ (Rlt_gt _ _ (Rinv_0_lt_compat x (Rlt_gt _ _ H)))).
repeat rewrite <- Rinv_r_sym.
repeat rewrite <- Rinv_l_sym.
all: try apply (Rgt_not_eq _ _ H).
fold (Rsqr x).
rewrite (Rmult_comm x 2).
apply Rminus_ge.
rewrite <- Rsqr_1.
rewrite Rplus_comm.
rewrite <- (Rmult_1_r x) at 2.
rewrite (Rmult_comm x 1).
rewrite <- (Rmult_assoc 2 1 x).
rewrite <- Rsqr_minus.
apply Rle_ge.
apply Rle_0_sqr.
Optimize Proof.
Defined.

Print HamkinsQverheard9thGradeProblem.

(*
fun (x : R) (H : x > 0) =>
eq_ind_r (fun r : R => x + r >= 2)
  (eq_ind (1 * (x + / x)) (fun r : R => r >= 2)
     (eq_ind (1 * 2) (fun r : R => 1 * (x + / x) >= r)
        (eq_ind_r (fun r : R => r >= 1 * 2)
           (eq_ind (x * / x) (fun r : R => r * x + r * / x >= r * 2)
              (eq_ind_r (fun r : R => r * x + r * / x >= r * 2)
                 (eq_ind_r (fun r : R => r + / x * x * / x >= / x * x * 2)
                    (eq_ind_r (fun r : R => / x * (x * x) + r >= / x * x * 2)
                       (eq_ind_r (fun r : R => / x * (x * x) + / x * (x * / x) >= r)
                          (eq_ind (/ x * (x * x + x * / x)) (fun r : R => r >= / x * (x * 2))
                             (Rmult_ge_compat_l (/ x) (x * x + x * / x) 
                                (x * 2)
                                (Rgt_ge (/ x) 0
                                   (Rlt_gt 0 (/ x) (Rinv_0_lt_compat x (Rlt_gt 0 x H))))
                                (eq_ind 1 (fun r : R => x * x + r >= x * 2)
                                   (eq_ind_r (fun r : R => x² + 1 >= r)
                                      (Rminus_ge (x² + 1) (2 * x)
                                         (eq_ind 1² (fun r : R => x² + r - 2 * x >= 0)
                                            (eq_ind_r (fun r : R => r - 2 * x >= 0)
                                               ((fun lemma : x * 1 = x =>
                                                 Morphisms.reflexive_proper Rge
                                                   (1² + x² - 2 * x) 
                                                   (1² + x² - 2 * (x * 1))
                                                   (Morphisms.Reflexive_partial_app_morphism
                                                      (Morphisms.reflexive_proper Rminus)
                                                      (Morphisms.eq_proper_proxy (1² + x²))
                                                      (2 * x) (2 * (x * 1))
                                                      (Morphisms.Reflexive_partial_app_morphism
                                                         (Morphisms.reflexive_proper Rmult)
                                                         (Morphisms.eq_proper_proxy 2) x
                                                         (x * 1)
                                                         (RelationClasses.symmetry lemma))) 0
                                                   0 (Morphisms.eq_proper_proxy 0))
                                                  (Rmult_1_r x)
                                                  (eq_ind_r
                                                     (fun r : R => 1² + x² - 2 * r >= 0)
                                                     (eq_ind (2 * 1 * x)
                                                        (fun r : R => 1² + x² - r >= 0)
                                                        (eq_ind (1 - x)²
                                                           (fun r : R => r >= 0)
                                                           (Rle_ge 0 
                                                              (1 - x)² 
                                                              (Rle_0_sqr (1 - x)))
                                                           (1² + x² - 2 * 1 * x)
                                                           (Rsqr_minus 1 x)) 
                                                        (2 * (1 * x)) 
                                                        (Rmult_assoc 2 1 x)) 
                                                     (Rmult_comm x 1))) 
                                               (Rplus_comm x² 1²)) 1 Rsqr_1))
                                      (Rmult_comm x 2)) (x * / x)
                                   (Rinv_r_sym x (Rgt_not_eq x 0 H))))
                             (/ x * (x * x) + / x * (x * / x))
                             (Rmult_plus_distr_l (/ x) (x * x) (x * / x)))
                          (Rmult_assoc (/ x) x 2)) (Rmult_assoc (/ x) x (/ x)))
                    (Rmult_assoc (/ x) x x)) (Rmult_comm x (/ x))) 1
              (Rinv_r x (Rgt_not_eq x 0 H))) (Rmult_plus_distr_l 1 x (/ x))) 2 
        (Rmult_1_l 2)) (x + / x) (Rmult_1_l (x + / x))) (Rmult_1_l (/ x))
*)
