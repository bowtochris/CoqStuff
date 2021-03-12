Require Import Coq.Reals.Reals.
Require Import Coq.setoid_ring.Ring_theory.
Require Import Ring Ring_tac.
Require Import Coq.Classes.RelationClasses.
Require Import Relation_Definitions Setoid.


Example whitehead {R : Type} {rO rI : R} {radd rmul rsub : R -> R -> R} 
         {ropp : R -> R} {req : R -> R -> Prop} (req_eq : Equivalence req)
         (Rth : ring_theory rO rI radd rmul rsub ropp req) (Rth_proper : ring_eq_ext radd rmul ropp req):
         forall x : R, req (rmul (rmul (radd rI rI) x) (radd x rI)) (radd (rmul (radd rI rI) (rmul x x)) (rmul (radd rI rI) x)).
intros.
apply (@Equivalence_Transitive _ _ req_eq _ _ _ (Rmul_comm Rth (rmul (radd rI rI) x) (radd x rI))).
apply (@Equivalence_Transitive _ _ req_eq _ _ _ (Rdistr_l Rth _ _ _)).
apply (radd_ext Rth_proper).
apply (@Equivalence_Transitive _ _ req_eq _ _ _ (Rmul_assoc Rth _ _ _)).
apply (@Equivalence_Transitive _ _ req_eq _ _ _ (Rmul_comm Rth _ x)).
apply (@Equivalence_Transitive _ _ req_eq _ _ _ (Rmul_assoc Rth _ _ _)).
apply (Rmul_comm Rth (rmul x x) (radd rI rI)).
apply (Rmul_1_l Rth _).
Defined.

Open Scope R_scope.

Example whitehead_real : forall x : R, ((2 * x) * (x + 1)) = ((2 * (x * x)) + (2 * x)).
apply (whitehead (Eqsth _) RTheory).
split; cbv.
all: intros.
all: rewrite H.
3: reflexivity.
all: rewrite H0.
all: reflexivity.
Defined.