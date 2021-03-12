Section DEFINITIONS.
 Variable G : Type.
 Variable (gO : G) (gadd gsub: G->G->G) (gopp : G -> G).
 Variable geq : G -> G -> Prop.
 Notation "0" := gO.
 Infix "==" := geq (at level 70).
 Infix "+" := gadd.
 Infix "-" := gsub.
 Notation "- x" := (gopp x).

 Record group_theory : Prop := mk_gt {
    Gadd_0_l : forall x, 0 + x == x;
    Gadd_0_r : forall x, x + 0 == x;
    Gadd_assoc : forall x y z, x + (y + z) == (x + y) + z;
    Gsub_def : forall x y, x - y == x + -y;
    Gopp_def : forall x, x + (- x) == 0
 }.

End DEFINITIONS.

Fixpoint ltT(n m:nat) : Type :=
match n, m with
  |_, 0 => False
  |0, S _ => True
  |S k, S j => ltT k j
end.

Infix "<" := ltT.

Axiom Braid : nat -> Type.
Axiom (Braid_O : forall n:nat, Braid n) (Braid_add Braid_sub: forall n:nat, Braid n->Braid n->Braid n) (Braid_opp : forall n:nat, Braid n -> Braid n).

 Notation "0" := (Braid_O _).
 Infix "+" := (Braid_add _).
 Infix "-" := (Braid_sub _).
 Notation "- x" := (Braid_opp _ x).

Axiom Braid_add_0_l : forall n:nat, forall x:Braid n, 0 + x = x.
Axiom Braid_add_0_r : forall n:nat, forall x:Braid n, x + 0 = x.
Axiom Braid_add_assoc : forall n:nat, forall x:Braid n, forall y z, x + (y + z) = (x + y) + z.
Axiom Braid_sub_def : forall n:nat, forall x:Braid n, forall y, x - y = x + -y.
Axiom Braid_opp_def : forall n:nat, forall x:Braid n, x + (- x) = 0.

Axiom b : forall {n:nat} (m:nat) {_:ltT m n}, Braid n. 
Definition b1 : Braid 3 := b 1.
Axiom Braid_gen_1 : forall n i:nat, (S i) < n -> (b i) + (b (S i)) + (b i) = (b (S i)) + (b i) + (b (S i)).