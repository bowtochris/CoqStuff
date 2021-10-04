Require Import Coq.Classes.Equivalence.

Record Magma{M : Set}{meq : M -> M -> Prop}(meq_equiv : Equivalence meq) :=
{
  op : M -> M -> M;
  op_proper : forall a a' b b':M, meq a a' -> meq b b' -> meq (op a b) (op a' b')
}.

Arguments op [M] [meq] [meq_equiv] m.

Definition mk_magma := Build_Magma.

Record Semigroup{M : Set}{meq : M -> M -> Prop}{meq_equiv : Equivalence meq}(U : Magma meq_equiv) :=
{
  op_assoc : forall x y z:M, (op U x (op U y z)) = op U (op U x y) z
}.

Definition mk_semigroup (M : Set) (meq : M -> M -> Prop) (meq_equiv : Equivalence meq)
         (op : M -> M -> M)
         (H: forall a a' b b' : M, meq a a' -> meq b b' -> meq (op a b) (op a' b'))
         (H' : forall x y z:M, (op x (op y z)) = op (op x y) z) :
         Semigroup (mk_magma M meq meq_equiv op H) := Build_Semigroup M meq meq_equiv (mk_magma _ _ _ op H) H'.

Record UMagma{M : Set}{meq : M -> M -> Prop}{meq_equiv : Equivalence meq}(U : Magma meq_equiv) :=
{
  e : M;
  e_id_left  : forall x:M, (op U x e) = x;
  e_id_right : forall x:M, (op U e x) = x
}.

Arguments e [M] [meq] [meq_equiv] [U] u.

Definition mk_umagma (M : Set) (meq : M -> M -> Prop) (meq_equiv : Equivalence meq)
         (op  : M -> M -> M) (e:M)
         (H   : forall a a' b b' : M, meq a a' -> meq b b' -> meq (op a b) (op a' b'))
         (H'  : forall x:M, (op x e) = x)
         (H'' : forall x:M, (op e x) = x) :
         UMagma (mk_magma M meq meq_equiv op H) := Build_UMagma M meq meq_equiv (mk_magma _ _ _ op H) e H' H''.

Record Quasigroup{M : Set}{meq : M -> M -> Prop}{meq_equiv : Equivalence meq}(U : Magma meq_equiv) :=
{
  div_left : M -> M -> M;
  div_right : M -> M -> M;
  div_left_proper : forall a a' b b':M, meq a a' -> meq b b' -> meq (div_left a b) (div_left a' b');
  div_right_proper : forall a a' b b':M, meq a a' -> meq b b' -> meq (div_right a b) (div_right a' b');
  cancel_div_left  : forall x y:M, (op U x (div_left x y)) = y;
  cancel_div_right : forall x y:M, (op U (div_right x y) x) = y
}.

Definition mk_quasigroup (M : Set) (meq : M -> M -> Prop) (meq_equiv : Equivalence meq)
         (op  : M -> M -> M) (div_left  : M -> M -> M) (div_right  : M -> M -> M) 
         (H   : forall a a' b b' : M, meq a a' -> meq b b' -> meq (op a b) (op a' b'))
         (H'  : _)
         (H'' : _) 
         (H''' : _) 
         (H'''' : _) :
         Quasigroup (mk_magma M meq meq_equiv op H) := Build_Quasigroup M meq meq_equiv (mk_magma _ _ _ op H) div_left div_right H' H'' H''' H''''.

Record Group{M : Set}{meq : M -> M -> Prop}{meq_equiv : Equivalence meq}{U : Magma meq_equiv}
             (S:Semigroup U)(Q:Quasigroup U)(UM:UMagma U):= {}.

Definition mk_group (M : Set) (meq : M -> M -> Prop) (meq_equiv : Equivalence meq)
         (op  : M -> M -> M) (inv  : M -> M) (e:M)
         (H   : forall a a' b b' : M, meq a a' -> meq b b' -> meq (op a b) (op a' b'))
         (H0  : _)
         (H1 : _) 
         (H2 : _) 
         (H3 : _) 
         (H4 : _) 
         (H5 : _) 
         (H6 : _) :
         Group (mk_semigroup M meq meq_equiv op H H0) (mk_quasigroup M meq meq_equiv op (fun x:M => fun y:M => op (inv x) y) (fun x:M => fun y:M => op y (inv x)) H H1 H2 H3 H4) (mk_umagma M meq meq_equiv op e H H5 H6) :=
           Build_Group M meq meq_equiv (mk_magma _ _ _ op H) _ _ _.

Record Monoid{M : Set}{meq : M -> M -> Prop}{meq_equiv : Equivalence meq}{U : Magma meq_equiv}
             (S:Semigroup U)(UM:UMagma U):= {}.

Definition mk_monoid (M : Set) (meq : M -> M -> Prop) (meq_equiv : Equivalence meq)
         (op  : M -> M -> M) (e:M)
         (H   : forall a a' b b' : M, meq a a' -> meq b b' -> meq (op a b) (op a' b'))
         (H0  : _)
         (H1 : _) 
         (H2 : _) :
         Monoid (mk_semigroup M meq meq_equiv op H H0) (mk_umagma M meq meq_equiv op e H H1 H2) :=
           Build_Monoid M meq meq_equiv (mk_magma _ _ _ op H) _ _.

Record CommutativeMonoid{M : Set}{meq : M -> M -> Prop}{meq_equiv : Equivalence meq}{U : Magma meq_equiv}
             {S:Semigroup U}{UM:UMagma U}(MM:Monoid S UM):=
{
  op_comm : forall x y:M, op U x y = op U y x
}.

Definition mk_comm_monoid (M : Set) (meq : M -> M -> Prop) (meq_equiv : Equivalence meq)
         (op  : M -> M -> M) (e:M)
         (H   : forall a a' b b' : M, meq a a' -> meq b b' -> meq (op a b) (op a' b'))
         (H0  : _)
         (H1 : _) 
         (H2 : _) 
         (H3 : _) :
         CommutativeMonoid (mk_monoid M meq meq_equiv op e H H0 H1 H2) :=
           Build_CommutativeMonoid M meq meq_equiv (mk_magma _ _ _ op H) _ _ _ H3.

Theorem EckmannHiltonE : forall M:Set, forall X Y:Magma (@eq_equivalence M), forall UX:UMagma X, forall UY:UMagma Y,
 (forall a b c d:M, (op Y (op X a b) (op X c d)) = (op X (op Y a c) (op Y b d))) ->
 (e UX = e UY).
intros.
all: destruct X, Y, UX, UY; simpl in *.
assert (He := H e0 e1 e1 e0).
rewrite (e_id_right0 e1) in He.
rewrite (e_id_left0 e1) in He.
rewrite (e_id_left1 e0) in He.
rewrite (e_id_right1 e0) in He.
rewrite (e_id_left1 e1) in He.
rewrite (e_id_left0 e0) in He.
symmetry in He.
apply He.
Defined.

Theorem EckmannHiltonOp : forall M:Set, forall X Y:Magma (@eq_equivalence M), forall UX:UMagma X, forall UY:UMagma Y,
 (forall a b c d:M, (op Y (op X a b) (op X c d)) = (op X (op Y a c) (op Y b d))) ->
 (forall a b:M, op X a b = op Y a b).
intros.
assert (H' := EckmannHiltonE M X Y UX UY H).
all: destruct X, Y, UX, UY; simpl in *.
destruct H'.
assert (Hop := H a e0 e0 b).
rewrite (e_id_right0 b) in Hop.
rewrite (e_id_left0 a) in Hop.
rewrite (e_id_right1 b) in Hop.
rewrite (e_id_left1 a) in Hop.
symmetry in Hop.
apply Hop.
Defined.

Theorem EckmannHilton : forall M:Set, forall X Y:Magma (@eq_equivalence M), forall UX:UMagma X, forall UY:UMagma Y,
 (forall a b c d:M, (op Y (op X a b) (op X c d)) = (op X (op Y a c) (op Y b d))) ->
  {H:_ & CommutativeMonoid (mk_monoid M _ _ (op X) (e UX) (op_proper _ X) H (e_id_left _ UX) (e_id_right _ UX))}.
intros.
assert (H' := EckmannHiltonE M X Y UX UY H).
assert (H'' := EckmannHiltonOp M X Y UX UY H).
all: destruct X, Y, UX, UY; simpl in *.
destruct H'.
assert (H''' : forall a b c d : M, op0 (op0 a b) (op0 c d) = op0 (op0 a c) (op0 b d)).
intros.
rewrite (H'' a c).
rewrite (H'' b d).
rewrite (H'' (op0 a b) _).
apply H.
clear H H''.
rename H''' into H.
clear op1 op_proper1 e_id_left1 e_id_right1.
assert (H0 : forall x y z : M, op0 x (op0 y z) = op0 (op0 x y) z).
intros.
assert (Hass := H x y e0 z).
rewrite e_id_left0 in Hass.
rewrite e_id_right0 in Hass.
symmetry in Hass.
apply Hass.
exists H0.
apply mk_comm_monoid.
intros.
simpl.
assert (Hcomm := H e0 x y e0).
repeat rewrite e_id_left0 in Hcomm.
repeat rewrite e_id_right0 in Hcomm.
apply Hcomm.
Defined.


