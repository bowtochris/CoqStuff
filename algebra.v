Require Import Coq.Classes.Equivalence.

Record Magma{M : Set}{meq : M -> M -> Prop}(meq_equiv : Equivalence meq) :=
{
  op : M -> M -> M;
  op_proper : forall a a' b b':M, meq a a' -> meq b b' -> meq (op a b) (op a' b')
}.

Definition mk_magma := Build_Magma.

Record Semigroup{M : Set}{meq : M -> M -> Prop}{meq_equiv : Equivalence meq}(U : Magma meq_equiv) :=
{
  op_assoc : forall x y z:M, (op _ U x (op _ U y z)) = op _ U (op _ U x y) z
}.

Definition mk_semigroup (M : Set) (meq : M -> M -> Prop) (meq_equiv : Equivalence meq)
         (op : M -> M -> M)
         (H: forall a a' b b' : M, meq a a' -> meq b b' -> meq (op a b) (op a' b'))
         (H' : forall x y z:M, (op x (op y z)) = op (op x y) z) :
         Semigroup (mk_magma M meq meq_equiv op H) := Build_Semigroup M meq meq_equiv (mk_magma _ _ _ op H) H'.

Record UMagma{M : Set}{meq : M -> M -> Prop}{meq_equiv : Equivalence meq}(U : Magma meq_equiv) :=
{
  e : M;
  e_id_left  : forall x:M, (op _ U x e) = x;
  e_id_right : forall x:M, (op _ U e x) = x
}.

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
  cancel_div_left  : forall x y:M, (op _ U x (div_left x y)) = y;
  cancel_div_right : forall x y:M, (op _ U (div_right x y) x) = y
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

Check mk_group.