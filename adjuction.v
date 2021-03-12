Require Import Coq.Program.Basics.
Require Import ExtLib.Core.Any.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.FunctorLaws.
Require Import ExtLib.Structures.CoFunctor.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.CoMonad.

Search "FunctorLaws".

Polymorphic NonCumulative Record Natural_Transformation {F G : Type -> Type} (Functor_F : Functor F) (Functor_G : Functor G) :=
{
  alpha : forall X:Type, (F X) -> (G X);
  natural_law : forall X Y:Type, forall f:X -> Y, compose (alpha Y) (@fmap _ Functor_F _ _ f) = compose (@fmap _ Functor_G _ _ f) (alpha X)
}.

Definition id_nt{F : Type -> Type} (Functor_F : Functor F) : Natural_Transformation Functor_F Functor_F.
apply (Build_Natural_Transformation _ _ _ _ (fun X:Type => id)).
cbv; auto.
Defined.

Lemma compose_assoc : forall A B C D:Type, forall h:A -> B, forall g:B -> C, forall f:C -> D,  compose (compose f g) h = compose f (compose g h).
intros; cbv; easy.
Defined.

Definition compose_nt{F G H : Type -> Type} {Functor_F : Functor F} {Functor_G : Functor G} {Functor_H : Functor H} (eta : Natural_Transformation Functor_G Functor_H) (epsilon : Natural_Transformation Functor_F Functor_G): Natural_Transformation Functor_F Functor_H.
apply (Build_Natural_Transformation _ _ _ _ (fun X:Type => compose (alpha _ _ eta X) (alpha _ _ epsilon X))).
destruct eta as [alpha_eta natural_law_eta].
destruct epsilon as [alpha_epsilon natural_law_epsilon].
simpl in *.
intros.
rewrite compose_assoc.
rewrite natural_law_epsilon.
repeat rewrite <- compose_assoc.
rewrite natural_law_eta.
trivial.
Optimize Proof.
Defined.

Definition Hom_Functor : forall C:Type, Functor (fun D:Type => C -> D).
intros; apply Build_Functor.
intros A B f g c.
apply f.
apply g.
apply c.
Optimize Proof.
Defined.

Definition Hom_FunctorLawsProp : Prop.
eapply (forall C:Type, FunctorLaws (Hom_Functor C) _).
Unshelve.
repeat intro.
destruct X.
split.
all: repeat intro.
apply (forall c:C, equal (X c) (X0 c)).
apply (forall c:C, proper (X c)).
Defined.

Ltac crush :=
  repeat match reverse goal with
         | [ H : ?T |- _ ] => destruct H
         end.

Definition Hom_FunctorLaws : Hom_FunctorLawsProp.
cbv.
repeat intro.
apply Build_FunctorLaws.
all: repeat intro.
all: simpl.
all: unfold Identity.IsIdent in *.
all: crush.
all: try simpl in *.
all: repeat intro.
cbv in *.
apply (equiv_trans _ (x c) _).
apply H.
destruct (only_proper _ _ (H0 c)).
apply H1.
apply H0.
all: cbv in *.
apply H3.
apply H2.
apply H4.
apply H1.
apply H2.
Defined.

Polymorphic NonCumulative Record Adjoint {L R : Type -> Type} (Functor_L : Functor L) (Functor_R : Functor R) :=
{
   adjoint_left : Natural_Transformation Functor_L Functor_R
}.