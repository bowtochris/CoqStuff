Axiom fun_ext : forall A:Type, forall B:A -> Type, forall f g:(forall a:A, B a), (f = g) = (forall a:A, f a = g a).
Axiom Arrow : Type.
Axiom source : Arrow.
Axiom target : Arrow.
Axiom ale : Arrow -> Arrow -> Prop.
Axiom ale_sym : forall x y:Arrow, (ale x y * ale y x)%type = (x = y).
Axiom ale_trans : forall x y z:Arrow, ale x y -> ale y z -> ale x z.
Axiom ale_total : forall x y:Arrow, (ale x y) + (ale y x)%type.
Axiom ale_top : forall x:Arrow, ale x target.
Axiom ale_bot : forall x:Arrow, ale source x.
Axiom ale_not : target <> source.

Definition ale_join : Arrow -> Arrow -> Arrow.
intros s t.
destruct (ale_total s t).
apply s.
apply t.
Defined.

Definition ale_meet : Arrow -> Arrow -> Arrow.
intros s t.
destruct (ale_total s t).
apply t.
apply s.
Defined.
Definition Span(X Y:Type) : Type := {E:Type & (E -> X) * (E -> Y)}%type.

Definition fun2span : forall X Y:Type, (X -> Y) -> (Span X Y).
intros.
exists X.
split.
intro x.
apply x.
apply X0.
Defined.

Axiom walking : (Arrow -> Type) = {X:Type & {Y:Type & Span X Y}}.

Lemma walking_cast : (Arrow -> Type) -> {X:Type & {Y:Type & Span X Y}}.
intros.
rewrite walking in X.
apply X.
Defined.

Lemma walking_cast_inv : {X:Type & {Y:Type & Span X Y}} -> (Arrow -> Type).
rewrite <- walking.
intro f.
apply f.
Defined.

Axiom walking_eval_source : forall F:Arrow -> Type, ((projT1 (walking_cast F)) = (F source)).
Axiom walking_eval_target : forall F:Arrow -> Type, ((projT1 (projT2 (walking_cast F))) = (F target)).

Theorem walking_cast_iso : forall F:Arrow -> Type, F = (walking_cast_inv (walking_cast F)).
cbv.
intro F.
destruct walking.
trivial.
Defined.

Theorem walking_cast_iso2 : forall F:{X : Type & {Y : Type & Span X Y}}, F = (walking_cast (walking_cast_inv F)).
cbv.
intro F.
rewrite walking.
trivial.
Defined.

Axiom fun_arrow : forall A:Type, forall B:A -> Type, (Arrow -> (forall a:A, B a)) = (forall a:A, Arrow -> B a).
Lemma fun_arrow_cast {A:Type}{B:A -> Type}(f:forall a:A, Arrow -> B a) : (Arrow -> (forall a:A, B a)).
rewrite fun_arrow.
apply f.
Defined.

Axiom fun_arrow_eval : forall A:Type, forall B:A -> Type, forall f:(forall a:A, Arrow -> B a), forall x:Arrow, (fun_arrow_cast f x) = (fun a:A => f a x).

Definition compose{A B C:Type}(f:B -> C)(g:A -> B) : A -> C := fun a:A => f (g a).
Definition monic{A B:Type}(f:A -> B) := forall C:Type, forall g g':C -> A, ((compose f g) = (compose f g')) -> (g = g').
Definition epic{A B:Type}(f:A -> B) := forall C:Type, forall g g':B -> C, ((compose g f) = (compose g' f)) -> (g = g').
Definition automorphicType : forall x y:Type, (x = y) -> (Arrow -> Type).
intros X Y H.
induction H.
apply (walking_cast_inv (existT _ _ (existT _ _ (fun2span _ _ (fun x:X => x))))).
Defined.

Theorem amTSource : forall x y:Type, forall p:x = y, (automorphicType x y p source) = x.
intros.
unfold automorphicType.
destruct p.
assert ((existT (fun X : Type => {Y : Type & Span X Y}) x
        (existT (Span x) x (fun2span x x (fun x0 : x => x0)))) = (walking_cast (automorphicType x x eq_refl ))).
unfold automorphicType.
rewrite walking_cast_iso2.
cbv.
Theorem amTTarget : forall x y:Type, forall p:x = y, (automorphicType x y p target) = y.
Theorem amTMonic : forall x y:Type, monic (automorphicType x y).


Axiom automorphic : forall X:Type, forall x y:X, (x = y) -> (Arrow -> X).
Axiom automorphicEval : (automorphic Type) = automorphicType.

Axiom amSource : forall X:Type, forall x y:X, forall p:x = y, (automorphic X x y p source) = x.
Axiom amTarget : forall X:Type, forall x y:X, forall p:x = y, (automorphic X x y p target) = y.
Axiom amMonic : forall X:Type, forall x y:X, monic (automorphic X x y).

Theorem QQQ : 

Axiom autoevalaxiom : forall X:Type, (walking_cast (automorphic Type X X (eq_refl))) = (existT (fun X:Type => {Y:Type & X -> Y}) X (existT (fun Y:Type => X -> Y) X (fun x:X => x))).

Definition Cube : nat -> Type := (fix F m := match m with
                                             |0 => unit
                                             |1 => Arrow
                                             |S j => (Arrow * (F j))%type
                                             end).

Theorem QQQ : DescendingList (cons source (cons target nil)).
cbv.
split.
apply ale_bot.
trivial.
Defined.

Lemma doubleduh : forall (a b : Arrow), (ale a b) -> forall (l : list Arrow), DescendingList (a :: (b :: l))%list -> DescendingList l.
intros.
destruct H0.
apply H1.

Theorem duh : forall (l : list Arrow) (a : Arrow), DescendingList (a :: l) -> DescendingList l.
intro l.
destruct l.
trivial.
destruct l.
intros.
cbv.
trivial.
intros a1 H1.
split.

Theorem QQQQ : forall l:(list Arrow), (DescendingList l) -> DescendingList (cons source l).
intros.
destruct l.
trivial.
split.
apply ale_bot.
generalize H.
generalize l.
generalize a.
clear H.
clear l.
clear a.

Definition topCube : forall n:nat, Cube (S n) -> Cube n.
intros.
destruct n.
apply tt.
destruct X.
apply c.
Defined.

Definition idCube : forall n:nat, Cube n.
intros.
destruct n.
apply tt.
induction n.
cbv.
apply source.
apply (source, IHn).
Defined.

Lemma refl_depends : forall X:Type, forall x:X, {f:Arrow -> X & (f source) = x /\ (f target) = x}.
intros.
exists (automorphic X x x (eq_refl)).
split.
apply amSource.
apply amTarget.
Defined.

Record Category := mkCat
{
  Obj : Type;
  composeArrow : forall A B C:Obj, {f:Arrow -> Obj & f source = B /\ f target = C} -> {g:Arrow -> Obj & g source = A /\ g target = B} -> {h:Arrow -> Obj & h source = A /\ h target = C};
  law_compose_id_left : forall A B: Obj, forall F:{f:Arrow -> Obj & f source = A /\ f target = B}, (composeArrow _ _ _ F (refl_depends _ _)) = F;
  law_compose_id_right : forall A B: Obj, forall F:{f:Arrow -> Obj & f source = A /\ f target = B}, (composeArrow _ _ _ (refl_depends _ _) F) = F;
  law_compose_assoc : forall A B C D: Obj, forall F:{f:Arrow -> Obj & f source = C /\ f target = D}, forall G:{f:Arrow -> Obj & f source = B /\ f target = C}, forall H:{f:Arrow -> Obj & f source = A /\ f target = B}, (composeArrow _ _ _ F (composeArrow _ _ _ G H)) = (composeArrow _ _ _ (composeArrow _ _ _ F G) H)
}.

Lemma composeArrowType : forall A B C : Type,
  {f : Arrow -> Type & f source = B /\ f target = C} ->
  {g : Arrow -> Type & g source = A /\ g target = B} ->
  {h : Arrow -> Type & h source = A /\ h target = C}.
intros A B C.
rewrite dependent_walking.
rewrite dependent_walking.
rewrite dependent_walking.
apply compose.
Defined.

Definition TypeCat : Category.
apply (mkCat Type composeArrowType).
intros A B F.
destruct F.
destruct a.
rewrite <- e.
rewrite <- e0.
clear e.
clear e0.
rewrite <- (walking_eval x).
cbv.