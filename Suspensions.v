Inductive path{T:Type} : T -> T -> Type :=
|refl : forall a:T, path a a.

Infix "~" := path (at level 70, no associativity).

Definition trans{T:Type}{a b c:T} : (b ~ c) -> (a ~ b) -> (a ~ c).
intros.
destruct X.
destruct X0.
apply refl.
Defined.

Definition sym{T:Type}{a b:T} : (a ~ b) -> (b ~ a).
intros.
destruct X.
apply refl.
Defined.

Axiom Suspension : Type -> Type.
Axiom north : forall T:Type, Suspension T.
Axiom south : forall T:Type, Suspension T.
Axiom merid : forall T:Type, T ~ ((north T) ~ (south T)).

Definition ap{T:Type}{B:Type}{a b:T} : forall f:T -> B, (a ~ b) -> (f a ~ f b).
intros.
destruct X.
apply refl.
Defined.

Definition transport{X Y:Type} : (X ~ Y) -> X -> Y.
intros.
destruct X0.
apply X1.
Defined.

Definition adp{T:Type}{B:T -> Type} : forall f:(forall x:T, B x), forall a b:T, forall p:(a ~ b), ((transport (ap B p) (f a)) ~ f b).
intros.
destruct p.
cbv.
apply refl.
Defined.

Axiom Suspension_rect : forall T : Type, (forall P : Type,
       forall N: P,
       forall S: P, 
       forall m: (T -> N ~ S),
       (Suspension T) -> P).

Axiom Suspension_rect_univ : forall T:Type, (forall P : Type,
       forall f : (Suspension T) -> P,
       f ~ (Suspension_rect T P (f (north T)) (f (south T)) (fun x:T => (ap f (transport (merid T) x))))).

Axiom Suspension_rect_north : forall T : Type, (forall P : Type,
       forall N: P,
       forall S: P, 
       forall m: (T -> N ~ S),
       (Suspension_rect T P N S m (north T)) ~ N).

Axiom Suspension_rect_south : forall T : Type, (forall P : Type,
       forall N: P,
       forall S: P, 
       forall m: (T -> N ~ S),
       (Suspension_rect T P N S m (south T)) ~ S).

Axiom Suspension_rect_merid : forall T : Type, (forall P : Type,
       forall N: P,
       forall S: P, 
       forall m: (T -> N ~ S),
       (fun x:T => (trans (Suspension_rect_south T P N S m) (trans (ap (Suspension_rect T P N S m) (transport (merid T) x)) (sym (Suspension_rect_north T P N S m))))) ~ m).

Theorem SF_bool_iso_map  : (Suspension False) -> bool.
apply (Suspension_rect _ _ true false).
intros.
destruct H.
Defined.

Theorem SF_bool_iso_map_inv  : bool -> (Suspension False).
intros.
destruct H.
apply (north _).
apply (south _).
Defined.

Theorem SF_bool_iso1 : forall b:bool, SF_bool_iso_map (SF_bool_iso_map_inv b) ~ b.
intro b.
destruct b.
all: simpl.
all: unfold SF_bool_iso_map.
apply Suspension_rect_north.
apply Suspension_rect_south.
Defined.

Theorem SF_bool_iso2 : forall b:Suspension False, SF_bool_iso_map_inv (SF_bool_iso_map b) ~ b.
apply Suspension_rect.
Defined.
