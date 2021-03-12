Open Scope type.

Inductive eq{A:Type} : forall a b:A, Type :=
| refl : forall a:A, eq a a.

Definition isIso{X Y:Type}(f:X -> Y) := {g:Y -> X & forall x:X, @eq X x (g (f x))} * {h:Y -> X & forall y:Y, @eq Y y (f (h y))}.
Definition iso(X Y:Type) := {f:X -> Y & isIso f}.

Definition id2iso(X Y:Type) : (@eq Type X Y) -> iso X Y.
intro H.
induction H.
exists (fun x:_ => x).
split.
exists (fun x:_ => x).
apply refl.
exists (fun x:_ => x).
apply refl.
Defined.

Parameter ua : forall X Y:Type, isIso (id2iso X Y).

Definition uaIso : forall X Y:Type, iso (@eq Type X Y) (iso X Y).
intros X Y.
exists (id2iso _ _).
apply ua.
Defined.

Inductive N : Type :=
|zero : N
|succ : N -> N.

Theorem nat2N : @eq Type nat N.
destruct (ua nat N).
destruct s.
apply x.
exists (fix F n := match n with
                    |0 => zero
                    |S k => succ (F k)
                    end).
split.
exists (fix F n := match n with
                    |zero => 0
                    |succ k => S (F k)
                    end).
intro n.
induction n.
apply refl.
induction IHn.
apply refl.
exists (fix F n := match n with
                    |zero => 0
                    |succ k => S (F k)
                    end).
intro n.
induction n.
apply refl.
induction IHn.
apply refl.
Defined.

Definition uaEq : forall X Y:Type, @eq Type (@eq Type X Y) (iso X Y).
intros X Y.
destruct (ua (@eq Type X Y) (iso X Y)).
destruct s.
apply x.
apply uaIso.
Defined.

Definition fun_ext : forall A:Type, forall B:A -> Type, forall f g:(forall a:A, B a), @eq Type (@eq (forall a:A, B a) f g) (forall a:A, @eq (B a) (f a) (g a)).
intros A B f g.
rewrite (uaEq (@eq (forall a : A, B a) f g) (forall a : A, @eq (B a) (f a) (g a))).