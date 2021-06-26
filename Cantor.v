Lemma unequal_functions : forall A B:Type, forall f g:A -> B, {a:A & f a <> g a} -> f <> g.
intros.
intro e.
destruct X.
apply n.
rewrite e.
reflexivity.
Defined.

Theorem cantor : forall X:Type, forall f:X -> (X -> Prop), {P:X -> Prop & forall x:X, f x <> P}.
intros.
exists (fun x:X => ~ (f x x)).
intros.
apply unequal_functions.
exists x.
intro F.
assert (n : ~ f x x).
intro n.
rewrite F in n.
apply n.
rewrite <- F in n.
apply n.
apply n.
rewrite F.
apply n.
Defined.

