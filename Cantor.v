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
Optimize Proof.
Defined.

Print cantor.

(*
cantor = 
fun (X : Type) (f : X -> X -> Prop) =>
existT (fun P : X -> Prop => forall x : X, f x <> P) (fun x : X => ~ f x x)
  (fun x : X =>
   unequal_functions X Prop (f x) (fun x0 : X => ~ f x0 x0)
     (existT (fun a : X => f x a <> (~ f a a)) x
        (fun F : f x x = (~ f x x) =>
         let n : ~ f x x :=
           fun n : f x x =>
           let n0 : ~ f x x := eq_ind (f x x) (fun P : Prop => P) n (~ f x x) F in
           n0 (let n1 : f x x := eq_ind_r (fun P : Prop => P) n0 F in n1) in
         n (eq_ind_r (fun P : Prop => P) n F))))
     : forall (X : Type) (f : X -> X -> Prop), {P : X -> Prop & forall x : X, f x <> P}
*)

