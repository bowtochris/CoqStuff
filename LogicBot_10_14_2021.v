Theorem LogicBot_10_14_2021 : (forall a b:Prop, ~((a /\ (b <-> b)) <-> ~a)).
intros A B H.
destruct H.
assert (a:A).
apply H0.
intro a.
apply H.
split.
apply a.
apply iff_refl.
apply a.
apply H.
split.
apply a.
apply iff_refl.
apply a.
Optimize Proof.
Defined.

Print LogicBot_10_14_2021.
(*
fun (A B : Prop) (H : A /\ (B <-> B) <-> ~ A) =>
match H with
| conj H0 H1 =>
    let a : A :=
      let H2 : ~ A -> A := fun H2 : ~ A => match H1 H2 with
                                           | conj x _ => x
                                           end in
      H2 (fun a : A => H0 (conj a (iff_refl B)) a) in
    H0 (conj a (iff_refl B)) a
end
*)