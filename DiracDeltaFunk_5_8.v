Require Import Coq.Logic.FinFun.

Definition pullback{X Y Z:Type}(f:X -> Z)(g:Y -> Z) : Type := {x:X & {y:Y & (f x) = (g y)}}.

Definition DiracDeltaFunk_5_8_property(X:Type) := forall Y:Type, {f:X -> Y & Surjective (fun p:pullback f f => projT1 p)}.

Theorem DD_Empty : forall X:Type, DiracDeltaFunk_5_8_property X -> (X -> False).
intros X H x.
assert (c := H False).
destruct c as [f H0].
apply (f x).
Defined.

Definition DiracDeltaFunk_5_8_property_mach2(X:Type) := forall Y:Type, Y -> {f:X -> Y & Surjective (fun p:pullback f f => projT1 p)}.

Example DD_unit_ex : DiracDeltaFunk_5_8_property_mach2 unit.
intros Y y.
exists (fun _:_ => y).
cbv.
intro u.
destruct u.
exists (existT (fun _:unit => {_ : unit & y = y}) tt (existT (fun _:unit => y = y) tt eq_refl)).
reflexivity.
Defined.

Example DD_nat_ex : DiracDeltaFunk_5_8_property_mach2 nat.
intros Y y.
exists (fun _:_ => y).
cbv.
intro u.
exists (existT (fun _:nat => {_ : nat & y = y}) u (existT (fun _:nat => y = y) u eq_refl)).
reflexivity.
Defined.


Theorem DD_all : forall X:Type, DiracDeltaFunk_5_8_property_mach2 X.
intros X Y y.
exists (fun _:_ => y).
cbv.
intro u.
exists (existT (fun _:_ => {_ : _ & y = y}) u (existT (fun _:_ => y = y) u eq_refl)).
reflexivity.
Defined.