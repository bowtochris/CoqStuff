Definition PointedType := {X:Type & X}.
Definition PointedMap(X Y:PointedType) := {f:(projT1 X) -> (projT1 Y) & f (projT2 X) = (projT2 Y)}.

Definition PointMap(X Y:PointedType) : PointedType.
exists (PointedMap X Y).
destruct Y as [Y y].
exists (fun _:_ => y).
cbv.
trivial.
Defined.

Definition point : PointedType.
exists unit.
apply tt.
Defined.

Definition loop : PointedType -> PointedType.
intro X.
destruct X as [X x].
exists (x = x).
apply eq_refl.
Defined.

Definition loopMap : forall X Y:PointedType, (PointedMap X Y) -> (PointedMap (loop X) (loop Y)).
intros.
destruct X as [X x].
destruct Y as [Y y].
destruct X0 as [f Hf].
simpl in *.
cbv.
exists (fun p:x = x => match Hf with
                       |eq_refl => match p with
                                   |eq_refl => eq_refl
                                    end
                       end).
rewrite Hf.
trivial.
Defined.

Inductive int : Set :=
|neg : nat -> int
|zero : int
|pos : nat -> int.

Definition succ(n:int) : int := match n with
                                |neg (S k) => neg k
                                |neg 0 => zero
                                |zero => pos 0
                                |pos k => pos (S k)
                                end.

Definition pred(n:int) : int := match n with
                                |pos (S k) => pos k
                                |pos 0 => zero
                                |zero => neg 0
                                |neg k => neg (S k)
                                end.

Definition spectrum := {E: int -> PointedType & forall n:int, PointedMap (E n) (loop (E (succ n)))}.

Definition loopSpectrumTypes(X:PointedType) : int -> PointedType := fix F n := match n with
                     |zero => X
                     |pos k => (fix G m := match m with
                                           |0 => loop X
                                           |S j => loop (G j)
                                           end) k
                     |neg _ => point
                     end.

Definition loopSpectrum(X:PointedType) : spectrum.
exists (loopSpectrumTypes X).
intros.
induction n.
induction n.
destruct X as [X x].
simpl.
exists (fun _:_ => eq_refl).
cbv.
trivial.
destruct X as [X x].
simpl.
exists (fun _:_ => eq_refl).
cbv.
trivial.
destruct X as [X x].
simpl.
exists (fun _:_ => eq_refl).
cbv.
trivial.
induction n.
destruct X as [X x].
simpl.
exists (fun _:_ => eq_refl).
cbv.
trivial.
simpl in *.
apply loopMap.
apply IHn.
Defined.

Definition constantSpectrumTypes(X:PointedType) : int -> PointedType := fun _:_ => X.

Definition constantSpectrum(X:PointedType) : spectrum.
exists (constantSpectrumTypes X).
intros.
induction n.
induction n.
destruct X as [X x].
simpl.
exists (fun _:_ => eq_refl).
cbv.
trivial.
destruct X as [X x].
simpl.
exists (fun _:_ => eq_refl).
cbv.
trivial.
destruct X as [X x].
simpl.
exists (fun _:_ => eq_refl).
cbv.
trivial.
induction n.
destruct X as [X x].
simpl.
exists (fun _:_ => eq_refl).
cbv.
trivial.
simpl in *.
apply IHn.
Defined.

Definition mapSpectrumTypes(X:PointedType) : spectrum -> int -> PointedType := fun S:spectrum => fun n:int => PointMap X ((projT1 S) n).

Definition mapSpectrum(X:PointedType) : spectrum -> spectrum.
intro S.
exists (mapSpectrumTypes X S).
destruct S as [S HS].
intros.
induction n.
induction n.
destruct X as [X x].
simpl.
exists (fun _:_ => eq_refl).
cbv.
trivial.
destruct X as [X x].
simpl.
exists (fun _:_ => eq_refl).
cbv.
trivial.
destruct X as [X x].
simpl.
exists (fun _:_ => eq_refl).
cbv.
trivial.
induction n.
destruct X as [X x].
simpl.
exists (fun _:_ => eq_refl).
cbv.
trivial.
destruct X as [X x].
exists (fun _:_ => eq_refl).
simpl in *.
trivial.
Defined.

Definition sphereSpectrum(X:PointedType) : spectrum := loopSpectrum (existT _ _ true).