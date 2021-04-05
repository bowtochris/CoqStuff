Inductive Tree : Set :=
|children : list Tree -> Tree.

Fixpoint length(t:Tree) : nat :=
match t with
|children l => S (length_forest l)
end
with length_forest(f:list Tree) : nat :=
match f with
|nil => 0
|cons t ts => (length t) + (length_forest ts)
end.

(*
Recursive definition of length_forest is ill-formed.
In environment
length : Tree -> nat
length_forest : list Tree -> nat
f : list Tree
t : Tree
ts : list Tree
Recursive call to length has principal argument equal to
"t" instead of "ts".
Recursive definition is:
"fun f : list Tree =>
 match f with
 | nil => 0
 | (t :: ts)%list => length t + length_forest ts
 end".
*)