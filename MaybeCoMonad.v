Require Import Coq.Program.Basics.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.CoMonad.

Set Implicit Arguments.

Import MonadNotation.
Local Open Scope program_scope.
Local Open Scope monad_scope.

Definition MaybeMonad : Monad option.
apply Build_Monad.
intro T.
apply Some.
intros T U t f.
destruct t.
apply (f t).
apply None.
Defined.

Definition NotMaybeCoMonad : (CoMonad option) -> False.
intros.
destruct X.
destruct (extract False None).
Defined.