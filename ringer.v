Require Import Coq.Init.Decimal.
Require Import Coq.ZArith.ZArith.

Inductive positive : Set :=
    xI : positive -> positive | xO : positive -> positive | xH : positive.

Declare Scope local_scope.
Open Scope  local_scope.

Notation "p ~ 1" := (xI p)
 (at level 7, left associativity, format "p '~' '1'") : local_scope.
Notation "p ~ 0" := (xO p)
 (at level 7, left associativity, format "p '~' '0'") : local_scope.

Definition succ := 
fix succ (x : positive) : positive :=
  match x with
  | (p~1) => ((succ p)~0)
  | (p~0) => (p~1)
  | xH => xH~0
  end.

Fixpoint add x y :=
  match x, y with
    | p~1, q~1 => (add_carry p q)~0
    | p~1, q~0 => (add p q)~1
    | p~1, xH => (succ p)~0
    | p~0, q~1 => (add p q)~1
    | p~0, q~0 => (add p q)~0
    | p~0, xH => p~1
    | xH, q~1 => (succ q)~0
    | xH, q~0 => q~1
    | xH, xH => xH~0
  end

with add_carry x y :=
  match x, y with
    | p~1, q~1 => (add_carry p q)~1
    | p~1, q~0 => (add_carry p q)~0
    | p~1, xH => (succ p)~1
    | p~0, q~1 => (add_carry p q)~0
    | p~0, q~0 => (add p q)~1
    | p~0, xH => (succ p)~0
    | xH, q~1 => (succ q)~1
    | xH, q~0 => (succ q)~0
    | xH, xH => xH~1
  end.

Definition mul := 
fix mul (x y : positive) {struct x} : positive :=
  match x with
  | (p~1) => add y (mul p y)~0
  | (p~0) => ((mul p y)~0)
  | xH => y
  end.

Inductive N :=
| O : N
| N_pos : positive -> N.

Definition N_succ(n:N) : N :=
  match n with
   | O => N_pos xH
   | N_pos p => N_pos (succ p)
  end.

Definition N_add(n m:N) : N :=
  match n, m with
   |O, m => m
   |n, O => n
   |N_pos p, N_pos q => N_pos (add p q)
  end.

Definition N_mul(n m:N) : N :=
  match n, m with
   |O, _ => O
   |_, O => O
   |N_pos p, N_pos q => N_pos (mul p q)
  end.

Infix "+" := N_add : local_scope.
Infix "*" := N_mul : local_scope.



Definition one := N_pos xH.
Definition two := N_pos xH~0.
Definition three := N_pos xH~1.
Definition four := N_pos xH~0~0.
Definition five := N_pos xH~0~1.
Definition six := N_pos xH~1~0.
Definition seven := N_pos xH~1~1.
Definition eight := N_pos xH~0~0~0.
Definition nine := N_pos xH~0~0~1.
Definition ten := N_pos xH~0~1~0.
Definition eleven := N_pos xH~0~1~1.
Definition twelve := N_pos xH~1~0~0.
Definition thirteen := N_pos xH~1~0~1.
Definition fourteen := N_pos xH~1~1~0.
Definition fifteen := N_pos xH~1~1~1.
Definition sixteen := N_pos xH~0~0~0~0.

Fixpoint N_uparse_rev (u:Decimal.uint) : N :=
match u with
  |Nil => O
  |D0 k => ten * N_uparse_rev k
  |D1 k => one + ten * N_uparse_rev k
  |D2 k => two + ten * N_uparse_rev k
  |D3 k => three + ten * N_uparse_rev k
  |D4 k => four + ten * N_uparse_rev k
  |D5 k => five + ten * N_uparse_rev k
  |D6 k => six + ten * N_uparse_rev k
  |D7 k => seven + ten * N_uparse_rev k
  |D8 k => eight + ten * N_uparse_rev k
  |D9 k => nine + ten * N_uparse_rev k
end.

Definition N_uparse (n:Decimal.uint) : N := N_uparse_rev (rev n).

Print Hexadecimal.uint.

Fixpoint N_uhparse_rev (u:Hexadecimal.uint) : N :=
match u with
  |Hexadecimal.Nil => O
  |Hexadecimal.D0 k => sixteen * N_uhparse_rev k
  |Hexadecimal.D1 k => one + sixteen * N_uhparse_rev k
  |Hexadecimal.D2 k => two + sixteen * N_uhparse_rev k
  |Hexadecimal.D3 k => three + sixteen * N_uhparse_rev k
  |Hexadecimal.D4 k => four + sixteen * N_uhparse_rev k
  |Hexadecimal.D5 k => five + sixteen * N_uhparse_rev k
  |Hexadecimal.D6 k => six + sixteen * N_uhparse_rev k
  |Hexadecimal.D7 k => seven + sixteen * N_uhparse_rev k
  |Hexadecimal.D8 k => eight + sixteen * N_uhparse_rev k
  |Hexadecimal.D9 k => nine + sixteen * N_uhparse_rev k
  |Hexadecimal.Da k => ten + sixteen * N_uhparse_rev k
  |Hexadecimal.Db k => eleven + sixteen * N_uhparse_rev k
  |Hexadecimal.Dc k => twelve + sixteen * N_uhparse_rev k
  |Hexadecimal.Dd k => thirteen + sixteen * N_uhparse_rev k
  |Hexadecimal.De k => fourteen + sixteen * N_uhparse_rev k
  |Hexadecimal.Df k => fifteen + sixteen * N_uhparse_rev k
end.

Definition N_uhparse (n:Hexadecimal.uint) : N := N_uhparse_rev (Hexadecimal.rev n).

Definition N_parse (n:Number.int) : option N :=
  match n with
   |Number.IntDecimal d => match d with
                     |Decimal.Pos u => Some (N_uparse u)
                     |Decimal.Neg u => None
                    end
   |Number.IntHexadecimal h => match h with
                     |Hexadecimal.Pos u => Some (N_uhparse u)
                     |Hexadecimal.Neg u => None
                    end
  end.


Fixpoint pos_for_pos(p:positive) : BinNums.positive :=
 match p with
 |xH => BinNums.xH
 |p~0 => BinNums.xO (pos_for_pos p)
 |p~1 => BinNums.xI (pos_for_pos p)
 end.

Definition N_print (n:N) : Z :=
 match n with
  | O => Z0
  | N_pos p => Zpos (pos_for_pos p)
 end.

Number Notation N N_parse N_print : local_scope.

Example q : ((14 * 13) + (12 * 11)) = 314.
compute.
trivial.
Defined.

Example q2 : ((fourteen * thirteen) + (twelve * eleven)) = 314.
compute.
trivial.
Defined.

Lemma add_one : forall n:positive, (succ n) = (add n xH).
destruct n.
all: simpl.
all: trivial.
Defined.

Lemma carry_one : forall n m:positive, (add_carry n m) = (add n (succ m)).
induction n.
all: induction m.
all: simpl.
all: try rewrite IHn.
all: try rewrite add_one.
all: try easy.
Defined.

Lemma ringer_pos : forall n m:positive, succ (add n m) = add n (succ m).
induction n.
all: induction m.
all: simpl.
all: try rewrite add_one.
all: try trivial.
3: rewrite <- IHn.
3: rewrite add_one.
3: trivial.
all: try rewrite <- add_one.
all: try rewrite carry_one.
trivial.
rewrite IHn.
trivial.
Defined.

Theorem ringer : forall n m:N, N_succ (n + m) = n + (N_succ m).
intros.
destruct n.
all: destruct m.
all: simpl.
all: try trivial.
all: try rewrite <- add_one.
trivial.
rewrite ringer_pos.
trivial.
Defined.
