Lemma Scarlet_11_16_22 : forall f: nat -> (nat -> nat), let d := fun n:nat => 1 + f(n)(n) in forall m:nat, d <> f m.
simpl.
intros.
intro N.
assert (forall A B:Type, forall f g:A -> B, forall x:A, f = g -> f x = g x).
intros.
destruct H.
reflexivity.
assert (S (f m m) = f m m).
apply (H _ _ _ _ m N).
induction (f m m).
all: inversion H0.
apply (IHn H2).
Optimize Proof.
Defined.

Print Scarlet_11_16_22
(*
Scarlet_11_16_22 = 
fun (f : nat -> nat -> nat) (m : nat) (N : (fun n : nat => S (f n n)) = f m) =>
let H : forall (A B : Type) (f0 g : A -> B) (x : A), f0 = g -> f0 x = g x :=
  fun (A B : Type) (f0 g : A -> B) (x : A) (H : f0 = g) =>
  match H in (_ = y) return (f0 x = y x) with
  | eq_refl => eq_refl
  end in
let H0 : S (f m m) = f m m := H nat nat (fun n : nat => S (f n n)) (f m) m N in
let n := f m m in
nat_ind (fun n0 : nat => S n0 = n0 -> False)
  (fun H1 : 1 = 0 =>
   let H2 : 0 = 0 -> False :=
     match H1 in (_ = y) return (y = 0 -> False) with
     | eq_refl =>
         fun H2 : 1 = 0 =>
         (fun H3 : 1 = 0 =>
          let H4 : False := eq_ind 1 (fun e : nat => match e with
                                                     | 0 => False
                                                     | S _ => True
                                                     end) I 0 H3 in
          False_ind False H4) H2
     end in
   H2 eq_refl)
  (fun (n0 : nat) (IHn : S n0 = n0 -> False) (H1 : S (S n0) = S n0) =>
   let H2 : S n0 = S n0 -> False :=
     match H1 in (_ = y) return (y = S n0 -> False) with
     | eq_refl =>
         fun H2 : S (S n0) = S n0 =>
         (fun H3 : S (S n0) = S n0 =>
          let H4 : S n0 = n0 := f_equal (fun e : nat => match e with
                                                        | 0 => S n0
                                                        | S n1 => n1
                                                        end) H3 in
          (fun H5 : S n0 = n0 => let H6 : S n0 = n0 := H5 in eq_ind (S n0) (fun _ : nat => False) (IHn H5) n0 H6) H4)
           H2
     end in
   H2 eq_refl) n H0
     : forall f : nat -> nat -> nat, let d := fun n : nat => 1 + f n n in forall m : nat, d <> f m
*).