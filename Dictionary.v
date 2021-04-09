Require Import Coq.Lists.List.

Fixpoint InAtMostOnce{A:Type}(a:A)(l:list A)(H : forall x y : A, (x = y) + (x <> y)) {struct l}: Prop :=
match l with
|nil => True
|cons a' l' => match H a a' with
                  |inl _ => (In a l') -> False
                  |inr _ => (InAtMostOnce a l' H)
                  end
end.

Record Dictionary (K V:Type) :=
{
  dict_entries : list (K * V);
  dict_decide_key_eq : forall x y:K, (x = y) + (x <> y);
  dict_unique : forall k:K, InAtMostOnce k (map fst dict_entries) dict_decide_key_eq
}.

Definition EmptyDictionary(K V:Type)(H : forall x y : K, (x = y) + (x <> y)) : Dictionary K V :=
{|
  dict_entries := nil;
  dict_decide_key_eq := H;
  dict_unique := fun (_ : K) => I
|}.

Definition keys{K V:Type}(D:Dictionary K V) : list K := map fst (dict_entries _ _ D).

Fixpoint getValue_list {K V:Type}(l:list (K * V))(H : forall x y : K, (x = y) + (x <> y))(k:K) {struct l}: option V :=
match l with
|nil => None
|(k', v) :: l' => match H k k' with
                  |inl _ => Some v
                  |inr _ => getValue_list l' H k
                  end
end.

Definition getValue{K V:Type}(D:Dictionary K V)(k:K) : option V :=
  getValue_list (dict_entries _ _ D) (dict_decide_key_eq _ _ D)(k:K).

Fixpoint setValue_list {K V:Type}(l:list (K * V))(H : forall x y : K, (x = y) + (x <> y))(k:K)(v:V) {struct l}: list (K * V) :=
match l with
|nil => (k, v) :: nil
|(k', v') :: l' => match H k k' with
                  |inl _ => (k, v) :: l'
                  |inr _ => (k', v') :: setValue_list l' H k v
                  end
end.

Ltac generalize_clear H := generalize H; clear H.

Lemma notinLemma{A:Type}(a:A)(l:list A)(H : forall x y : A, (x = y) + (x <> y)) : (In a l -> False) -> InAtMostOnce a l H.
induction l.
all: simpl.
all: intros.
apply I.
destruct (H a a0).
symmetry in e.
destruct (H0 (or_introl e)).
apply IHl.
intro.
destruct (H0 (or_intror H1)).
Optimize Proof.
Defined.

Lemma sVInLemma{K V:Type}(dict_entries0 : list (K * V))
 : forall (k' k:K)(v:V)(n:k<>k')(dict_decide_key_eq0 : forall x y : K, (x = y) + (x <> y)),
   In k' (map fst (setValue_list dict_entries0 dict_decide_key_eq0 k v)) -> In k' (map fst dict_entries0).
induction dict_entries0.
all: intros.
2: destruct a as [x y].
all: simpl in *.
destruct H.
apply (n H).
apply H.
destruct (dict_decide_key_eq0 k x).
simpl in H.
destruct H.
constructor 1.
destruct H.
destruct e.
trivial.
constructor 2.
apply H.
simpl in H.
destruct H.
constructor 1.
apply H.
constructor 2.
apply (IHdict_entries0 _ _ _ n dict_decide_key_eq0 H).
Optimize Proof.
Defined.

Definition setValue {K V:Type}(D:Dictionary K V)(k:K)(v:V) : Dictionary K V.
apply (Build_Dictionary _ _
   (setValue_list (dict_entries K V D) (dict_decide_key_eq K V D) k v)
   (dict_decide_key_eq K V D)).
destruct D.
simpl in *.
induction dict_entries0.
all: intro k'.
simpl in *.
destruct (dict_decide_key_eq0 k' k).
intro F; apply F.
apply I.
destruct a as [x y].
simpl in *.
destruct (dict_decide_key_eq0 k x).
destruct e.
simpl in *.
apply dict_unique0.
unfold map.
fold (map fst (setValue_list dict_entries0 dict_decide_key_eq0 k v)).
unfold fst at 1.
unfold InAtMostOnce.
fold (InAtMostOnce k').
assert (forall k : K, InAtMostOnce k (map fst dict_entries0) dict_decide_key_eq0).
intros.
assert (H := dict_unique0 k0).
destruct (dict_decide_key_eq0 k0 x).
apply notinLemma.
apply H.
apply H.
assert (H' := IHdict_entries0 H k').
destruct (dict_decide_key_eq0 k' x).
destruct e.
2: apply H'.
assert (H'' := dict_unique0 k').
destruct (dict_decide_key_eq0 k' k').
2: destruct (n0 eq_refl).
intros.
apply H''.
generalize H0.
apply sVInLemma.
apply n.
Optimize Proof.
Defined.
