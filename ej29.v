Section Max.
Require Arith.
Definition max :=
(nat_rec [_:nat]nat->nat [n1:nat]n1
[n1:nat]
[Rec:nat->nat]
[H0:nat]
Cases H0 of
O => (S n1)
| (S n2) => (S (Rec n2))
end).

Lemma max_O_r : (a:nat) (max a O)=a.
Intro.
Induction a.
Simpl.
Trivial.
Simpl.
Trivial.
Defined.

Lemma max_O_l : (a:nat) (max O a)=a.
Intro.
Induction a.
Simpl.
Trivial.
Simpl.
Trivial.
Defined.

Lemma max_sym : (a,b:nat) (max a b)=(max b a).
Induction a.
Simpl.
Induction b.
Simpl.
Trivial.
Intros.
Simpl.
Trivial.
Intros.
Elim b.
Simpl.
Trivial.
Intros.
Simpl.
Apply eq_S.
Apply (H n0).
Defined.

