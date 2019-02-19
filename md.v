Require Arith.
Require ZArith.
Inductive Zr : Set := cero : Zr | pos : nat->Zr | neg : nat->Zr.
Definition Z_a_Zr:Z->Zr:= [z:Z] Cases z of ZERO=>cero |(POS p)=>(pos(pred(convert p))) |(NEG p)=>(neg(pred(convert p))) end.
Definition Zr_a_Z :Zr->Z:= [z:Zr] Cases z of cero=>ZERO |(pos n)=>(POS(anti_convert n)) |(neg n)=>(NEG(anti_convert n)) end.
Inductive tree012 : Set := c0 :tree012 | c1 : tree012->tree012 | c2 : tree012->tree012->tree012.
Inductive tree12: Set := c1' : tree12->tree12 | c2' : tree12->tree12->tree12.
Inductive LE : nat->nat->Prop := LE_O : (n:nat) (LE O n) | LE_S : (n,m:nat) (LE n m)->(LE (S n) (S m)).
Inductive Natural : Zr->Prop := Cero_nat : (Natural cero) | Uno_nat : (Natural (pos O)) | N_nat : (n:nat) (Natural (pos n))->(Natural (pos (S n))).
Definition Nat_Zr : nat->Zr := [n:nat] Cases n of O => cero | (S n) => (pos n) end.
Inductive Diff : nat->nat->Zr->Prop := Diff_n : (n:nat) (Diff n n cero) | Diff_n_O : (n:nat) (Diff n O (pos (pred n))) | Diff_O_n : (n:nat) (Diff O n (neg (pred n))) | Diff_S : (n,m:nat) (z:Zr) (Diff n m z)->(Diff (S n) (S m) z).
Definition Predecesor : nat->nat := [x:nat]Cases x of O => O | (S x) => x end.
Definition Es_cero : nat->bool := [x:nat]Cases x of O => true | _ => false end.
Section Ejercicio13.
Variables A:Set;P:A->Set.
Inductive suma : Set := intro: (x:A) (P x) -> suma.
Definition p1 : suma -> A := [H:suma] Cases H of (intro x _) => x end.
Definition p2 : (s:suma) (P (p1 s)) := [s:suma] <[t:suma](P (p1 t))>Cases s of (intro x p) => p end.
End Ejercicio13.
Definition Or : bool->bool->bool := [x,y:bool] Cases x of true => true | false => y end.
Definition Opuesto : Zr->Zr := [z:Zr] Cases z of cero => cero | (pos n) => (neg n) | (neg n) => (pos n) end.
Fixpoint diff [n:nat] : nat->Zr := [m:nat] Cases n m of O O => cero | O (S n) => (neg n) | (S n) O => (pos n) | (S n) (S m) => (diff n m) end.
Definition Suma :Zr->Zr->Zr := [x,y:Zr] Cases x y of cero y => y | x cero =>x | (pos n) (pos m) => (pos (plus n m)) | (neg n) (neg m) => (neg (plus n m)) | (pos n) (neg m) => (diff n m) | (neg m) (pos n) => (diff n m) end.
Definition max :=(nat_rec [_:nat]nat->nat [n1:nat]n1 [n1:nat][Rec:nat->nat][H0:nat] Cases H0 of O => (S n1) | (S n2) => (S (Rec n2)) end).

Lemma max_O_r:(a:nat)(max a O)=a.
Intro.
Induction a.
Simpl.
Trivial.
Simpl.
Trivial.
Defined.

Lemma max_O_l:(a:nat)(max O a)=a.
Intro.
Induction a.
Simpl.
Trivial.
Simpl.
Trivial.
Defined.

Lemma max_sym:(a,b:nat)(max a b)=(max b a).
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

Lemma max_intro_l:(a,b:nat)(le a (max a b)).
Induction a.
Induction b.
Simpl.
Trivial.
Intros.
Simpl.
Apply (le_O_n (S n)).
Intros.
Elim b.
Simpl.
Apply (le_n (S n)).
Intros.
Simpl.
Apply (le_n_S n (max n n0) (H n0)).
Defined.

Lemma max_intro_r:(a,b:nat)(le b (max a b)).
Induction a.
Induction b.
Simpl.
Trivial.
Intros.
Simpl.
Trivial.
Intros.
Elim b.
Simpl.
Apply (le_O_n (S n)).
Intros.
Simpl.
Apply (le_n_S n0 (max n n0) (H n0)).
Defined.

Lemma max_id:(a:nat)(max a a)=a.
Intro.
Induction a.
Simpl.
Trivial.
Simpl.
Rewrite Hreca.
Trivial.
Defined.

Lemma max_le:(a,b:nat)(le a b)->(max a b)=b.
Induction a.
Induction b.
Trivial.
Intros.
Trivial.
Intros.
Elim H0.
Apply (max_id (S n)).
Intros.
Simpl.
Apply eq_S.
Apply (H m (le_trans_S n m H1)).
Defined.
