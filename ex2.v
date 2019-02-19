
(*  EXAMEN REALIZADO POR CARLOS RODIRGUEZ DIAZ      infcrd00  *)


(*  EJERCICIO 1 *)

Theorem imp_distr:(P,Q,R:Prop)(P->(Q->R))->(P->Q)->P->R.

Intros.
Apply H.
Assumption.

Apply H0.
Assumption.
Qed.


Theorem imp_perm:(P,Q,R:Prop)(P->Q->R)->(Q->P->R).

Intros.
Apply H;Assumption.
Qed.


Theorem delta_impR:(P,Q:Prop)(P->Q)->(P->P->Q).

Intros.
Apply H; Assumption.
Qed.


Theorem weak_peirce:(P,Q:Prop)((((P->Q)->P)->P)->Q)->Q.

Intros.
Apply H.
Intro.
Apply H0.
Intro.
Apply H.
Intro.
Assumption.
Qed.



(* EJERCICIO 2 *)

Require Arith.
Inductive impar:nat->Prop:=
	impar_1: (impar (S O))
       |impar_S: (n:nat)(impar n) -> (impar (S (S n))).


Lemma doce_lt_cuarenta:(lt (12) (40)).

Repeat Constructor.
Qed.


Lemma impar_trece :(impar (13)).

Repeat Constructor 2;Constructor 1.
Qed.



(*  EJERCICIO 3   *)

Definition maximo:= (nat_rec 
		    [_:nat]nat->nat
		    [x:nat]x
			[n:nat][rec:nat->nat][y:nat] Cases y of O => (S n)
											|(S n2) => (S (rec n2))
										 end).

Theorem max : (n,m:nat)(le n m) -> (maximo n m)=m.

Induction n;Induction m;Intros.
Constructor.

Constructor.

Inversion H0.

Elim H1.
Simpl.
Auto.

Intros.
Generalize (le_trans_S n0 m0 H2).
Intro.
Simpl.
Generalize (H m0 H4).
Intro.
Simpl.
Auto.
Qed.




