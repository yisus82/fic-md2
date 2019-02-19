
(* ejercicio 1:(PUNTOS: 2 )
  Probar las siguientes proposiciones sin hacer uso de Tauto ni de Auto: *)


Lemma distr_impl : (A,B,C:Prop)(A->(B->C))->(A->B)->(A->C).
Intros.
Apply H.
Assumption.

Apply H0.
Assumption.
Defined.

Section ej1.
Variables p,q:Prop.
Hypothesis premisa1: ~p \/ q.

Lemma ejemplo1 : p -> q.
Intro.
Elim premisa1.
Intro.
Absurd p.
Assumption.

Assumption.

Intro.
Assumption.
Defined.
End ej1.


Section Regla_MT.

Variables A,B:Prop.
Hypothesis prem1 : A->B.
Hypothesis prem2 : ~B.

Theorem MT : ~A.
Intro.
Generalize (prem1 H).
Intro.
Absurd B.
Assumption.

Assumption.
Defined.
End Regla_MT.

Print distr_impl.
Print ejemplo1.
Print MT. 

(* En logica intuicionista de segundo orden, los conectivos
"falso", "o" e "y" pueden ser definidos en funcion de "para todo" y
la implicacion *) 

(* definicion de falso *)

Definition new_false := (a:Prop)a .

(* ejercicio 2:(PUNTOS: 2 )
   probar dos teoremas que juntos prueben la equivalencia de
   new_false y False *)

Theorem equiv_false1:(new_false)->(False).
Intro.
Apply H.
Defined.

Theorem equiv_false2: 
(False)->new_false.
Intro.
Contradiction.
Defined.
Print equiv_false1.
Print equiv_false2.


(* definicion de "y":
a "y" b es verdad si todo lo que se puede derivar del conjunto
{a,b} es verdad *)

Definition new_and := [a,b:Prop](c:Prop)((a -> b -> c) -> c) .

(* ejercicio 3:(PUNTOS: 3 ) 
   probar dos teoremas que juntos demuestren
   la equivalencia de new_and y /\ *)
Theorem equiv_and1:(a,b:Prop)(new_and a b)->(a/\b) .
Intro.
Intros.
Apply H.
Intros.
Split.
Assumption.
Assumption.
Defined.

Theorem equiv_and2:(a,b:Prop)(a/\b)->(new_and a b) . 
Intros.
Unfold new_and.
Intros.
Apply H0.
Elim H.
Intros.
Assumption.
Elim H.
Intros.
Assumption.
Defined.

Print equiv_and1.
Print equiv_and2.

(* usando polimorfismo podemos definir tipos de datos como 
   numeros naturales y booleanos aunque
   Coq use definiciones inductivas porque resulta
   mas eficiente *)   
    

(* numeros naturales *)

Definition new_nat := (a:Set)(a->(a->a)->a).

 1
(* numeros polimorficos de Church *)

Definition zero := [a:Set][z:a][s:a->a] z.
Definition one  := [a:Set][z:a][s:a->a] (s z).
Definition two  := [a:Set][z:a][s:a->a] (s (s z)).


(* ejercicio 4 : (PUNTOS 3 ) 
   Dar una definicion de sucesor y chequearla con
   al menos dos entradas diferentes. Por ejemplo, comprobar
   que el sucesor de zero es one y el sucesor de one es two *)

Definition sucesor[x:Set;z:x;s:x->x;]:=(s ).


Print sucesor.






