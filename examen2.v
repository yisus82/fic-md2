(*EXAMEN GRUPO B*)
(* Directorio /PRACTICAS/EI/ExMD2Dic/P2 *)

(*NOMBRE: JESUS ANGEL PEREZ-ROCA FERNANDEZ*)

(* ejercicio 1:(PUNTOS: 2 )
  Probar las siguientes proposiciones sin hacer uso de Tauto ni de Auto: *)

Theorem Imp_trans:(P,Q,R:Prop)(P->Q)->(Q->R)->(P->R).
Intros.
Apply (H0 (H H1)).
Defined.

Theorem Ignore_Q:(P,Q,R:Prop)(P->R)->P->Q->R.
Intros.
Apply (H H0).
Defined.

Theorem Delta_imp:(P,Q:Prop)(P->P->Q)->P->Q.
Intros.
Apply (H H0).
Trivial.
Defined.

Theorem Losange:(P,Q,R,S:Prop)(P->Q)->(P->R)->(Q->R->S)->P->S.
Intros.
Apply (H1 (H H2) (H0 H2)).
Defined.

Print Imp_trans.
Print Ignore_Q.
Print Delta_imp.
Print Losange.

(* En logica intuicionista de segundo orden, los conectivos
"falso", "o" e "y" pueden ser definidos en funcion de "para todo" y
la implicacion *) 

(* definicion de falso *)

Definition new_false := (a:Prop)a .


(* exercise 2: (PUNTOS 2) 
   probar el siguiente teorema *)

Theorem ef : (a:Prop)(new_false -> a).
Intros.
Apply H.
Defined.

Print ef.

(* Definicion de "o":
 a"o"b es verdad si todo lo que se deduce de {a} y de {b} es verdad *)

Definition new_or:=[a,b:Prop](c:Prop)(a->c)->(b->c)->c.

(* ejercicio 3 :(PUNTOS 3) 
   probar dos teoremas que juntos demuestren la 
   equivalencia de new_or y \/. *)


Theorem equiv_or1: (a,b:Prop)(new_or a b)->(a\/b).
Intros.
Apply H.
Intro.
Left.
Trivial.
Intro.
Right.
Trivial.
Defined.

Theorem equiv_or2: (a,b:Prop)(a\/b)->(new_or a b).
Intros.
Unfold new_or.
Intros.
Elim H.
Trivial.
Trivial.
Defined.

(* usando polimorfismo podemos definir tipos de datos como 
   numeros naturales y booleanos aunque
   Coq use definiciones inductivas porque resulta
   mas eficiente *)   

(* booleanos *)

Definition new_bool := (a:Set)(a->a->a) .
Definition t := [a:Set][x,y:a]x .
Definition f := [a:Set][x,y:a]y .

(* exercicio 4 :(PUNTOS 3)
   Dar una definicion de new_not:new_bool -> new_bool
   para la negacion en new_bool
   y chequearla con dos entradas diferentes *)

Definition new_not:new_bool->new_bool.
Unfold new_bool.
Intros.
Apply H.
Exact H1.
Exact H0.
Defined.

Print new_not.

Eval Compute in (new_not t).

Eval Compute in (new_not f).

(* Estos dos resultados serian para los tipos polimorficos. 
   Si quisieramos probarlo para el tipo bool la comprobacion seria asi:*)
   
Eval Compute in (t bool true false).

Eval Compute in ((new_not t) bool true false).

Eval Compute in (f bool true false).

Eval Compute in ((new_not f) bool true false).
