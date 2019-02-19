Definition or_user_2[a:bool]:=<bool->bool>Case a of ([_:bool]true) ([b:bool]b)  end.

Parameter c:bool.
Lemma or1:(or_user_2 true c)=true.
Simpl.
Trivial.
Save.

Require codigoCoq.
Require Arith.

(* ===== OPERACIONES DE NUMEROS NATURALES =========*)


(* suma de dos naturales, resultado natural *)
Fixpoint sumN[n,m:nat]:nat:=
Cases n m of
h O=>h
|h (S i)=>(S (sumN h i))
end.

(* predecesor de un natural, para el cero es cero *)
Definition predN:=[n:nat]Cases n of O=>O | (S i)=>i end.

(* resta de dos naturales, resultado natural *)
Fixpoint restaN[n,m:nat]:nat:=
Cases n m of
h O=>h
|h (S k)=>(predN(restaN h k))
end.

(* resta de dos naturales, resultado natural, VERSION _REC *)
Definition mi_restaN:=[n:nat]
(nat_rec [_:nat]nat n [k,b:nat](predN b)).


(* producto de naturales, resultado natural *)
Fixpoint productoN[n,m:nat]:nat:= Cases n m of
_ O => O
|k (S l)=> (sumN k (productoN k l))
end.

(* potencia de naturales, resultado natural *)
Fixpoint potenciaN[n,m:nat]:nat:= Cases n m of
_ O => (S O)
|k (S l)=> (productoN k (potenciaN k l))
end.


(* factorial de un natural, resultado natural *)
Fixpoint factorial[n:nat]:nat:=
Cases n of
O => (S O)
|(S l)=>(productoN (S l) (factorial l))
end.

(* factorial de un natural, resultado natural, VERSION _REC *)
Definition mifactorial:=
(nat_rec ([_:nat]nat) (S O) [j:nat][l:nat](productoN (S j) l)).

(* potencia de dos naturales, resultado natural, VERSION _REC *)
Definition mipotencia:=[x:nat]
(nat_rec ([_:nat]nat) (S O) [k:nat][v:nat](productoN x v)).

(* producto de dos naturales, resultado natural, VERSION _REC *)
Definition miproducto:=[x:nat]
(nat_rec ([_:nat]nat) O [k:nat][f:nat](sumN x f)).

(* suma de dos naturales, resultado natural, VERSION _REC *)
Definition misuma:=[x:nat]
(nat_rec ([_:nat]nat) x [k:nat][f:nat](S f)).


(* LEMAS DE LAS RESTAS==================*)


(* primer lema sobre las restas *)
Lemma restaN_eq1:(n,m:nat)(restaN n m)=(mi_restaN  n m).
Intros.
Induction m.
Simpl.
Trivial.
Simpl.
Induction n.
Rewrite Hrecm.
Trivial.
Rewrite Hrecm.
Trivial.
Save.

(* segundo lema sobre la resta *)
Lemma mi_restaN_1:(n:nat)(mi_restaN O n)=O.
Induction n.
Simpl; Trivial.
Simpl.
Intros.
Rewrite H.
Simpl.
Trivial.
Save.

(* tercer lema sobre la resta *)
Lemma mi_restaN_2:(n:nat)(mi_restaN n O)=n.
Induction n.
Simpl; Trivial.
Simpl.
Trivial.
Save.

(* IGUALDAD ======= *)
(* igualdad para los naturales *)
Fixpoint egal_nat[n:nat]:nat->bool:=
[m:nat]
Cases n m of
O O=>true
|(S n) (S m)=>(egal_nat n m)
|_ _=>false
end.

(* comprobacion de igualdad con cero *)
Definition es_cero[n:nat]:=
Cases n of
O=>true
|(S n)=>false
end.

(* igualdad para los naturales, VERSION _REC *)
Definition egal_natt:=[n:nat]
(nat_rec [_:nat]bool (if (es_cero n) then true else false)
[indice:nat][k:bool](if (k) then false else 
			(if (es_cero (minus (S indice) n)) 
				then true 
				else false)
		    )			
).



(* ===== DEFINICION DE ENTEROS ===== *)
Inductive Set Z:=
cero:Z
|pos:nat->Z
|neg:nat->Z.


(* primera version de opuestos de enteros *)
Definition opuestoZ[a:Z]:=
Cases a of
cero=>cero
|(pos n)=>(neg n)
|(neg n)=>(pos n)
end.

(* segunda version de opuestos de enteros *)
Definition opu_Z[a:Z]:=
Cases a of
cero=>cero
|(pos n)=>(neg n)
|(neg n)=>(pos n)
end.

(* opuesto de un entero, VERSION _REC *)
Definition mi_opuesto:=
(Z_rec ([_:Z]Z) cero [v:nat](neg v) [vn:nat](pos vn)).


(* siguiente de un entero *)
Definition sigZ[a:Z]:=
Cases a of
cero=>(pos O)
|(pos n)=>(pos (S n))
|(neg O)=>cero
|(neg (S n))=>(neg n)
end.

(* predecesor de un entero *)
Definition predZ[a:Z]:=
Cases a of
cero=>(neg O)
|(pos (S n))=>(pos  n)
|(pos O)=>cero
|(neg n)=>(neg (S n))
end.


(* igual a signo(a)*(abs(a)+1) *)
Definition absZ[a:Z]:=
Cases a of
cero=>(pos O)
|(pos n)=>(pos (S n))
|(neg n)=>(neg (S n))
end.

(* proyeccion de nat sobre Z, impares son positivos, pares negativos *)
Fixpoint semantica[n:nat]:Z:=
Cases n of
O=>cero
|(S O)=>(pos O)
|(S(S O))=>(neg O)
|(S(S n))=>(absZ (semantica n))
end.


(* resta de dos naturales,resultado entero *)
Fixpoint difN[n:nat]:nat->Z:=
Cases n of 
O => ([n2:nat] Cases n2 of O=>cero | (S k)=>(neg k) end)
|(S l) => ([n2:nat] Cases n2 of O=>(pos l) | (S m)=> (difN l m) end)
end.

(* suma de dos naturales, resultado entero *)
Fixpoint sumZ[n:nat]:nat->Z:=
Cases n of
O => ([n2:nat] Cases n2 of O=>cero | (S k)=>(pos k) end)
|(S l) => ([n2:nat] Cases n2 of O=>(pos l) | (S m)=> (sigZ(sumZ l (S m))) end)
end.

(* suma de dos enteros, resultado entero *)
Definition suma[a,b:Z]:=<Z>Cases (a,b) of
(cero,v)=>v
|(v,cero)=>v
|((pos n),(pos m))=>(sumZ (S n) (S m))
|((pos n),(neg m))=>(difN (S n) (S m))
|((neg n),(pos m))=>(difN (S m) (S n))
|((neg n),(neg m))=>(opu_Z (sumZ (S n) (S m)))
end.

(* TONTERIAS =================================*)

(* proyeccion de los naturales sobre las expresiones *)
Fixpoint semExpr[e:expr]:Z:=
Cases e of
CERO => cero
| UNO => (pos O)
| (mas a b)=>(suma (semExpr a) (semExpr b))
| (menos a b)=>(suma (semExpr a) (opu_Z (semExpr b)))
end.

(* TONTERIAS =================================*)
(* lemas de los ejercicios *)
Lemma consUno:(n,m:nat)(n=m)->(pos n)=(pos m).
Intros.
Rewrite H.
Trivial.
Save.

Lemma consDos:(n,m:nat)(n=m)->(neg n)=(neg m).
Intros.
Rewrite H.
Trivial.
Save.

Lemma diffff:(n,m:nat)(difN (S n) (S m))=(difN n m).
Intros.
Simpl.
Trivial.
Save.

(*======= DEFINICIONES DE LISTAS =================================*)
(* Seccion de listas *)

(* definicion de las listas *)
Inductive lista[A:Set]:Set:=
Nil:(lista A)
|Cons:A->(lista A)->(lista A).

(* obtencion de la cola de una lista *)
Definition cdr[A:Set;l:(lista A)]:=<lista A>Cases l of
Nil=>(Nil A)
|(Cons A x)=>x
end.

(* obtiene la cola de una lista, VERSION _REC *)
Definition micdr:=[A:Set]
(lista_rec A [_:(lista A)](lista A) (Nil A) [_:A][l:(lista A)][_:(lista A)]l).

(* concatena dos listas *)
Fixpoint concat[A:Set;l:(lista A)]:(lista A)->(lista A):=
Cases l of
Nil=>[m:(lista A)]m
|(Cons x cd)=>[m:(lista A)](Cons A x (concat A cd m))
end.

(* concatena un elemento a una lista por detras, VERSION _REC *)
Definition mi_concatenar:=[A:Set;e:A]
(lista_rec A [_:(lista A)](lista A)
	(Cons A e (Nil A))
	[x:A;_:(lista A);l2:(lista A)](Cons A x l2)
).

(* concatena dos listas, VERSION _REC, NO FUNCIONA *)
(*
Definition mi_concat:=[A:Set;l1:(lista A)]
(lista_rec A [_:(lista A)](lista A) (invertir A l1)
	[x:A;la:(lista A)][l2:(lista A)](Cons A x l2)
).
*)

(* comprobacion *)
(*
Eval Compute in (concat nat (Cons nat (3) (Cons nat (2) (Nil nat))) (Cons nat (1) (Cons nat (0) (Nil nat)))).
*)

(* obtiene la longitud de una lista *)
Fixpoint longit[A:Set;l:(lista A)]:nat:=
Cases l of
Nil=>O
|(Cons _ cd)=>(S (longit A cd))
end.


(* obtiene la longitud de una lista , VERSION _REC*)
Definition milongit:=[A:Set]
(lista_rec A ([_:(lista A)]nat) O [_:A][l:(lista A)]S).

(* invierte una lista *)
Fixpoint invertir[A:Set;l:(lista A)]:(lista A):=
Cases l of
Nil => (Nil A)
|(Cons x l')=>(concat A (invertir A l') (Cons A x (Nil A)))
end.

(* invierte una lista, VERSION _REC *)
Definition miinvertir:=[A:Set]
(lista_rec A ([_:(lista A)](lista A)) (Nil A) [v:A][l:(lista A)][m:(lista A)]
(concat A m (Cons A v (Nil A)))).

(* cuenta el numero de ocurrencias de un entero en una lista de enteros *)
Fixpoint nocc[e:nat;l:(lista nat)]:nat:=
Cases l of
Nil => O
|(Cons x v)=>(if (egal_nat e x) then (S (nocc e v)) else (nocc e v))
end.

(* cuenta el numero de ocurrencias de un entero en una lista de enteros, VERSION _REC *)
Definition mi_nocc:=[e:nat]
(lista_rec nat [_:(lista nat)]nat O 
	([i:nat;l:(lista nat);anterior:nat](if (egal_nat anterior e) 
						then (S i)
						else i)
	)
).

(* obtiene la primera posicion de un elemento en una lista,funcion auxiliar *)
Fixpoint posicion_aux[e:nat;l:(lista nat)]:nat->nat:=[i:nat]
Cases l of
Nil=>O
|(Cons x l')=>(if (egal_nat e x) then (S i) else (posicion_aux e l' (S i)))
end.

(* obtiene la primera posicion de un elemento en una lista *)
Definition posicion:=[e:nat;l:(lista nat)](posicion_aux e l O).

(* obtiene la primera posicion de un elemento en una lista, VERSION _REC *)
Definition mi_posicion:=[e:nat]
(lista_rec nat [_:(lista nat)]nat O
	[y:nat;li:(lista nat)][ant:nat](if (egal_nat y e) then (S O)
					else (if (egal_nat O ant) 
						then O 
						else (S ant)
					      )
					)
).



(*=================================*)


(* not de un valor booleano *)
Definition mi_not[b:bool]:=
Case b of false true end.

(* operacion xor sobre booleanos *)
Definition mxor[b1,b2:bool]:=
Cases b1 b2 of
false b2=>b2
|true b2=>(mi_not b2)
end.

(* operacion xor sobre booleanos, VERSION _REC *)
Definition mi_xor:=[b:bool]
(bool_rec ([_:bool]bool) (mi_not b) b).

(*===== ENTEROS ALTERNATIVOS =================================*)
(*
Definicion de los enteros independientes, para hacer la suma de enteros recursivamente
*)
Inductive Set ZZ:=
cc:ZZ
|pp:ZZ->ZZ
|nn:ZZ->ZZ.

Definition sssig[l:ZZ]:=
Cases l of
cc=>(pp cc)
|(pp u)=>(pp l)
|(nn y)=>y
end.

Definition pppred[l:ZZ]:=
Cases l of
cc=>(nn cc)
|(pp u)=>u
|(nn y)=>(nn l)
end.

Fixpoint sumaZ[z1:ZZ]:ZZ->ZZ:=
[z2:ZZ]
Cases z1 of
cc=>z2
|(pp k)	=>(sumaZ k (sssig z2))
|(nn k)	=>(sumaZ k (pppred z2))
end.

(*=================================*)

