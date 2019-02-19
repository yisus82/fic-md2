 Definition masdos :=
 	(nat_rec 
 	[_:nat]nat
	 (S (S O))
  [n:nat][rec:nat](S rec)).

 Definition sumauno :=
	(nat_rec
	[_:nat]nat
	(S O)
	[n:nat][rec:nat](S rec)).


 Definition minimo :=
	(nat_rec
	[_:nat]nat->nat
	[n:nat]O
	[a:nat][rec:nat->nat] 
	[b:nat] Cases b of
		O => O
	   | (S n) => (S (rec n))
	end).


 Definition maximo :=
	(nat_rec 
	[_:nat]nat->nat
	[b:nat]b
	[a:nat][rec:nat->nat]
	[c:nat] Cases c of
		O => (S a)
	    |(S n) => (S (rec n))
	end).

 Definition pordos :=
 (nat_rec 
[_:nat]nat
 O
[n:nat][rec:nat](S (S rec))).


Definition longitud :=
	(list_rec
	[_:list]nat
	O
	[a:A; l:list][rec:nat]
	(S rec)).

Definition concatenar :=
	(list_rec
	[_:list]list->list
	[b:list]b
	[a:A; l:list][rec:list->list]
	[l2:list] Cases l2 of
		nil => (cons a l)
	    | (cons x y) => (cons a (rec (cons x y)))
	end).


Definition sumaunopos :=
	(positive_rec 
	[_:positive]positive
	[p:positive][rec1:positive](xO rec1)
	[q:positive][rec2:positive](xI q)
	(xO xH)
	).


Definition sumadospos :=
	(positive_rec 
	[_:positive]positive
	[p:positive][rec1:positive](xO rec2)
	[q:positive][rec2:positive](x0 rec1)
	(xI xH)
	).
	

Fixpoint concatenar2 [l:list]:list->list :=
	[m:list]Cases l of
        nil=>m
       |(cons x y)=>(Cases m of
			nil=>l
         	|(cons a b)=>(cons x (concatenar2 y (cons a b)))
                     end)
      end.



Lemma concat : list->list->list.
Intro l1.
Induction l1.
Intro l2.
Exact l2.
Intro l2.
Induction l2.
Exact (cons a l1).
Exact (cons a (Hrecl1 l2)).


Section uno.
Variables A, B:Prop.
Variables a:A; b:B.
Lemma l : ((left A B a) = (right A B b))->False.
Intros.
Inversion H.
End uno.


Lemma uno : (n:nat)(le O n).
Intro n.
Elim n.
Constructor.

Intro.
Intro.
Constructor 2.
Assumption.


Definition maximo := (nat_rec
	[_:nat]nat->nat
	[x:nat]x
	[n:nat][rec:nat->nat]
	[y:nat] Cases y of
		O => (S n)
	   | (S n2) => (S (rec n2))
end).

Theorem max : (n,m:nat) (le n m)->(maximo n m)=m.