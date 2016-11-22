(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes ()
  ((Char (A)
     (B) (C) (D) (E) (F) (G) (H) (I) (J) (K) (L) (M) (N) (O) (P) (Q) (R)
     (S2) (T) (U) (V) (W) (X) (Y) (Z2))))
(declare-datatypes ()
  ((Edit (Insert (Insert_0 Char) (Insert_1 Nat))
     (Delete (Delete_0 Nat)) (Subst (Subst_0 Char) (Subst_1 Nat)))))
(declare-datatypes ()
  ((list2 (Nil2) (Cons2 (Cons_02 Edit) (Cons_12 list2)))))
(declare-datatypes ()
  ((list (Nil) (Cons (Cons_0 Char) (Cons_1 list)))))
(define-fun-rec
  take
    ((x Nat) (y list)) list
    (match x
      (case Z Nil)
      (case (S z)
        (match y
          (case Nil Nil)
          (case (Cons x2 x3) (Cons x2 (take z x3)))))))
(define-fun-rec
  drop
    ((x Nat) (y list)) list
    (match x
      (case Z y)
      (case (S z)
        (match y
          (case Nil Nil)
          (case (Cons x2 x3) (drop z x3))))))
(define-fun-rec
  append
    ((x list) (y list)) list
    (match x
      (case Nil y)
      (case (Cons z xs) (Cons z (append xs y)))))
(define-fun
  edit
    ((x Edit) (y list)) list
    (match x
      (case (Insert c n)
        (append (take n y) (append (Cons c Nil) (drop n y))))
      (case (Delete m) (append (take m y) (drop (S m) y)))
      (case (Subst c2 o)
        (append (take o y) (append (Cons c2 Nil) (drop (S o) y))))))
(define-fun-rec
  edits
    ((x list2) (y list)) list
    (match x
      (case Nil2 y)
      (case (Cons2 e es) (edits es (edit e y)))))
(assert-not
  (forall ((a Edit) (b Edit))
    (distinct
      (edits (Cons2 a (Cons2 b Nil2))
        (Cons K (Cons I (Cons T (Cons T (Cons E (Cons N Nil)))))))
      (Cons M
        (Cons I (Cons T (Cons T (Cons E (Cons N (Cons S2 Nil))))))))))
(check-sat)
