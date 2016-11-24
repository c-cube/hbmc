(declare-datatypes (a)
  ((list (Nil) (Cons (Cons_0 a) (Cons_1 (list a))))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes ()
  ((Char (A)
     (B) (C) (D) (E) (F) (G) (H) (I) (J) (K) (L) (M) (N) (O) (P) (Q) (R)
     (S2) (T) (U) (V) (W) (X) (Y) (Z2))))
(declare-datatypes ()
  ((Edit (Insert (Insert_0 Char) (Insert_1 Nat))
     (Delete (Delete_0 Nat)) (Subst (Subst_0 Char) (Subst_1 Nat)))))
(define-fun-rec
  (par (a)
    (take
       ((x Nat) (y (list a))) (list a)
       (match x
         (case Z (as Nil (list a)))
         (case (S z)
           (match y
             (case Nil (as Nil (list a)))
             (case (Cons x2 x3) (Cons x2 (take z x3)))))))))
(define-fun-rec
  (par (a)
    (drop
       ((x Nat) (y (list a))) (list a)
       (match x
         (case Z y)
         (case (S z)
           (match y
             (case Nil (as Nil (list a)))
             (case (Cons x2 x3) (drop z x3))))))))
(define-fun-rec
  (par (a)
    (append
       ((x (list a)) (y (list a))) (list a)
       (match x
         (case Nil y)
         (case (Cons z xs) (Cons z (append xs y)))))))
(define-fun
  edit
    ((x Edit) (y (list Char))) (list Char)
    (match x
      (case (Insert c n)
        (append (take n y)
          (append (Cons c (as Nil (list Char))) (drop n y))))
      (case (Delete m) (append (take m y) (drop (S m) y)))
      (case (Subst c2 o)
        (append (take o y)
          (append (Cons c2 (as Nil (list Char))) (drop (S o) y))))))
(define-fun-rec
  edits
    ((x (list Edit)) (y (list Char))) (list Char)
    (match x
      (case Nil y)
      (case (Cons e es) (edits es (edit e y)))))
(assert-not
  (forall ((a Edit) (b Edit))
    (distinct
      (edits (Cons a (Cons b (as Nil (list Edit))))
        (Cons K
          (Cons I (Cons T (Cons T (Cons E (Cons N (as Nil (list Char)))))))))
      (Cons M
        (Cons I
          (Cons T
            (Cons T (Cons E (Cons N (Cons S2 (as Nil (list Char))))))))))))
(check-sat)
