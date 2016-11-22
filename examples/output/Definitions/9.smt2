(declare-datatypes () ((Nat (S (p Nat)) (Z))))
(declare-datatypes ()
  ((list (Nil) (Cons (Cons_0 Nat) (Cons_1 list)))))
(declare-const error list)
(declare-const error2 Bool)
(define-fun-rec
  lt
    ((x Nat) (y Nat)) Bool
    (match x
      (case (S z)
        (match y
          (case (S y2) (lt z y2))
          (case Z error2)))
      (case Z true)))
(define-fun-rec
  length
    ((x list)) Nat
    (match x
      (case Nil Z)
      (case (Cons y xs) (S (length xs)))))
(define-fun-rec
  eqNat
    ((x Nat) (y Nat)) Bool
    (match x
      (case (S z)
        (match y
          (case (S y2) (eqNat z y2))
          (case Z false)))
      (case Z
        (match y
          (case (S x2) false)
          (case Z true)))))
(define-fun-rec
  elem
    ((x Nat) (y list)) Bool
    (match y
      (case Nil false)
      (case (Cons z xs) (or (eqNat x z) (elem x xs)))))
(define-fun-rec
  union2
    ((x list) (y list)) list
    (match x
      (case Nil y)
      (case (Cons z xs)
        (ite (elem z y) (union2 xs y) (Cons z (union2 xs y))))))
(define-fun-rec
  drop
    ((x Nat) (y list)) list
    (match x
      (case (S z)
        (match y
          (case Nil error)
          (case (Cons x2 xs) (drop z xs))))
      (case Z y)))
(define-fun-rec
  append
    ((x list) (y list)) list
    (match x
      (case Nil y)
      (case (Cons z xs) (Cons z (append xs y)))))
(define-fun-rec
  rotate
    ((x Nat) (y list)) list
    (match x
      (case (S n)
        (match y
          (case Nil error)
          (case (Cons z xs) (rotate n (append xs (Cons z Nil))))))
      (case Z y)))
(assert-not
  (forall ((xs list) (ys list) (zs list))
    (=> (= (append xs ys) (append xs zs)) (= ys zs))))
(check-sat)
