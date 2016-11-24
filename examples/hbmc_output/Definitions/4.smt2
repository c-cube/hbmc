(declare-datatypes (a)
  ((list (Nil) (Cons (Cons_0 a) (Cons_1 (list a))))))
(declare-datatypes () ((Nat (S (p Nat)) (Z))))
(declare-const (par (eta0) (error eta0)))
(define-fun-rec
  lt
    ((x Nat) (y Nat)) Bool
    (match x
      (case (S z)
        (match y
          (case (S y2) (lt z y2))
          (case Z (as error Bool))))
      (case Z true)))
(define-fun-rec
  (par (a)
    (length
       ((x (list a))) Nat
       (match x
         (case Nil Z)
         (case (Cons y xs) (S (length xs)))))))
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
    ((x Nat) (y (list Nat))) Bool
    (match y
      (case Nil false)
      (case (Cons z xs) (or (eqNat x z) (elem x xs)))))
(define-fun-rec
  union2
    ((x (list Nat)) (y (list Nat))) (list Nat)
    (match x
      (case Nil y)
      (case (Cons z xs)
        (ite (elem z y) (union2 xs y) (Cons z (union2 xs y))))))
(define-fun-rec
  (par (a)
    (drop
       ((x Nat) (y (list a))) (list a)
       (match x
         (case (S z)
           (match y
             (case Nil (as error (list a)))
             (case (Cons x2 xs) (drop z xs))))
         (case Z y)))))
(define-fun-rec
  (par (a)
    (append
       ((x (list a)) (y (list a))) (list a)
       (match x
         (case Nil y)
         (case (Cons z xs) (Cons z (append xs y)))))))
(define-fun-rec
  (par (a)
    (rotate
       ((x Nat) (y (list a))) (list a)
       (match x
         (case (S n)
           (match y
             (case Nil (as error (list a)))
             (case (Cons z xs)
               (rotate n (append xs (Cons z (as Nil (list a))))))))
         (case Z y)))))
(assert-not
  (forall ((n Nat) (xs (list Nat)) (ys (list Nat)))
    (=> (= (drop n xs) (drop n ys)) (= xs ys))))
(check-sat)
