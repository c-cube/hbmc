(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-const error Bool)
(define-fun-rec
  plus
    ((x Nat) (y Nat)) Nat
    (match x
      (case Z y)
      (case (S n) (S (plus n y)))))
(define-fun-rec
  mult
    ((x Nat) (y Nat)) Nat
    (match x
      (case Z Z)
      (case (S n) (plus y (mult n y)))))
(define-fun-rec
  minus
    ((x Nat) (y Nat)) Nat
    (match x
      (case Z
        (match y
          (case Z Z)
          (case (S z) Z)))
      (case (S n)
        (match y
          (case Z x)
          (case (S m) (minus n m))))))
(define-fun-rec
  lt
    ((x Nat) (y Nat)) Bool
    (match x
      (case Z true)
      (case (S n)
        (match y
          (case Z error)
          (case (S m) (lt n m))))))
(define-fun-rec
  id
    ((x Nat)) Nat
    (match x
      (case Z Z)
      (case (S n) (S (id n)))))
(assert-not (forall ((x Nat)) (= (S x) x)))
(check-sat)
