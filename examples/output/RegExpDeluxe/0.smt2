(declare-datatypes () ((T (A) (B) (C))))
(declare-datatypes ()
  ((list (Nil) (Cons (Cons_0 T) (Cons_1 list)))))
(declare-datatypes ()
  ((R (Nil2)
     (Eps) (Atom (Atom_0 T)) (+2 (+_0 R) (+_1 R)) (& (&_0 R) (&_1 R))
     (>2 (>_0 R) (>_1 R)) (Star (Star_0 R)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(define-fun
  minus1
    ((x Nat)) Nat
    (match x
      (case Z Z)
      (case (S y) y)))
(define-fun-rec
  minn
    ((x Nat) (y Nat)) Nat
    (match x
      (case Z Z)
      (case (S z)
        (match y
          (case Z Z)
          (case (S b) (S (minn z b)))))))
(define-fun-rec
  maxx
    ((x Nat) (y Nat)) Nat
    (match x
      (case Z y)
      (case (S a)
        (match y
          (case Z x)
          (case (S b) (S (maxx a b)))))))
(define-fun
  isZero2
    ((x Nat)) Bool
    (match x
      (case Z true)
      (case (S y) false)))
(define-fun
  eqT
    ((x T) (y T)) Bool
    (match x
      (case A
        (match y
          (case default false)
          (case A true)))
      (case B
        (match y
          (case default false)
          (case B true)))
      (case C
        (match y
          (case default false)
          (case C true)))))
(define-fun-rec
  eps
    ((x R)) Bool
    (match x
      (case default false)
      (case Eps true)
      (case (+2 q r) (or (eps q) (eps r)))
      (case (& p2 q2) (and (eps p2) (eps q2)))
      (case (>2 p3 q3) (and (eps p3) (eps q3)))
      (case (Star y) true)))
(define-fun cond ((x Bool)) R (ite x Eps Nil2))
(define-fun-rec
  rep
    ((x R) (y Nat) (z Nat)) R
    (match z
      (case Z
        (match y
          (case Z Eps)
          (case (S x2) Nil2)))
      (case (S j) (>2 (+2 (cond (isZero2 y)) x) (rep x (minus1 y) j)))))
(define-fun
  .>.
    ((x R) (y R)) R
    (match x
      (case default
        (match y
          (case default
            (match x
              (case default
                (match y
                  (case default (>2 x y))
                  (case Eps x)))
              (case Eps y)))
          (case Nil2 Nil2)))
      (case Nil2 Nil2)))
(define-fun
  .+.
    ((x R) (y R)) R
    (match x
      (case default
        (match y
          (case default (+2 x y))
          (case Nil2 x)))
      (case Nil2 y)))
(define-fun
  .&.
    ((x R) (y R)) R
    (match x
      (case default
        (match y
          (case default (& x y))
          (case Nil2 Nil2)))
      (case Nil2 Nil2)))
(define-fun-rec
  step
    ((x R) (y T)) R
    (match x
      (case default Nil2)
      (case (Atom b) (ite (eqT b y) Eps Nil2))
      (case (+2 q r) (.+. (step q y) (step r y)))
      (case (& p2 q2) (.&. (step p2 y) (step q2 y)))
      (case (>2 p3 q3)
        (ite
          (eps p3) (.+. (.>. (step p3 y) q3) (step q3 y))
          (.+. (.>. (step p3 y) q3) Nil2)))
      (case (Star p4) (.>. (step p4 y) x))))
(define-fun-rec
  rec
    ((x R) (y list)) Bool
    (match y
      (case Nil (eps x))
      (case (Cons z xs) (rec (step x z) xs))))
(assert-not
  (forall ((q R) (i Nat) (j Nat) (k Nat) (j2 Nat) (s list))
    (=> (not (eps q))
      (= (rec (& (rep q i k) (rep q j j2)) s)
        (rec (rep q (maxx i j) (minn k j2)) s)))))
(check-sat)
