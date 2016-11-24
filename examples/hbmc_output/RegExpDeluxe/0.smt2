(declare-datatypes (a)
  ((list (Nil) (Cons (Cons_0 a) (Cons_1 (list a))))))
(declare-datatypes () ((T (A) (B) (C))))
(declare-datatypes (a)
  ((R (Nil2)
     (Eps) (Atom (Atom_0 a)) (+2 (+_0 (R a)) (+_1 (R a)))
     (& (&_0 (R a)) (&_1 (R a))) (>2 (>_0 (R a)) (>_1 (R a)))
     (Star (Star_0 (R a))))))
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
    ((x (R T))) Bool
    (match x
      (case default false)
      (case Eps true)
      (case (+2 q r) (or (eps q) (eps r)))
      (case (& p2 q2) (and (eps p2) (eps q2)))
      (case (>2 p3 q3) (and (eps p3) (eps q3)))
      (case (Star y) true)))
(define-fun
  cond ((x Bool)) (R T) (ite x (as Eps (R T)) (as Nil2 (R T))))
(define-fun-rec
  rep
    ((x (R T)) (y Nat) (z Nat)) (R T)
    (match z
      (case Z
        (match y
          (case Z (as Eps (R T)))
          (case (S x2) (as Nil2 (R T)))))
      (case (S j) (>2 (+2 (cond (isZero2 y)) x) (rep x (minus1 y) j)))))
(define-fun
  .>.
    ((x (R T)) (y (R T))) (R T)
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
          (case Nil2 (as Nil2 (R T)))))
      (case Nil2 (as Nil2 (R T)))))
(define-fun
  .+.
    ((x (R T)) (y (R T))) (R T)
    (match x
      (case default
        (match y
          (case default (+2 x y))
          (case Nil2 x)))
      (case Nil2 y)))
(define-fun
  .&.
    ((x (R T)) (y (R T))) (R T)
    (match x
      (case default
        (match y
          (case default (& x y))
          (case Nil2 (as Nil2 (R T)))))
      (case Nil2 (as Nil2 (R T)))))
(define-fun-rec
  step
    ((x (R T)) (y T)) (R T)
    (match x
      (case default (as Nil2 (R T)))
      (case (Atom b) (ite (eqT b y) (as Eps (R T)) (as Nil2 (R T))))
      (case (+2 q r) (.+. (step q y) (step r y)))
      (case (& p2 q2) (.&. (step p2 y) (step q2 y)))
      (case (>2 p3 q3)
        (ite
          (eps p3) (.+. (.>. (step p3 y) q3) (step q3 y))
          (.+. (.>. (step p3 y) q3) (as Nil2 (R T)))))
      (case (Star p4) (.>. (step p4 y) x))))
(define-fun-rec
  rec
    ((x (R T)) (y (list T))) Bool
    (match y
      (case Nil (eps x))
      (case (Cons z xs) (rec (step x z) xs))))
(assert-not
  (forall ((q (R T)) (i Nat) (j Nat) (k Nat) (j2 Nat) (s (list T)))
    (=> (not (eps q))
      (= (rec (& (rep q i k) (rep q j j2)) s)
        (rec (rep q (maxx i j) (minn k j2)) s)))))
(check-sat)
