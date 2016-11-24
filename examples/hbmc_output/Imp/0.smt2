(declare-datatypes (a)
  ((list (Nil) (Cons (Cons_0 a) (Cons_1 (list a))))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes ()
  ((E (N (N_0 Nat))
     (Add (Add_0 E) (Add_1 E)) (Mul (Mul_0 E) (Mul_1 E))
     (Eq (Eq_0 E) (Eq_1 E)) (V (V_0 Nat)))))
(declare-datatypes ()
  ((P (Print (Print_0 E))
     (=2 (=_0 Nat) (=_1 E)) (While (While_0 E) (While_1 (list P)))
     (If (If_0 E) (If_1 (list P)) (If_2 (list P))))))
(define-fun-rec
  store
    ((x (list Nat)) (y Nat) (z Nat)) (list Nat)
    (match x
      (case Nil
        (match y
          (case Z (Cons z (as Nil (list Nat))))
          (case (S x2) (Cons Z (store (as Nil (list Nat)) x2 z)))))
      (case (Cons n st)
        (match y
          (case Z (Cons z st))
          (case (S x3) (Cons n (store st x3 z)))))))
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
  fetch
    ((x (list Nat)) (y Nat)) Nat
    (match x
      (case Nil Z)
      (case (Cons n st)
        (match y
          (case Z n)
          (case (S z) (fetch st z))))))
(define-fun-rec
  equal
    ((x Nat) (y Nat)) Bool
    (match x
      (case Z
        (match y
          (case Z true)
          (case (S z) false)))
      (case (S x2)
        (match y
          (case Z false)
          (case (S y2) (equal x2 y2))))))
(define-fun-rec
  eval
    ((x (list Nat)) (y E)) Nat
    (match y
      (case (N n) n)
      (case (Add a b) (plus (eval x a) (eval x b)))
      (case (Mul c b2) (mult (eval x c) (eval x b2)))
      (case (Eq a2 b3) (ite (equal (eval x a2) (eval x b3)) (S Z) Z))
      (case (V z) (fetch x z))))
(define-fun-rec
  (par (a)
    (append
       ((x (list a)) (y (list a))) (list a)
       (match x
         (case Nil y)
         (case (Cons z xs) (Cons z (append xs y)))))))
(define-fun
  opti
    ((x P)) P
    (match x
      (case default x)
      (case (While e q) (While e (append q q)))
      (case (If c r q2) (If c q2 r))))
(define-fun-rec
  run
    ((x (list Nat)) (y (list P))) (list Nat)
    (match y
      (case Nil (as Nil (list Nat)))
      (case (Cons z r)
        (match z
          (case (Print e) (Cons (eval x e) (run x r)))
          (case (=2 x2 e2) (run (store x x2 (eval x e2)) r))
          (case (While e3 q)
            (run x
              (Cons
                (If e3 (append q (Cons z (as Nil (list P)))) (as Nil (list P)))
                r)))
          (case (If e4 p2 q2)
            (ite
              (equal (eval x e4) Z) (run x (append q2 r))
              (run x (append p2 r))))))))
(assert-not
  (forall ((q P))
    (= (run (as Nil (list Nat)) (Cons q (as Nil (list P))))
      (run (as Nil (list Nat)) (Cons (opti q) (as Nil (list P)))))))
(check-sat)
