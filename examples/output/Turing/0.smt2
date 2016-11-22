(declare-datatypes () ((Nat (Zero) (Succ (pred Nat)))))
(declare-datatypes ()
  ((Action (Lft (Lft_0 Nat)) (Rgt (Rgt_0 Nat)) (Stp))))
(declare-datatypes () ((A (O) (A2) (B))))
(declare-datatypes () ((Pair3 (Pair22 (first2 Nat) (second2 A)))))
(declare-datatypes ()
  ((Pair4 (Pair24 (first4 A) (second4 Action)))))
(declare-datatypes ()
  ((Pair (Pair2 (first Pair3) (second Pair4)))))
(declare-datatypes ()
  ((list (Nil) (Cons (Cons_0 Pair) (Cons_1 list)))))
(declare-datatypes ()
  ((list2 (Nil2) (Cons2 (Cons_02 A) (Cons_12 list2)))))
(declare-datatypes ()
  ((Pair5 (Pair23 (first3 A) (second3 list2)))))
(declare-datatypes ()
  ((Triple
     (Triple2 (Triple_0 Nat) (Triple_1 list2) (Triple_2 list2)))))
(declare-datatypes ()
  ((Either (Left (Left_0 list2)) (Right (Right_0 Triple)))))
(define-fun
  split
    ((x list2)) Pair5
    (match x
      (case Nil2 (Pair23 O Nil2))
      (case (Cons2 y xs) (Pair23 y xs))))
(define-fun-rec
  rev
    ((x list2) (y list2)) list2
    (match x
      (case Nil2 y)
      (case (Cons2 z xs)
        (match z
          (case default (rev xs (Cons2 z y)))
          (case O y)))))
(define-fun
  eqA
    ((x A) (y A)) Bool
    (match x
      (case O
        (match y
          (case default false)
          (case O true)))
      (case A2
        (match y
          (case default false)
          (case A2 true)))
      (case B
        (match y
          (case default false)
          (case B true)))))
(define-fun-rec
  eqT
    ((x Pair3) (y Pair3)) Bool
    (match x
      (case (Pair22 z c)
        (match z
          (case Zero
            (match y
              (case (Pair22 x2 b2)
                (match x2
                  (case Zero (eqA c b2))
                  (case (Succ x3) false)))))
          (case (Succ p)
            (match y
              (case (Pair22 x4 b3)
                (match x4
                  (case Zero false)
                  (case (Succ q) (eqT (Pair22 p c) (Pair22 q b3)))))))))))
(define-fun-rec
  apply
    ((x list) (y Pair3)) Pair4
    (match x
      (case Nil (Pair24 O Stp))
      (case (Cons z q)
        (match z (case (Pair2 sa rhs) (ite (eqT sa y) rhs (apply q y)))))))
(define-fun
  act
    ((x Action) (y list2) (z A) (x2 list2)) Either
    (match x
      (case (Lft s)
        (match (split y)
          (case (Pair23 y2 lft)
            (Right (Triple2 s lft (Cons2 y2 (Cons2 z x2)))))))
      (case (Rgt t) (Right (Triple2 t (Cons2 z y) x2)))
      (case Stp (Left (rev y (Cons2 z x2))))))
(define-fun
  step
    ((x list) (y Triple)) Either
    (match y
      (case (Triple2 s lft rgt)
        (match (split rgt)
          (case (Pair23 z rgt2)
            (match (apply x (Pair22 s z))
              (case (Pair24 x2 what) (act what lft x2 rgt2))))))))
(define-fun-rec
  steps
    ((x list) (y Triple)) list2
    (match (step x y)
      (case (Left tape) tape)
      (case (Right st) (steps x st))))
(define-fun
  runt ((x list) (y list2)) list2 (steps x (Triple2 Zero Nil2 y)))
(define-fun
  prog0
    ((x list)) Bool
    (match (runt x (Cons2 A2 Nil2))
      (case Nil2 false)
      (case (Cons2 y z)
        (match y
          (case default false)
          (case A2
            (match z
              (case Nil2
                (match
                  (runt x
                    (Cons2 B
                      (Cons2 A2 (Cons2 A2 (Cons2 A2 (Cons2 A2 (Cons2 B Nil2)))))))
                  (case Nil2 false)
                  (case (Cons2 x2 x3)
                    (match x2
                      (case default false)
                      (case A2
                        (match x3
                          (case Nil2 false)
                          (case (Cons2 x4 x5)
                            (match x4
                              (case default false)
                              (case A2
                                (match x5
                                  (case Nil2 false)
                                  (case (Cons2 x6 x7)
                                    (match x6
                                      (case default false)
                                      (case A2
                                        (match x7
                                          (case Nil2 false)
                                          (case (Cons2 x8 x9)
                                            (match x8
                                              (case default false)
                                              (case A2
                                                (match x9
                                                  (case Nil2 false)
                                                  (case (Cons2 x10 x11)
                                                    (match x10
                                                      (case default false)
                                                      (case B
                                                        (match x11
                                                          (case Nil2 false)
                                                          (case (Cons2 x12 x13)
                                                            (match x12
                                                              (case default false)
                                                              (case B
                                                                (match x13
                                                                  (case Nil2 true)
                                                                  (case (Cons2 x14 x15)
                                                                    false)))))))))))))))))))))))))))
              (case (Cons2 x16 x17) false)))))))
(assert-not (forall ((q list)) (not (prog0 q))))
(check-sat)
