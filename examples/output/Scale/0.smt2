(declare-datatypes ()
  ((Object (O1)
     (O2) (O3) (O4) (O5) (O6) (O7) (O8) (O9) (O10) (O11) (O12))))
(declare-datatypes ()
  ((Pair (Pair2 (first Bool) (second Object)))))
(declare-datatypes ()
  ((list (Nil) (Cons (Cons_0 Pair) (Cons_1 list)))))
(declare-datatypes ()
  ((list2 (Nil2) (Cons2 (Cons_02 Object) (Cons_12 list2)))))
(declare-datatypes ()
  ((Schema (Answer (Answer_0 Bool) (Answer_1 Object))
     (Weigh (Weigh_0 list2)
       (Weigh_1 list2) (Weigh_2 Schema) (Weigh_3 Schema)
       (Weigh_4 Schema)))))
(declare-datatypes () ((Nat (Zero) (Succ (pred Nat)))))
(define-fun
  ~~
    ((x Object) (y Object)) Bool
    (match x
      (case O1
        (match y
          (case default false)
          (case O1 true)))
      (case O2
        (match y
          (case default false)
          (case O2 true)))
      (case O3
        (match y
          (case default false)
          (case O3 true)))
      (case O4
        (match y
          (case default false)
          (case O4 true)))
      (case O5
        (match y
          (case default false)
          (case O5 true)))
      (case O6
        (match y
          (case default false)
          (case O6 true)))
      (case O7
        (match y
          (case default false)
          (case O7 true)))
      (case O8
        (match y
          (case default false)
          (case O8 true)))
      (case O9
        (match y
          (case default false)
          (case O9 true)))
      (case O10
        (match y
          (case default false)
          (case O10 true)))
      (case O11
        (match y
          (case default false)
          (case O11 true)))
      (case O12
        (match y
          (case default false)
          (case O12 true)))))
(define-fun-rec
  weigh
    ((x Bool) (y Object) (z list2) (x2 list2) (x3 Schema) (x4 Schema)
     (x5 Schema))
    Schema
    (match z
      (case Nil2 x4)
      (case (Cons2 b bs)
        (match x2
          (case Nil2 x4)
          (case (Cons2 c cs)
            (ite
              (~~ y b) (ite x x3 x5)
              (ite (~~ y c) (ite x x5 x3) (weigh x y bs cs x3 x4 x5))))))))
(define-fun-rec
  sameSize
    ((x list2) (y list2)) Bool
    (match x
      (case Nil2
        (match y
          (case Nil2 true)
          (case (Cons2 z x2) false)))
      (case (Cons2 x3 xs)
        (match y
          (case Nil2 false)
          (case (Cons2 x4 ys) (sameSize xs ys))))))
(define-fun-rec
  len
    ((x list2) (y Nat)) Bool
    (match x
      (case Nil2 true)
      (case (Cons2 z xs)
        (match y
          (case Zero false)
          (case (Succ n) (len xs n))))))
(define-fun
  le
    ((x Object) (y Object)) Bool
    (match x
      (case default
        (match y
          (case default
            (match x
              (case default
                (match y
                  (case default
                    (match x
                      (case default
                        (match y
                          (case default
                            (match x
                              (case default
                                (match y
                                  (case default
                                    (match x
                                      (case default
                                        (match y
                                          (case default
                                            (match x
                                              (case default
                                                (match y
                                                  (case default
                                                    (match x
                                                      (case default
                                                        (match y
                                                          (case default
                                                            (match x
                                                              (case default
                                                                (match y
                                                                  (case default
                                                                    (match x
                                                                      (case default
                                                                        (match y
                                                                          (case default
                                                                            (match x
                                                                              (case default
                                                                                (match y
                                                                                  (case default
                                                                                    (match x
                                                                                      (case default
                                                                                        (match y
                                                                                          (case
                                                                                            default
                                                                                            true)
                                                                                          (case O11
                                                                                            false)))
                                                                                      (case O11
                                                                                        true)))
                                                                                  (case O10 false)))
                                                                              (case O10 true)))
                                                                          (case O9 false)))
                                                                      (case O9 true)))
                                                                  (case O8 false)))
                                                              (case O8 true)))
                                                          (case O7 false)))
                                                      (case O7 true)))
                                                  (case O6 false)))
                                              (case O6 true)))
                                          (case O5 false)))
                                      (case O5 true)))
                                  (case O4 false)))
                              (case O4 true)))
                          (case O3 false)))
                      (case O3 true)))
                  (case O2 false)))
              (case O2 true)))
          (case O1 false)))
      (case O1 true)))
(define-fun lt ((x Object) (y Object)) Bool (not (le y x)))
(define-fun-rec
  usorted
    ((x list2)) Bool
    (match x
      (case Nil2 true)
      (case (Cons2 y z)
        (match z
          (case Nil2 true)
          (case (Cons2 y2 xs) (and (lt y y2) (usorted z)))))))
(define-fun-rec
  disjoint
    ((x list2) (y list2)) Bool
    (match x
      (case Nil2 true)
      (case (Cons2 z xs)
        (match y
          (case Nil2 true)
          (case (Cons2 y2 ys)
            (ite
              (le z y2) (and (not (le y2 z)) (disjoint xs y))
              (disjoint x ys)))))))
(define-fun-rec
  isFine
    ((x Schema)) Bool
    (match x
      (case (Answer y z) true)
      (case (Weigh xs ys p q r)
        (and
          (and
            (and
              (and
                (and
                  (and
                    (and
                      (and (len xs (Succ (Succ (Succ (Succ Zero)))))
                        (len ys (Succ (Succ (Succ (Succ Zero))))))
                      (usorted xs))
                    (usorted ys))
                  (disjoint xs ys))
                (sameSize xs ys))
              (isFine p))
            (isFine q))
          (isFine r)))))
(define-fun-rec
  depth
    ((x Nat) (y Schema)) Bool
    (match x
      (case Zero
        (match y
          (case (Answer z x2) true)
          (case (Weigh x3 x4 x5 x6 x7) false)))
      (case (Succ n)
        (match y
          (case (Answer x8 x9) false)
          (case (Weigh x10 x11 p q r)
            (and (and (depth n p) (depth n q)) (depth n r)))))))
(define-fun
  allCases
    () list
    (Cons (Pair2 false O1)
      (Cons (Pair2 false O2)
        (Cons (Pair2 false O3)
          (Cons (Pair2 false O4)
            (Cons (Pair2 false O5)
              (Cons (Pair2 false O6)
                (Cons (Pair2 false O7)
                  (Cons (Pair2 false O8)
                    (Cons (Pair2 false O9)
                      (Cons (Pair2 false O10)
                        (Cons (Pair2 false O11)
                          (Cons (Pair2 false O12)
                            (Cons (Pair2 true O1)
                              (Cons (Pair2 true O2)
                                (Cons (Pair2 true O3)
                                  (Cons (Pair2 true O4)
                                    (Cons (Pair2 true O5)
                                      (Cons (Pair2 true O6)
                                        (Cons (Pair2 true O7)
                                          (Cons (Pair2 true O8)
                                            (Cons (Pair2 true O9)
                                              (Cons (Pair2 true O10)
                                                (Cons (Pair2 true O11)
                                                  (Cons (Pair2 true O12)
                                                    Nil)))))))))))))))))))))))))
(define-fun =~ ((x Bool) (y Bool)) Bool (ite x y (not y)))
(define-fun-rec
  solves
    ((x Schema) (y Bool) (z Object)) Bool
    (match x
      (case (Answer hx x2) (and (=~ hx y) (~~ x2 z)))
      (case (Weigh xs ys p q r) (solves (weigh y z xs ys p q r) y z))))
(define-fun-rec
  solvesAll
    ((x Schema) (y list)) Bool
    (match y
      (case Nil true)
      (case (Cons z css)
        (match z
          (case (Pair2 h o) (and (solves x h o) (solvesAll x css)))))))
(define-fun
  isSolution
    ((x Schema)) Bool (and (isFine x) (solvesAll x allCases)))
(assert-not
  (forall ((s Schema))
    (=> (depth (Succ (Succ (Succ Zero))) s) (not (isSolution s)))))
(check-sat)
