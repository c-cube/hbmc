(declare-sort sk 0)
(declare-sort sk2 0)
(declare-datatypes ()
  ((list2 (Nil2) (Cons2 (Cons_02 sk2) (Cons_12 list2)))))
(declare-datatypes ()
  ((list (Nil) (Cons (Cons_0 sk) (Cons_1 list)))))
(declare-datatypes () ((Q3 (Q22 (Q_02 list2) (Q_12 list2)))))
(declare-datatypes () ((Q (Q2 (Q_0 list) (Q_1 list)))))
(declare-datatypes ()
  ((Pair3 (Pair22 (first2 list2) (second2 list2)))))
(declare-datatypes () ((Pair (Pair2 (first list) (second list)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((Maybe4 (Nothing4) (Just4 (Just_04 sk2)))))
(declare-datatypes () ((Maybe3 (Nothing3) (Just3 (Just_03 sk)))))
(declare-datatypes () ((Maybe2 (Nothing2) (Just2 (Just_02 Q3)))))
(declare-datatypes () ((Maybe (Nothing) (Just (Just_0 Q)))))
(declare-datatypes ()
  ((E2 (Empty2)
     (EnqL2 (EnqL_02 sk2) (EnqL_12 E2))
     (EnqR2 (EnqR_02 E2) (EnqR_12 sk2)) (DeqL2 (DeqL_02 E2))
     (DeqR2 (DeqR_02 E2)) (App2 (App_02 E2) (App_12 E2)))))
(declare-datatypes ()
  ((E (Empty)
     (EnqL (EnqL_0 sk) (EnqL_1 E)) (EnqR (EnqR_0 E) (EnqR_1 sk))
     (DeqL (DeqL_0 E)) (DeqR (DeqR_0 E)) (App (App_0 E) (App_1 E)))))
(define-fun-rec
  take2
    ((x Nat) (y list2)) list2
    (match x
      (case Z Nil2)
      (case (S z)
        (match y
          (case Nil2 Nil2)
          (case (Cons2 x2 x3) (Cons2 x2 (take2 z x3)))))))
(define-fun-rec
  take
    ((x Nat) (y list)) list
    (match x
      (case Z Nil)
      (case (S z)
        (match y
          (case Nil Nil)
          (case (Cons x2 x3) (Cons x2 (take z x3)))))))
(define-fun
  tail2
    ((x list2)) list2
    (match x
      (case Nil2 Nil2)
      (case (Cons2 y xs) xs)))
(define-fun
  tail
    ((x list)) list
    (match x
      (case Nil Nil)
      (case (Cons y xs) xs)))
(define-fun-rec
  length2
    ((x list2)) Nat
    (match x
      (case Nil2 Z)
      (case (Cons2 y xs) (S (length2 xs)))))
(define-fun-rec
  length
    ((x list)) Nat
    (match x
      (case Nil Z)
      (case (Cons y xs) (S (length xs)))))
(define-fun-rec
  last
    ((x list2)) Maybe4
    (match x
      (case Nil2 Nothing4)
      (case (Cons2 y z)
        (match z
          (case Nil2 (Just4 y))
          (case (Cons2 x2 x3) (last z))))))
(define-fun-rec
  init2
    ((x list2)) list2
    (match x
      (case Nil2 Nil2)
      (case (Cons2 y z)
        (match z
          (case Nil2 Nil2)
          (case (Cons2 x2 x3) (Cons2 y (init2 z)))))))
(define-fun-rec
  init
    ((x list)) list
    (match x
      (case Nil Nil)
      (case (Cons y z)
        (match z
          (case Nil Nil)
          (case (Cons x2 x3) (Cons y (init z)))))))
(define-fun
  head
    ((x list)) Maybe3
    (match x
      (case Nil Nothing3)
      (case (Cons y z) (Just3 y))))
(define-fun-rec
  half
    ((x Nat)) Nat
    (match x
      (case Z Z)
      (case (S y)
        (match y
          (case Z Z)
          (case (S n) (S (half n)))))))
(define-fun
  fstR
    ((x Q3)) Maybe4
    (match x
      (case (Q22 y z)
        (let
          ((x2
              (match z
                (case Nil2 Nothing4)
                (case (Cons2 y2 x3) (Just4 y2)))))
          (match y
            (case Nil2 x2)
            (case (Cons2 x4 x5)
              (match x5
                (case Nil2
                  (match z
                    (case Nil2 (Just4 x4))
                    (case (Cons2 x6 x7) x2)))
                (case (Cons2 x8 x9) x2))))))))
(define-fun
  fstL
    ((x Q)) Maybe3
    (match x
      (case (Q2 y z)
        (match y
          (case Nil
            (match z
              (case Nil Nothing3)
              (case (Cons y2 x2)
                (match x2
                  (case Nil (Just3 y2))
                  (case (Cons x3 x4) Nothing3)))))
          (case (Cons x5 x6) (Just3 x5))))))
(define-fun
  fromMaybe2
    ((x Q3) (y Maybe2)) Q3
    (match y
      (case Nothing2 x)
      (case (Just2 z) z)))
(define-fun
  fromMaybe
    ((x Q) (y Maybe)) Q
    (match y
      (case Nothing x)
      (case (Just z) z)))
(define-fun empty2 () Q3 (Q22 Nil2 Nil2))
(define-fun empty () Q (Q2 Nil Nil))
(define-fun-rec
  drop2
    ((x Nat) (y list2)) list2
    (match x
      (case Z y)
      (case (S z)
        (match y
          (case Nil2 Nil2)
          (case (Cons2 x2 x3) (drop2 z x3))))))
(define-fun
  halve2
    ((x list2)) Pair3
    (let ((k (half (length2 x)))) (Pair22 (take2 k x) (drop2 k x))))
(define-fun-rec
  drop
    ((x Nat) (y list)) list
    (match x
      (case Z y)
      (case (S z)
        (match y
          (case Nil Nil)
          (case (Cons x2 x3) (drop z x3))))))
(define-fun
  halve
    ((x list)) Pair
    (let ((k (half (length x)))) (Pair2 (take k x) (drop k x))))
(define-fun-rec
  append2
    ((x list2) (y list2)) list2
    (match x
      (case Nil2 y)
      (case (Cons2 z xs) (Cons2 z (append2 xs y)))))
(define-fun-rec
  list23
    ((x E2)) list2
    (match x
      (case Empty2 Nil2)
      (case (EnqL2 y e) (Cons2 y (list23 e)))
      (case (EnqR2 e2 z) (append2 (list23 e2) (Cons2 z Nil2)))
      (case (DeqL2 e3) (tail2 (list23 e3)))
      (case (DeqR2 e4) (init2 (list23 e4)))
      (case (App2 a3 b2) (append2 (list23 a3) (list23 b2)))))
(define-fun-rec
  reverse2
    ((x list2)) list2
    (match x
      (case Nil2 Nil2)
      (case (Cons2 y xs) (append2 (reverse2 xs) (Cons2 y Nil2)))))
(define-fun
  enqL2
    ((x sk2) (y Q3)) Q3
    (match y
      (case (Q22 xs ys)
        (match ys
          (case Nil2
            (match (halve2 (Cons2 x xs))
              (case (Pair22 bs cs) (Q22 bs (reverse2 cs)))))
          (case (Cons2 z x2) (Q22 (Cons2 x xs) ys))))))
(define-fun
  mkQ2
    ((x list2) (y list2)) Q3
    (match x
      (case Nil2
        (match (halve2 y) (case (Pair22 bs cs) (Q22 (reverse2 cs) bs))))
      (case (Cons2 z x2)
        (match y
          (case Nil2
            (match (halve2 x)
              (case (Pair22 as2 bs2) (Q22 as2 (reverse2 bs2)))))
          (case (Cons2 x3 x4) (Q22 x y))))))
(define-fun
  deqL2
    ((x Q3)) Maybe2
    (match x
      (case (Q22 y z)
        (match y
          (case Nil2
            (match z
              (case Nil2 Nothing2)
              (case (Cons2 x2 x3)
                (match x3
                  (case Nil2 (Just2 empty2))
                  (case (Cons2 x4 x5) Nothing2)))))
          (case (Cons2 x6 xs) (Just2 (mkQ2 xs z)))))))
(define-fun
  deqR2
    ((x Q3)) Maybe2
    (match x
      (case (Q22 y z)
        (let
          ((x2
              (match z
                (case Nil2 Nothing2)
                (case (Cons2 y2 ys) (Just2 (mkQ2 y ys))))))
          (match y
            (case Nil2 x2)
            (case (Cons2 x3 x4)
              (match x4
                (case Nil2
                  (match z
                    (case Nil2 (Just2 empty2))
                    (case (Cons2 x5 x6) x2)))
                (case (Cons2 x7 x8) x2))))))))
(define-fun
  enqR2
    ((x Q3) (y sk2)) Q3
    (match x (case (Q22 xs ys) (mkQ2 xs (Cons2 y ys)))))
(define-fun-rec
  append
    ((x list) (y list)) list
    (match x
      (case Nil y)
      (case (Cons z xs) (Cons z (append xs y)))))
(define-fun-rec
  list22
    ((x E)) list
    (match x
      (case Empty Nil)
      (case (EnqL y e) (Cons y (list22 e)))
      (case (EnqR e2 z) (append (list22 e2) (Cons z Nil)))
      (case (DeqL e3) (tail (list22 e3)))
      (case (DeqR e4) (init (list22 e4)))
      (case (App a3 b2) (append (list22 a3) (list22 b2)))))
(define-fun-rec
  reverse
    ((x list)) list
    (match x
      (case Nil Nil)
      (case (Cons y xs) (append (reverse xs) (Cons y Nil)))))
(define-fun
  enqL
    ((x sk) (y Q)) Q
    (match y
      (case (Q2 xs ys)
        (match ys
          (case Nil
            (match (halve (Cons x xs))
              (case (Pair2 bs cs) (Q2 bs (reverse cs)))))
          (case (Cons z x2) (Q2 (Cons x xs) ys))))))
(define-fun
  mkQ
    ((x list) (y list)) Q
    (match x
      (case Nil
        (match (halve y) (case (Pair2 bs cs) (Q2 (reverse cs) bs))))
      (case (Cons z x2)
        (match y
          (case Nil
            (match (halve x) (case (Pair2 as2 bs2) (Q2 as2 (reverse bs2)))))
          (case (Cons x3 x4) (Q2 x y))))))
(define-fun
  deqL
    ((x Q)) Maybe
    (match x
      (case (Q2 y z)
        (match y
          (case Nil
            (match z
              (case Nil Nothing)
              (case (Cons x2 x3)
                (match x3
                  (case Nil (Just empty))
                  (case (Cons x4 x5) Nothing)))))
          (case (Cons x6 xs) (Just (mkQ xs z)))))))
(define-fun
  deqR
    ((x Q)) Maybe
    (match x
      (case (Q2 y z)
        (let
          ((x2
              (match z
                (case Nil Nothing)
                (case (Cons y2 ys) (Just (mkQ y ys))))))
          (match y
            (case Nil x2)
            (case (Cons x3 x4)
              (match x4
                (case Nil
                  (match z
                    (case Nil (Just empty))
                    (case (Cons x5 x6) x2)))
                (case (Cons x7 x8) x2))))))))
(define-fun
  enqR
    ((x Q) (y sk)) Q (match x (case (Q2 xs ys) (mkQ xs (Cons y ys)))))
(define-fun
  +++2
    ((x Q3) (y Q3)) Q3
    (match x
      (case (Q22 xs ys)
        (match y
          (case (Q22 vs ws)
            (mkQ2 (append2 xs (reverse2 ys)) (append2 (reverse2 vs) ws)))))))
(define-fun-rec
  queue2
    ((x E2)) Q3
    (match x
      (case Empty2 empty2)
      (case (EnqL2 y e) (enqL2 y (queue2 e)))
      (case (EnqR2 e2 z) (enqR2 (queue2 e2) z))
      (case (DeqL2 e3) (let ((q (queue2 e3))) (fromMaybe2 q (deqL2 q))))
      (case (DeqR2 e4) (let ((r (queue2 e4))) (fromMaybe2 r (deqR2 r))))
      (case (App2 a6 b2) (+++2 (queue2 a6) (queue2 b2)))))
(define-fun
  +++
    ((x Q) (y Q)) Q
    (match x
      (case (Q2 xs ys)
        (match y
          (case (Q2 vs ws)
            (mkQ (append xs (reverse ys)) (append (reverse vs) ws)))))))
(define-fun-rec
  queue
    ((x E)) Q
    (match x
      (case Empty empty)
      (case (EnqL y e) (enqL y (queue e)))
      (case (EnqR e2 z) (enqR (queue e2) z))
      (case (DeqL e3) (let ((q (queue e3))) (fromMaybe q (deqL q))))
      (case (DeqR e4) (let ((r (queue e4))) (fromMaybe r (deqR r))))
      (case (App a6 b2) (+++ (queue a6) (queue b2)))))
(assert-not
  (forall ((e E)) (= (fstL (queue e)) (head (list22 e)))))
(check-sat)
