(declare-datatypes (a)
  ((list (Nil) (Cons (Cons_0 a) (Cons_1 (list a))))))
(declare-datatypes (a) ((Q (Q2 (Q_0 (list a)) (Q_1 (list a))))))
(declare-datatypes (a b) ((Pair (Pair2 (first a) (second b)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes (a) ((Maybe (Nothing) (Just (Just_0 a)))))
(declare-datatypes (a)
  ((E (Empty)
     (EnqL (EnqL_0 a) (EnqL_1 (E a))) (EnqR (EnqR_0 (E a)) (EnqR_1 a))
     (DeqL (DeqL_0 (E a))) (DeqR (DeqR_0 (E a)))
     (App (App_0 (E a)) (App_1 (E a))))))
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
(define-fun
  (par (t)
    (tail
       ((x (list t))) (list t)
       (match x
         (case Nil (as Nil (list t)))
         (case (Cons y xs) xs)))))
(define-fun-rec
  (par (a)
    (length
       ((x (list a))) Nat
       (match x
         (case Nil Z)
         (case (Cons y xs) (S (length xs)))))))
(define-fun-rec
  (par (a)
    (last
       ((x (list a))) (Maybe a)
       (match x
         (case Nil (as Nothing (Maybe a)))
         (case (Cons y z)
           (match z
             (case Nil (Just y))
             (case (Cons x2 x3) (last z))))))))
(define-fun-rec
  (par (t)
    (init
       ((x (list t))) (list t)
       (match x
         (case Nil (as Nil (list t)))
         (case (Cons y z)
           (match z
             (case Nil (as Nil (list t)))
             (case (Cons x2 x3) (Cons y (init z)))))))))
(define-fun
  (par (a)
    (head
       ((x (list a))) (Maybe a)
       (match x
         (case Nil (as Nothing (Maybe a)))
         (case (Cons y z) (Just y))))))
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
  (par (a)
    (fstR
       ((x (Q a))) (Maybe a)
       (match x
         (case (Q2 y z)
           (let
             ((x2
                 (match z
                   (case Nil (as Nothing (Maybe a)))
                   (case (Cons y2 x3) (Just y2)))))
             (match y
               (case Nil x2)
               (case (Cons x4 x5)
                 (match x5
                   (case Nil
                     (match z
                       (case Nil (Just x4))
                       (case (Cons x6 x7) x2)))
                   (case (Cons x8 x9) x2))))))))))
(define-fun
  (par (a)
    (fstL
       ((x (Q a))) (Maybe a)
       (match x
         (case (Q2 y z)
           (match y
             (case Nil
               (match z
                 (case Nil (as Nothing (Maybe a)))
                 (case (Cons y2 x2)
                   (match x2
                     (case Nil (Just y2))
                     (case (Cons x3 x4) (as Nothing (Maybe a)))))))
             (case (Cons x5 x6) (Just x5))))))))
(define-fun
  (par (t)
    (fromMaybe
       ((x t) (y (Maybe t))) t
       (match y
         (case Nothing x)
         (case (Just z) z)))))
(define-fun
  (par (a)
    (empty () (Q a) (Q2 (as Nil (list a)) (as Nil (list a))))))
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
(define-fun
  (par (a)
    (halve
       ((x (list a))) (Pair (list a) (list a))
       (let ((k (half (length x)))) (Pair2 (take k x) (drop k x))))))
(define-fun-rec
  (par (a)
    (append
       ((x (list a)) (y (list a))) (list a)
       (match x
         (case Nil y)
         (case (Cons z xs) (Cons z (append xs y)))))))
(define-fun-rec
  (par (a)
    (list2
       ((x (E a))) (list a)
       (match x
         (case Empty (as Nil (list a)))
         (case (EnqL y e) (Cons y (list2 e)))
         (case (EnqR e2 z) (append (list2 e2) (Cons z (as Nil (list a)))))
         (case (DeqL e3) (tail (list2 e3)))
         (case (DeqR e4) (init (list2 e4)))
         (case (App a32 b2) (append (list2 a32) (list2 b2)))))))
(define-fun-rec
  (par (a)
    (reverse
       ((x (list a))) (list a)
       (match x
         (case Nil (as Nil (list a)))
         (case (Cons y xs)
           (append (reverse xs) (Cons y (as Nil (list a)))))))))
(define-fun
  (par (a)
    (enqL
       ((x a) (y (Q a))) (Q a)
       (match y
         (case (Q2 xs ys)
           (match ys
             (case Nil
               (match (halve (Cons x xs))
                 (case (Pair2 bs cs) (Q2 bs (reverse cs)))))
             (case (Cons z x2) (Q2 (Cons x xs) ys))))))))
(define-fun
  (par (a)
    (mkQ
       ((x (list a)) (y (list a))) (Q a)
       (match x
         (case Nil
           (match (halve y) (case (Pair2 bs cs) (Q2 (reverse cs) bs))))
         (case (Cons z x2)
           (match y
             (case Nil
               (match (halve x) (case (Pair2 as2 bs2) (Q2 as2 (reverse bs2)))))
             (case (Cons x3 x4) (Q2 x y))))))))
(define-fun
  (par (a)
    (deqL
       ((x (Q a))) (Maybe (Q a))
       (match x
         (case (Q2 y z)
           (match y
             (case Nil
               (match z
                 (case Nil (as Nothing (Maybe (Q a))))
                 (case (Cons x2 x3)
                   (match x3
                     (case Nil (Just (as empty (Q a))))
                     (case (Cons x4 x5) (as Nothing (Maybe (Q a))))))))
             (case (Cons x6 xs) (Just (mkQ xs z)))))))))
(define-fun
  (par (a)
    (deqR
       ((x (Q a))) (Maybe (Q a))
       (match x
         (case (Q2 y z)
           (let
             ((x2
                 (match z
                   (case Nil (as Nothing (Maybe (Q a))))
                   (case (Cons y2 ys) (Just (mkQ y ys))))))
             (match y
               (case Nil x2)
               (case (Cons x3 x4)
                 (match x4
                   (case Nil
                     (match z
                       (case Nil (Just (as empty (Q a))))
                       (case (Cons x5 x6) x2)))
                   (case (Cons x7 x8) x2))))))))))
(define-fun
  (par (a)
    (enqR
       ((x (Q a)) (y a)) (Q a)
       (match x (case (Q2 xs ys) (mkQ xs (Cons y ys)))))))
(define-fun
  (par (a)
    (+++
       ((x (Q a)) (y (Q a))) (Q a)
       (match x
         (case (Q2 xs ys)
           (match y
             (case (Q2 vs ws)
               (Q2 (append xs (reverse ys)) (append ws (reverse vs))))))))))
(define-fun-rec
  (par (a)
    (queue
       ((x (E a))) (Q a)
       (match x
         (case Empty (as empty (Q a)))
         (case (EnqL y e) (enqL y (queue e)))
         (case (EnqR e2 z) (enqR (queue e2) z))
         (case (DeqL e3) (let ((q (queue e3))) (fromMaybe q (deqL q))))
         (case (DeqR e4) (let ((r (queue e4))) (fromMaybe r (deqR r))))
         (case (App a62 b2) (+++ (queue a62) (queue b2)))))))
(assert-not
  (par (a)
    (forall ((e (E a))) (= (fstL (queue e)) (head (list2 e))))))
(check-sat)
