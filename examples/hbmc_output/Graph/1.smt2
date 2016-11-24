(declare-datatypes (a)
  ((list (Nil) (Cons (Cons_0 a) (Cons_1 (list a))))))
(declare-datatypes (a b) ((Pair (Pair2 (first a) (second b)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes (a) ((Maybe (Nothing) (Just (Just_0 a)))))
(declare-datatypes () ((B (I) (O))))
(define-fun-rec
  plus
    ((x Nat) (y Nat)) Nat
    (match x
      (case Z y)
      (case (S n) (S (plus n y)))))
(define-fun-rec
  petersen3
    ((x Nat) (y (list Nat))) (list (Pair Nat Nat))
    (match y
      (case Nil (as Nil (list (Pair Nat Nat))))
      (case (Cons z x2) (Cons (Pair2 z (plus x z)) (petersen3 x x2)))))
(define-fun-rec
  petersen2
    ((x Nat) (y (list (Pair Nat Nat)))) (list (list (Pair Nat Nat)))
    (match y
      (case Nil (as Nil (list (list (Pair Nat Nat)))))
      (case (Cons z x2)
        (match z
          (case (Pair2 u v)
            (Cons
              (Cons z
                (Cons (Pair2 (plus x u) (plus x v))
                  (as Nil (list (Pair Nat Nat)))))
              (petersen2 x x2)))))))
(define-fun-rec
  petersen
    ((x (list Nat))) (list (Pair Nat Nat))
    (match x
      (case Nil (as Nil (list (Pair Nat Nat))))
      (case (Cons y z) (Cons (Pair2 y (S y)) (petersen z)))))
(define-fun-rec
  or2
    ((x (list Bool))) Bool
    (match x
      (case Nil false)
      (case (Cons y xs) (or y (or2 xs)))))
(define-fun-rec
  max2
    ((x Nat) (y Nat)) Nat
    (match x
      (case Z y)
      (case (S z)
        (match y
          (case Z x)
          (case (S x2) (S (max2 z x2)))))))
(define-fun-rec
  maximum
    ((x Nat) (y (list (Pair Nat Nat)))) Nat
    (match y
      (case Nil x)
      (case (Cons z yzs)
        (match z
          (case (Pair2 y2 z2) (maximum (max2 x (max2 y2 z2)) yzs))))))
(define-fun-rec
  lt
    ((x Nat) (y Nat)) Bool
    (match y
      (case Z false)
      (case (S z)
        (match x
          (case Z true)
          (case (S n) (lt n z))))))
(define-fun-rec
  prop_p5
    ((x (list Nat))) (list Bool)
    (match x
      (case Nil (as Nil (list Bool)))
      (case (Cons y z) (Cons (lt y (S (S (S Z)))) (prop_p5 z)))))
(define-fun-rec
  (par (a)
    (length
       ((x (list a))) Nat
       (match x
         (case Nil Z)
         (case (Cons y xs) (S (length xs)))))))
(define-fun-rec
  (par (t)
    (last
       ((x t) (y (list t))) t
       (match y
         (case Nil x)
         (case (Cons z ys) (last z ys))))))
(define-fun-rec
  (par (a)
    (index
       ((x (list a)) (y Nat)) (Maybe a)
       (match x
         (case Nil (as Nothing (Maybe a)))
         (case (Cons z xs)
           (match y
             (case Z (Just z))
             (case (S n) (index xs n))))))))
(define-fun-rec
  half
    ((x Nat)) Nat
    (match x
      (case Z Z)
      (case (S y)
        (match y
          (case Z Z)
          (case (S n) (S (half n)))))))
(define-fun-rec
  ge
    ((x Nat) (y Nat)) Bool
    (match y
      (case Z true)
      (case (S z)
        (match x
          (case Z false)
          (case (S x2) (ge x2 z))))))
(define-fun-rec
  even
    ((x Nat)) Bool
    (match x
      (case Z true)
      (case (S y)
        (match y
          (case Z false)
          (case (S z) (even z))))))
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
  path2
    ((x Nat) (y Nat) (z (list (Pair Nat Nat)))) (list Bool)
    (match z
      (case Nil (as Nil (list Bool)))
      (case (Cons x2 x3)
        (match x2
          (case (Pair2 u v)
            (Cons
              (or (and (equal u x) (equal v y)) (and (equal u y) (equal v x)))
              (path2 x y x3)))))))
(define-fun-rec
  path
    ((x (list Nat)) (y (list (Pair Nat Nat)))) Bool
    (match x
      (case Nil true)
      (case (Cons z x2)
        (match x2
          (case Nil true)
          (case (Cons y2 xs) (and (or2 (path2 z y2 y)) (path x2 y)))))))
(define-fun unequal ((x Nat) (y Nat)) Bool (not (equal x y)))
(define-fun-rec
  enumFromTo
    ((x Nat) (y Nat)) (list Nat)
    (ite (ge x y) (as Nil (list Nat)) (Cons x (enumFromTo (S x) y))))
(define-fun-rec
  elem
    ((x Nat) (y (list Nat))) Bool
    (match y
      (case Nil false)
      (case (Cons z ys) (or (equal x z) (elem x ys)))))
(define-fun-rec
  unique
    ((x (list Nat))) Bool
    (match x
      (case Nil true)
      (case (Cons y xs) (and (not (elem y xs)) (unique xs)))))
(define-fun
  tour
    ((x (list Nat)) (y (list (Pair Nat Nat)))) Bool
    (match x
      (case Nil
        (match y
          (case Nil true)
          (case (Cons z x2) false)))
      (case (Cons x3 x4)
        (match y
          (case Nil false)
          (case (Cons x5 vs)
            (match x5
              (case (Pair2 u v)
                (and (equal x3 (last x3 x4))
                  (and (path x y)
                    (and (unique x4)
                      (equal (length x) (S (S (maximum (max2 u v) vs))))))))))))))
(define-fun-rec
  dodeca4
    ((x Nat) (y (list Nat))) (list (Pair Nat Nat))
    (match y
      (case Nil (as Nil (list (Pair Nat Nat))))
      (case (Cons z x2)
        (Cons
          (Pair2 (plus x (plus x (plus x z)))
            (plus x (plus x (plus x (S z)))))
          (dodeca4 x x2)))))
(define-fun-rec
  dodeca3
    ((x Nat) (y (list Nat))) (list (Pair Nat Nat))
    (match y
      (case Nil (as Nil (list (Pair Nat Nat))))
      (case (Cons z x2)
        (Cons (Pair2 (plus x (plus x z)) (plus x (plus x (plus x z))))
          (dodeca3 x x2)))))
(define-fun-rec
  dodeca2
    ((x Nat) (y (list Nat))) (list (Pair Nat Nat))
    (match y
      (case Nil (as Nil (list (Pair Nat Nat))))
      (case (Cons z x2)
        (Cons (Pair2 (plus x (S z)) (plus x (plus x z))) (dodeca2 x x2)))))
(define-fun-rec
  dodeca
    ((x Nat) (y (list Nat))) (list (Pair Nat Nat))
    (match y
      (case Nil (as Nil (list (Pair Nat Nat))))
      (case (Cons z x2)
        (Cons (Pair2 (plus x z) (plus x (plus x z))) (dodeca x x2)))))
(define-fun-rec
  colouring2
    ((a (list Nat)) (x (list (Pair Nat Nat)))) (list Bool)
    (match x
      (case Nil (as Nil (list Bool)))
      (case (Cons y z)
        (match y
          (case (Pair2 u v)
            (match (index a u)
              (case Nothing (Cons false (colouring2 a z)))
              (case (Just c1)
                (match (index a v)
                  (case Nothing (Cons false (colouring2 a z)))
                  (case (Just c2) (Cons (unequal c1 c2) (colouring2 a z)))))))))))
(define-fun-rec
  bin
    ((x Nat)) (list B)
    (match x
      (case Z (as Nil (list B)))
      (case (S y)
        (ite (even x) (Cons O (bin (half x))) (Cons I (bin (half x)))))))
(define-fun-rec
  bgraph
    ((x (list (Pair Nat Nat)))) (list (Pair (list B) (list B)))
    (match x
      (case Nil (as Nil (list (Pair (list B) (list B)))))
      (case (Cons y z)
        (match y
          (case (Pair2 u v) (Cons (Pair2 (bin u) (bin v)) (bgraph z)))))))
(define-fun-rec
  beq
    ((x (list B)) (y (list B))) Bool
    (match x
      (case Nil
        (match y
          (case Nil true)
          (case (Cons z x2) false)))
      (case (Cons x3 xs)
        (match x3
          (case I
            (match y
              (case Nil false)
              (case (Cons x4 ys)
                (match x4
                  (case I (beq xs ys))
                  (case O false)))))
          (case O
            (match y
              (case Nil false)
              (case (Cons x5 zs)
                (match x5
                  (case I false)
                  (case O (beq xs zs))))))))))
(define-fun-rec
  bpath2
    ((x (list B)) (y (list B)) (z (list (Pair (list B) (list B)))))
    (list Bool)
    (match z
      (case Nil (as Nil (list Bool)))
      (case (Cons x2 x3)
        (match x2
          (case (Pair2 u v)
            (Cons (or (and (beq u x) (beq v y)) (and (beq u y) (beq v x)))
              (bpath2 x y x3)))))))
(define-fun-rec
  bpath
    ((x (list (list B))) (y (list (Pair (list B) (list B))))) Bool
    (match x
      (case Nil true)
      (case (Cons z x2)
        (match x2
          (case Nil true)
          (case (Cons y2 xs) (and (or2 (bpath2 z y2 y)) (bpath x2 y)))))))
(define-fun-rec
  belem2
    ((x (list B)) (y (list (list B)))) (list Bool)
    (match y
      (case Nil (as Nil (list Bool)))
      (case (Cons z x2) (Cons (beq x z) (belem2 x x2)))))
(define-fun
  belem ((x (list B)) (y (list (list B)))) Bool (or2 (belem2 x y)))
(define-fun-rec
  bunique
    ((x (list (list B)))) Bool
    (match x
      (case Nil true)
      (case (Cons y xs) (and (not (belem y xs)) (bunique xs)))))
(define-fun
  btour
    ((x (list (list B))) (y (list (Pair Nat Nat)))) Bool
    (match x
      (case Nil
        (match y
          (case Nil true)
          (case (Cons z x2) false)))
      (case (Cons x3 x4)
        (match y
          (case Nil false)
          (case (Cons x5 vs)
            (match x5
              (case (Pair2 u v)
                (and (beq x3 (last x3 x4))
                  (and (bpath x (bgraph y))
                    (and (bunique x4)
                      (equal (length x) (S (S (maximum (max2 u v) vs))))))))))))))
(define-fun-rec
  (par (a)
    (append
       ((x (list a)) (y (list a))) (list a)
       (match x
         (case Nil y)
         (case (Cons z xs) (Cons z (append xs y)))))))
(define-fun-rec
  (par (a)
    (concat2
       ((x (list (list a)))) (list a)
       (match x
         (case Nil (as Nil (list a)))
         (case (Cons xs xss) (append xs (concat2 xss)))))))
(define-fun-rec
  and2
    ((x (list Bool))) Bool
    (match x
      (case Nil true)
      (case (Cons y xs) (and y (and2 xs)))))
(define-fun
  colouring
    ((x (list (Pair Nat Nat))) (y (list Nat))) Bool
    (and2 (colouring2 y x)))
(assert-not
  (forall ((a (list Nat)))
    (or
      (not
        (colouring
          (let ((pn (S (S (S (S (S (S Z))))))))
            (append
              (concat2
                (petersen2 (S pn)
                  (Cons (Pair2 pn Z) (petersen (enumFromTo Z pn)))))
              (petersen3 (S pn) (enumFromTo Z (S pn)))))
          a))
      (not (and2 (prop_p5 a))))))
(check-sat)
