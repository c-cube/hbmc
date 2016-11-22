(declare-datatypes ()
  ((list7 (Nil7) (Cons7 (Cons_07 Bool) (Cons_17 list7)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes ()
  ((Pair2 (Pair23 (first2 Nat) (second2 Nat)))))
(declare-datatypes ()
  ((list2 (Nil4) (Cons4 (Cons_04 Pair2) (Cons_14 list2)))))
(declare-datatypes ()
  ((list (Nil) (Cons (Cons_0 list2) (Cons_1 list)))))
(declare-datatypes ()
  ((list6 (Nil5) (Cons5 (Cons_05 Nat) (Cons_15 list6)))))
(declare-datatypes () ((Maybe (Nothing) (Just (Just_0 Nat)))))
(declare-datatypes () ((B (I) (O))))
(declare-datatypes ()
  ((list4 (Nil6) (Cons6 (Cons_06 B) (Cons_16 list4)))))
(declare-datatypes ()
  ((Pair (Pair22 (first list4) (second list4)))))
(declare-datatypes ()
  ((list5 (Nil3) (Cons3 (Cons_03 Pair) (Cons_13 list5)))))
(declare-datatypes ()
  ((list3 (Nil2) (Cons2 (Cons_02 list4) (Cons_12 list3)))))
(define-fun-rec
  plus
    ((x Nat) (y Nat)) Nat
    (match x
      (case Z y)
      (case (S n) (S (plus n y)))))
(define-fun-rec
  petersen
    ((x Nat) (y list2)) list
    (match y
      (case Nil4 Nil)
      (case (Cons4 z x2)
        (match z
          (case (Pair23 u v)
            (Cons (Cons4 z (Cons4 (Pair23 (plus x u) (plus x v)) Nil4))
              (petersen x x2)))))))
(define-fun-rec
  or2
    ((x list7)) Bool
    (match x
      (case Nil7 false)
      (case (Cons7 y xs) (or y (or2 xs)))))
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
    ((x Nat) (y list2)) Nat
    (match y
      (case Nil4 x)
      (case (Cons4 z yzs)
        (match z
          (case (Pair23 y2 z2) (maximum (max2 x (max2 y2 z2)) yzs))))))
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
  prop_d5
    ((x list6)) list7
    (match x
      (case Nil5 Nil7)
      (case (Cons5 y z) (Cons7 (lt y (S (S (S Z)))) (prop_d5 z)))))
(define-fun-rec
  length2
    ((x list6)) Nat
    (match x
      (case Nil5 Z)
      (case (Cons5 y xs) (S (length2 xs)))))
(define-fun-rec
  length
    ((x list3)) Nat
    (match x
      (case Nil2 Z)
      (case (Cons2 y xs) (S (length xs)))))
(define-fun-rec
  last2
    ((x Nat) (y list6)) Nat
    (match y
      (case Nil5 x)
      (case (Cons5 z ys) (last2 z ys))))
(define-fun-rec
  last
    ((x list4) (y list3)) list4
    (match y
      (case Nil2 x)
      (case (Cons2 z ys) (last z ys))))
(define-fun-rec
  index
    ((x list6) (y Nat)) Maybe
    (match x
      (case Nil5 Nothing)
      (case (Cons5 z xs)
        (match y
          (case Z (Just z))
          (case (S n) (index xs n))))))
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
    ((x Nat) (y Nat) (z list2)) list7
    (match z
      (case Nil4 Nil7)
      (case (Cons4 x2 x3)
        (match x2
          (case (Pair23 u v)
            (Cons7
              (or (and (equal u x) (equal v y)) (and (equal u y) (equal v x)))
              (path2 x y x3)))))))
(define-fun-rec
  path
    ((x list6) (y list2)) Bool
    (match x
      (case Nil5 true)
      (case (Cons5 z x2)
        (match x2
          (case Nil5 true)
          (case (Cons5 y2 xs) (and (or2 (path2 z y2 y)) (path x2 y)))))))
(define-fun unequal ((x Nat) (y Nat)) Bool (not (equal x y)))
(define-fun-rec
  enumFromTo
    ((x Nat) (y Nat)) list6
    (ite (ge x y) Nil5 (Cons5 x (enumFromTo (S x) y))))
(define-fun-rec
  elem
    ((x Nat) (y list6)) Bool
    (match y
      (case Nil5 false)
      (case (Cons5 z ys) (or (equal x z) (elem x ys)))))
(define-fun-rec
  unique
    ((x list6)) Bool
    (match x
      (case Nil5 true)
      (case (Cons5 y xs) (and (not (elem y xs)) (unique xs)))))
(define-fun
  tour
    ((x list6) (y list2)) Bool
    (match x
      (case Nil5
        (match y
          (case Nil4 true)
          (case (Cons4 z x2) false)))
      (case (Cons5 x3 x4)
        (match y
          (case Nil4 false)
          (case (Cons4 x5 vs)
            (match x5
              (case (Pair23 u v)
                (and (equal x3 (last2 x3 x4))
                  (and (path x y)
                    (and (unique x4)
                      (equal (length2 x) (S (S (maximum (max2 u v) vs))))))))))))))
(define-fun-rec
  dodeca6
    ((x Nat) (y list6)) list2
    (match y
      (case Nil5 Nil4)
      (case (Cons5 z x2)
        (Cons4
          (Pair23 (plus x (plus x (plus x z)))
            (plus x (plus x (plus x (S z)))))
          (dodeca6 x x2)))))
(define-fun-rec
  dodeca5
    ((x Nat) (y list6)) list2
    (match y
      (case Nil5 Nil4)
      (case (Cons5 z x2)
        (Cons4 (Pair23 (plus x (plus x z)) (plus x (plus x (plus x z))))
          (dodeca5 x x2)))))
(define-fun-rec
  dodeca4
    ((x Nat) (y list6)) list2
    (match y
      (case Nil5 Nil4)
      (case (Cons5 z x2)
        (Cons4 (Pair23 (plus x (S z)) (plus x (plus x z)))
          (dodeca4 x x2)))))
(define-fun-rec
  dodeca3
    ((x Nat) (y list6)) list2
    (match y
      (case Nil5 Nil4)
      (case (Cons5 z x2)
        (Cons4 (Pair23 (plus x z) (plus x (plus x z))) (dodeca3 x x2)))))
(define-fun-rec
  dodeca2
    ((x Nat) (y list6)) list2
    (match y
      (case Nil5 Nil4)
      (case (Cons5 z x2) (Cons4 (Pair23 z (plus x z)) (dodeca2 x x2)))))
(define-fun-rec
  dodeca
    ((x list6)) list2
    (match x
      (case Nil5 Nil4)
      (case (Cons5 y z) (Cons4 (Pair23 y (S y)) (dodeca z)))))
(define-fun-rec
  colouring2
    ((a list6) (x list2)) list7
    (match x
      (case Nil4 Nil7)
      (case (Cons4 y z)
        (match y
          (case (Pair23 u v)
            (match (index a u)
              (case Nothing (Cons7 false (colouring2 a z)))
              (case (Just c1)
                (match (index a v)
                  (case Nothing (Cons7 false (colouring2 a z)))
                  (case (Just c2) (Cons7 (unequal c1 c2) (colouring2 a z)))))))))))
(define-fun-rec
  bin
    ((x Nat)) list4
    (match x
      (case Z Nil6)
      (case (S y)
        (ite (even x) (Cons6 O (bin (half x))) (Cons6 I (bin (half x)))))))
(define-fun-rec
  bgraph
    ((x list2)) list5
    (match x
      (case Nil4 Nil3)
      (case (Cons4 y z)
        (match y
          (case (Pair23 u v) (Cons3 (Pair22 (bin u) (bin v)) (bgraph z)))))))
(define-fun-rec
  beq
    ((x list4) (y list4)) Bool
    (match x
      (case Nil6
        (match y
          (case Nil6 true)
          (case (Cons6 z x2) false)))
      (case (Cons6 x3 xs)
        (match x3
          (case I
            (match y
              (case Nil6 false)
              (case (Cons6 x4 ys)
                (match x4
                  (case I (beq xs ys))
                  (case O false)))))
          (case O
            (match y
              (case Nil6 false)
              (case (Cons6 x5 zs)
                (match x5
                  (case I false)
                  (case O (beq xs zs))))))))))
(define-fun-rec
  bpath2
    ((x list4) (y list4) (z list5)) list7
    (match z
      (case Nil3 Nil7)
      (case (Cons3 x2 x3)
        (match x2
          (case (Pair22 u v)
            (Cons7 (or (and (beq u x) (beq v y)) (and (beq u y) (beq v x)))
              (bpath2 x y x3)))))))
(define-fun-rec
  bpath
    ((x list3) (y list5)) Bool
    (match x
      (case Nil2 true)
      (case (Cons2 z x2)
        (match x2
          (case Nil2 true)
          (case (Cons2 y2 xs) (and (or2 (bpath2 z y2 y)) (bpath x2 y)))))))
(define-fun-rec
  belem2
    ((x list4) (y list3)) list7
    (match y
      (case Nil2 Nil7)
      (case (Cons2 z x2) (Cons7 (beq x z) (belem2 x x2)))))
(define-fun belem ((x list4) (y list3)) Bool (or2 (belem2 x y)))
(define-fun-rec
  bunique
    ((x list3)) Bool
    (match x
      (case Nil2 true)
      (case (Cons2 y xs) (and (not (belem y xs)) (bunique xs)))))
(define-fun
  btour
    ((x list3) (y list2)) Bool
    (match x
      (case Nil2
        (match y
          (case Nil4 true)
          (case (Cons4 z x2) false)))
      (case (Cons2 x3 x4)
        (match y
          (case Nil4 false)
          (case (Cons4 x5 vs)
            (match x5
              (case (Pair23 u v)
                (and (beq x3 (last x3 x4))
                  (and (bpath x (bgraph y))
                    (and (bunique x4)
                      (equal (length x) (S (S (maximum (max2 u v) vs))))))))))))))
(define-fun-rec
  append
    ((x list2) (y list2)) list2
    (match x
      (case Nil4 y)
      (case (Cons4 z xs) (Cons4 z (append xs y)))))
(define-fun-rec
  concat2
    ((x list)) list2
    (match x
      (case Nil Nil4)
      (case (Cons xs xss) (append xs (concat2 xss)))))
(define-fun-rec
  and2
    ((x list7)) Bool
    (match x
      (case Nil7 true)
      (case (Cons7 y xs) (and y (and2 xs)))))
(define-fun
  colouring ((x list2) (y list6)) Bool (and2 (colouring2 y x)))
(assert-not
  (forall ((a list6))
    (or
      (not
        (colouring
          (let ((pn (S (S (S (S Z))))))
            (append
              (concat2
                (petersen (S pn) (Cons4 (Pair23 pn Z) (dodeca (enumFromTo Z pn)))))
              (dodeca2 (S pn) (enumFromTo Z (S pn)))))
          a))
      (not (and2 (prop_d5 a))))))
(check-sat)
