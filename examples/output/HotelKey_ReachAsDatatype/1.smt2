(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((Pair (Pair2 (first Nat) (second Nat)))))
(declare-datatypes ()
  ((Pair6 (Pair25 (first5 Nat) (second5 Bool)))))
(declare-datatypes () ((Maybe (Nothing) (Just (Just_0 Nat)))))
(declare-datatypes ()
  ((Pair3 (Pair22 (first2 Nat) (second2 Maybe)))))
(declare-datatypes ()
  ((Map4 (Rest2 (Rest_02 Maybe))
     (Slot2 (Slot_02 Maybe) (Slot_12 Map4)))))
(declare-datatypes ()
  ((Map3 (Rest (Rest_0 Nat)) (Slot (Slot_0 Nat) (Slot_1 Map3)))))
(declare-datatypes ()
  ((Reach (Init (Init_0 Map3))
     (CheckIn (CheckIn_0 Nat)
       (CheckIn_1 Nat) (CheckIn_2 Nat) (CheckIn_3 Reach))
     (EnterRoom (EnterRoom_0 Nat)
       (EnterRoom_1 Nat) (EnterRoom_2 Pair) (EnterRoom_3 Reach))
     (ExitRoom (ExitRoom_0 Nat) (ExitRoom_1 Nat) (ExitRoom_2 Reach)))))
(declare-datatypes ()
  ((Map2 (Rest5 (Rest_05 Bool))
     (Slot5 (Slot_05 Bool) (Slot_15 Map2)))))
(declare-datatypes ()
  ((Pair5 (Pair24 (first4 Nat) (second4 Map2)))))
(declare-datatypes ()
  ((Map (Rest4 (Rest_04 Map2))
     (Slot4 (Slot_04 Map2) (Slot_14 Map)))))
(declare-datatypes ()
  ((Map5 (Rest3 (Rest_03 Map))
     (Slot3 (Slot_03 Map) (Slot_13 Map5)))))
(declare-datatypes ()
  ((Pair4 (Pair23 (first3 Nat) (second3 Map)))))
(declare-datatypes ()
  ((State
     (State2 (State_0 Map4)
       (State_1 Map3) (State_2 Map2) (State_3 Map5) (State_4 Map3)
       (State_5 Map) (State_6 Map2)))))
(declare-datatypes ()
  ((Maybe2 (Nothing2) (Just2 (Just_02 State)))))
(define-fun
  safe
    ((x State)) Map2 (match x (case (State2 y z x2 x3 x4 x5 x6) x6)))
(define-fun
  roomk
    ((x State)) Map3 (match x (case (State2 y z x2 x3 x4 x5 x6) x4)))
(define-fun
  owns
    ((x State)) Map4 (match x (case (State2 y z x2 x3 x4 x5 x6) y)))
(define-fun
  issued
    ((x State)) Map2 (match x (case (State2 y z x2 x3 x4 x5 x6) x2)))
(define-fun
  isin
    ((x State)) Map (match x (case (State2 y z x2 x3 x4 x5 x6) x5)))
(define-fun-rec
  ind
    ((x Nat) (y Nat)) Bool
    (match x
      (case Z true)
      (case (S i)
        (match y
          (case Z false)
          (case (S j) (ind i j))))))
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
  inj_upto
    ((x Nat) (y Nat) (z Map3)) Bool
    (match x
      (case Z true)
      (case (S x2)
        (match z
          (case (Rest y2) (not (equal y y2)))
          (case (Slot y3 m) (and (not (equal y y3)) (inj_upto x2 y m)))))))
(define-fun-rec
  inj
    ((x Nat) (y Map3)) Bool
    (match x
      (case Z true)
      (case (S z)
        (match y
          (case (Rest x2) false)
          (case (Slot x3 m) (and (inj z m) (inj_upto x x3 m)))))))
(define-fun empty2 () Map (Rest4 (Rest5 false)))
(define-fun empty () Map2 (Rest5 false))
(define-fun
  cards
    ((x State)) Map5 (match x (case (State2 y z x2 x3 x4 x5 x6) x3)))
(define-fun
  ==?
    ((x Maybe) (y Maybe)) Bool
    (match x
      (case Nothing
        (match y
          (case Nothing true)
          (case (Just z) false)))
      (case (Just x2)
        (match y
          (case Nothing false)
          (case (Just y2) (equal x2 y2))))))
(define-fun ==. ((x Bool) (y Bool)) Bool (ite x y (not y)))
(define-fun-rec
  <=>
    ((x Map2) (y Map2)) Bool
    (match x
      (case (Rest5 z)
        (match y
          (case (Rest5 y2) (==. z y2))
          (case (Slot5 y3 q) (and (==. z y3) (<=> x q)))))
      (case (Slot5 x2 r)
        (match y
          (case (Rest5 y4) (and (==. x2 y4) (<=> r y)))
          (case (Slot5 y5 q2) (and (==. x2 y5) (<=> r q2)))))))
(define-fun-rec
  !=5
    ((x Map2) (y Pair6)) Map2
    (match x
      (case (Rest5 z)
        (match y
          (case (Pair25 x2 y2)
            (match x2
              (case Z (Slot5 y2 x))
              (case (S i) (Slot5 z (!=5 x (Pair25 i y2))))))))
      (case (Slot5 x3 m)
        (match y
          (case (Pair25 x4 y3)
            (match x4
              (case Z (Slot5 y3 m))
              (case (S j) (Slot5 x3 (!=5 m (Pair25 j y3))))))))))
(define-fun add ((x Nat) (y Map2)) Map2 (!=5 y (Pair25 x true)))
(define-fun-rec
  range
    ((x Map3)) Map2
    (match x
      (case (Rest y) (add y empty))
      (case (Slot z m) (add z (range m)))))
(define-fun rem ((x Nat) (y Map2)) Map2 (!=5 y (Pair25 x false)))
(define-fun-rec
  !=4
    ((x Map) (y Pair5)) Map
    (match x
      (case (Rest4 z)
        (match y
          (case (Pair24 x2 y2)
            (match x2
              (case Z (Slot4 y2 x))
              (case (S i) (Slot4 z (!=4 x (Pair24 i y2))))))))
      (case (Slot4 x3 m)
        (match y
          (case (Pair24 x4 y3)
            (match x4
              (case Z (Slot4 y3 m))
              (case (S j) (Slot4 x3 (!=4 m (Pair24 j y3))))))))))
(define-fun-rec
  !=3
    ((x Map5) (y Pair4)) Map5
    (match x
      (case (Rest3 z)
        (match y
          (case (Pair23 x2 y2)
            (match x2
              (case Z (Slot3 y2 x))
              (case (S i) (Slot3 z (!=3 x (Pair23 i y2))))))))
      (case (Slot3 x3 m)
        (match y
          (case (Pair23 x4 y3)
            (match x4
              (case Z (Slot3 y3 m))
              (case (S j) (Slot3 x3 (!=3 m (Pair23 j y3))))))))))
(define-fun-rec
  !=2
    ((x Map4) (y Pair3)) Map4
    (match x
      (case (Rest2 z)
        (match y
          (case (Pair22 x2 y2)
            (match x2
              (case Z (Slot2 y2 x))
              (case (S i) (Slot2 z (!=2 x (Pair22 i y2))))))))
      (case (Slot2 x3 m)
        (match y
          (case (Pair22 x4 y3)
            (match x4
              (case Z (Slot2 y3 m))
              (case (S j) (Slot2 x3 (!=2 m (Pair22 j y3))))))))))
(define-fun-rec
  !=
    ((x Map3) (y Pair)) Map3
    (match x
      (case (Rest z)
        (match y
          (case (Pair2 x2 y2)
            (match x2
              (case Z (Slot y2 x))
              (case (S i) (Slot z (!= x (Pair2 i y2))))))))
      (case (Slot x3 m)
        (match y
          (case (Pair2 x4 y3)
            (match x4
              (case Z (Slot y3 m))
              (case (S j) (Slot x3 (!= m (Pair2 j y3))))))))))
(define-fun-rec
  !25
    ((x Map2) (y Nat)) Bool
    (match x
      (case (Rest5 z) z)
      (case (Slot5 x2 m)
        (match y
          (case Z x2)
          (case (S i) (!25 m i))))))
(define-fun-rec
  !24
    ((x Map) (y Nat)) Map2
    (match x
      (case (Rest4 z) z)
      (case (Slot4 x2 m)
        (match y
          (case Z x2)
          (case (S i) (!24 m i))))))
(define-fun
  add2
    ((x Pair) (y Map)) Map
    (match x
      (case (Pair2 z y2) (!=4 y (Pair24 z (add y2 (!24 y z)))))))
(define-fun-rec
  !23
    ((x Map5) (y Nat)) Map
    (match x
      (case (Rest3 z) z)
      (case (Slot3 x2 m)
        (match y
          (case Z x2)
          (case (S i) (!23 m i))))))
(define-fun-rec
  !22
    ((x Map4) (y Nat)) Maybe
    (match x
      (case (Rest2 z) z)
      (case (Slot2 x2 m)
        (match y
          (case Z x2)
          (case (S i) (!22 m i))))))
(define-fun-rec
  !2
    ((x Map3) (y Nat)) Nat
    (match x
      (case (Rest z) z)
      (case (Slot x2 m)
        (match y
          (case Z x2)
          (case (S i) (!2 m i))))))
(define-fun-rec
  reach
    ((x Nat) (y Reach)) Maybe2
    (match y
      (case (Init initk)
        (ite
          (inj x initk)
          (Just2
            (State2 (Rest2 Nothing)
              initk (range initk) (Rest3 empty2) initk (Rest4 empty)
              (Rest5 true)))
          Nothing2))
      (case (CheckIn g r k q)
        (match (reach x q)
          (case Nothing2 Nothing2)
          (case (Just2 s)
            (ite
              (and (ind r x) (not (!25 (issued s) k)))
              (match s
                (case (State2 z x2 x3 x4 x5 x6 x7)
                  (Just2
                    (State2 (!=2 z (Pair22 r (Just g)))
                      (!= x2 (Pair2 r k)) (add k x3)
                      (!=3 x4 (Pair23 g (add2 (Pair2 (!2 x2 r) k) (!23 x4 g)))) x5 x6
                      (!=5 x7 (Pair25 r false))))))
              Nothing2))))
      (case (EnterRoom f r2 x8 q2)
        (match x8
          (case (Pair2 i j)
            (match (reach x q2)
              (case Nothing2 Nothing2)
              (case (Just2 t)
                (let ((rk (!2 (roomk t) r2)))
                  (ite
                    (and (ind r2 x)
                      (and (!25 (!24 (!23 (cards t) f) i) j)
                        (or (equal rk i) (equal rk j))))
                    (match t
                      (case (State2 x9 x10 x11 x12 x13 x14 x15)
                        (Just2
                          (State2 x9
                            x10 x11 x12 (!= x13 (Pair2 r2 j))
                            (!=4 x14 (Pair24 r2 (add f (!24 x14 r2))))
                            (!=5 x15
                              (Pair25 r2
                                (or (and (==? (!22 x9 r2) (Just f)) (<=> (!24 x14 r2) empty))
                                  (!25 x15 r2))))))))
                    Nothing2)))))))
      (case (ExitRoom h r3 q3)
        (match (reach x q3)
          (case Nothing2 Nothing2)
          (case (Just2 s2)
            (ite
              (and (ind r3 x) (!25 (!24 (isin s2) r3) h))
              (match s2
                (case (State2 x16 x17 x18 x19 x20 x21 x22)
                  (Just2
                    (State2 x16
                      x17 x18 x19 x20 (!=4 x21 (Pair24 r3 (rem h (!24 x21 r3)))) x22))))
              Nothing2))))))
(define-fun
  psafe
    ((x Nat) (y Nat) (z Nat) (x2 Reach)) Bool
    (match (reach x x2)
      (case Nothing2 true)
      (case (Just2 s)
        (=> (and (ind y x) (and (!25 (safe s) y) (!25 (!24 (isin s) y) z)))
          (==? (!22 (owns s) y) (Just z))))))
(assert-not
  (forall ((r Nat) (g Nat) (q Reach)) (psafe (S Z) r g q)))
(check-sat)
