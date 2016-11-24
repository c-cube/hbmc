(declare-datatypes (a b) ((Pair (Pair2 (first a) (second b)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes (a) ((Maybe (Nothing) (Just (Just_0 a)))))
(declare-datatypes (a)
  ((Map (Rest (Rest_0 a)) (Slot (Slot_0 a) (Slot_1 (Map a))))))
(declare-datatypes ()
  ((Reach (Init (Init_0 (Map Nat)))
     (CheckIn (CheckIn_0 Nat)
       (CheckIn_1 Nat) (CheckIn_2 Nat) (CheckIn_3 Reach))
     (EnterRoom (EnterRoom_0 Nat)
       (EnterRoom_1 Nat) (EnterRoom_2 (Pair Nat Nat)) (EnterRoom_3 Reach))
     (ExitRoom (ExitRoom_0 Nat) (ExitRoom_1 Nat) (ExitRoom_2 Reach)))))
(declare-datatypes ()
  ((State
     (State2 (State_0 (Map (Maybe Nat)))
       (State_1 (Map Nat)) (State_2 (Map Bool))
       (State_3 (Map (Map (Map Bool)))) (State_4 (Map Nat))
       (State_5 (Map (Map Bool))) (State_6 (Map Bool))))))
(define-fun
  safe
    ((x State)) (Map Bool)
    (match x (case (State2 y z x2 x3 x4 x5 x6) x6)))
(define-fun
  roomk
    ((x State)) (Map Nat)
    (match x (case (State2 y z x2 x3 x4 x5 x6) x4)))
(define-fun
  owns
    ((x State)) (Map (Maybe Nat))
    (match x (case (State2 y z x2 x3 x4 x5 x6) y)))
(define-fun
  issued
    ((x State)) (Map Bool)
    (match x (case (State2 y z x2 x3 x4 x5 x6) x2)))
(define-fun
  isin
    ((x State)) (Map (Map Bool))
    (match x (case (State2 y z x2 x3 x4 x5 x6) x5)))
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
    ((x Nat) (y Nat) (z (Map Nat))) Bool
    (match x
      (case Z true)
      (case (S x2)
        (match z
          (case (Rest y2) (not (equal y y2)))
          (case (Slot y3 m) (and (not (equal y y3)) (inj_upto x2 y m)))))))
(define-fun-rec
  inj
    ((x Nat) (y (Map Nat))) Bool
    (match x
      (case Z true)
      (case (S z)
        (match y
          (case (Rest x2) false)
          (case (Slot x3 m) (and (inj z m) (inj_upto x x3 m)))))))
(define-fun empty2 () (Map (Map Bool)) (Rest (Rest false)))
(define-fun empty () (Map Bool) (Rest false))
(define-fun
  cards
    ((x State)) (Map (Map (Map Bool)))
    (match x (case (State2 y z x2 x3 x4 x5 x6) x3)))
(define-fun
  ==?
    ((x (Maybe Nat)) (y (Maybe Nat))) Bool
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
    ((x (Map Bool)) (y (Map Bool))) Bool
    (match x
      (case (Rest z)
        (match y
          (case (Rest y2) (==. z y2))
          (case (Slot y3 q) (and (==. z y3) (<=> x q)))))
      (case (Slot x2 r)
        (match y
          (case (Rest y4) (and (==. x2 y4) (<=> r y)))
          (case (Slot y5 q2) (and (==. x2 y5) (<=> r q2)))))))
(define-fun-rec
  (par (a)
    (!=
       ((x (Map a)) (y (Pair Nat a))) (Map a)
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
                 (case (S j) (Slot x3 (!= m (Pair2 j y3))))))))))))
(define-fun
  add ((x Nat) (y (Map Bool))) (Map Bool) (!= y (Pair2 x true)))
(define-fun-rec
  range
    ((x (Map Nat))) (Map Bool)
    (match x
      (case (Rest y) (add y empty))
      (case (Slot z m) (add z (range m)))))
(define-fun
  rem ((x Nat) (y (Map Bool))) (Map Bool) (!= y (Pair2 x false)))
(define-fun-rec
  (par (a)
    (!2
       ((x (Map a)) (y Nat)) a
       (match x
         (case (Rest z) z)
         (case (Slot x2 m)
           (match y
             (case Z x2)
             (case (S i) (!2 m i))))))))
(define-fun
  add2
    ((x (Pair Nat Nat)) (y (Map (Map Bool)))) (Map (Map Bool))
    (match x (case (Pair2 z y2) (!= y (Pair2 z (add y2 (!2 y z)))))))
(define-fun-rec
  reach
    ((x Nat) (y Reach)) (Maybe State)
    (match y
      (case (Init initk)
        (ite
          (inj x initk)
          (Just
            (State2 (Rest (as Nothing (Maybe Nat)))
              initk (range initk) (Rest empty2) initk (Rest empty) (Rest true)))
          (as Nothing (Maybe State))))
      (case (CheckIn g r k q)
        (match (reach x q)
          (case Nothing (as Nothing (Maybe State)))
          (case (Just s)
            (ite
              (and (ind r x) (not (!2 (issued s) k)))
              (match s
                (case (State2 z x2 x3 x4 x5 x6 x7)
                  (Just
                    (State2 (!= z (Pair2 r (Just g)))
                      (!= x2 (Pair2 r k)) (add k x3)
                      (!= x4 (Pair2 g (add2 (Pair2 (!2 x2 r) k) (!2 x4 g)))) x5 x6
                      (!= x7 (Pair2 r false))))))
              (as Nothing (Maybe State))))))
      (case (EnterRoom f r2 x8 q2)
        (match x8
          (case (Pair2 i j)
            (match (reach x q2)
              (case Nothing (as Nothing (Maybe State)))
              (case (Just t)
                (let ((rk (!2 (roomk t) r2)))
                  (ite
                    (and (ind r2 x)
                      (and (!2 (!2 (!2 (cards t) f) i) j)
                        (or (equal rk i) (equal rk j))))
                    (match t
                      (case (State2 x9 x10 x11 x12 x13 x14 x15)
                        (Just
                          (State2 x9
                            x10 x11 x12 (!= x13 (Pair2 r2 j))
                            (!= x14 (Pair2 r2 (add f (!2 x14 r2))))
                            (!= x15
                              (Pair2 r2
                                (or (and (==? (!2 x9 r2) (Just f)) (<=> (!2 x14 r2) empty))
                                  (!2 x15 r2))))))))
                    (as Nothing (Maybe State)))))))))
      (case (ExitRoom h r3 q3)
        (match (reach x q3)
          (case Nothing (as Nothing (Maybe State)))
          (case (Just s2)
            (ite
              (and (ind r3 x) (!2 (!2 (isin s2) r3) h))
              (match s2
                (case (State2 x16 x17 x18 x19 x20 x21 x22)
                  (Just
                    (State2 x16
                      x17 x18 x19 x20 (!= x21 (Pair2 r3 (rem h (!2 x21 r3)))) x22))))
              (as Nothing (Maybe State))))))))
(define-fun
  psafe
    ((x Nat) (y Nat) (z Nat) (x2 Reach)) Bool
    (match (reach x x2)
      (case Nothing true)
      (case (Just s)
        (=> (and (ind y x) (and (!2 (safe s) y) (!2 (!2 (isin s) y) z)))
          (==? (!2 (owns s) y) (Just z))))))
(assert-not
  (forall ((r Nat) (g Nat) (q Reach)) (psafe (S (S (S Z))) r g q)))
(check-sat)
