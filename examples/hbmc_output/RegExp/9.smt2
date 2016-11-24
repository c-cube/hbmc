(declare-datatypes (a)
  ((list (Nil) (Cons (Cons_0 a) (Cons_1 (list a))))))
(declare-datatypes () ((T (A) (B) (C))))
(declare-datatypes (a)
  ((R (Nil2)
     (Eps) (Atom (Atom_0 a)) (+2 (+_0 (R a)) (+_1 (R a)))
     (>2 (>_0 (R a)) (>_1 (R a))) (Star (Star_0 (R a))))))
(declare-datatypes (a b) ((Pair (Pair2 (first a) (second b)))))
(define-fun-rec
  (par (a)
    (splits2
       ((x a) (y (list (Pair (list a) (list a)))))
       (list (Pair (list a) (list a)))
       (match y
         (case Nil (as Nil (list (Pair (list a) (list a)))))
         (case (Cons z x2)
           (match z
             (case (Pair2 bs cs)
               (Cons (Pair2 (Cons x bs) cs) (splits2 x x2)))))))))
(define-fun-rec
  (par (a)
    (splits
       ((x (list a))) (list (Pair (list a) (list a)))
       (match x
         (case Nil
           (Cons (Pair2 (as Nil (list a)) (as Nil (list a)))
             (as Nil (list (Pair (list a) (list a))))))
         (case (Cons y xs)
           (Cons (Pair2 (as Nil (list a)) x) (splits2 y (splits xs))))))))
(define-fun-rec
  ors
    ((x (list Bool))) Bool
    (match x
      (case Nil false)
      (case (Cons y xs) (or y (ors xs)))))
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
  (par (a)
    (eps
       ((x (R a))) Bool
       (match x
         (case default false)
         (case Eps true)
         (case (+2 p q) (or (eps p) (eps q)))
         (case (>2 r q2) (and (eps r) (eps q2)))
         (case (Star y) true)))))
(define-fun-rec
  okay
    ((x (R T))) Bool
    (match x
      (case default true)
      (case (+2 p q) (and (okay p) (okay q)))
      (case (>2 r q2) (and (okay r) (okay q2)))
      (case (Star p2) (and (okay p2) (not (eps p2))))))
(define-fun-rec
  step
    ((x (R T)) (y T)) (R T)
    (match x
      (case default (as Nil2 (R T)))
      (case (Atom b) (ite (eqT b y) (as Eps (R T)) (as Nil2 (R T))))
      (case (+2 p q) (+2 (step p y) (step q y)))
      (case (>2 r q2)
        (ite
          (eps r) (+2 (>2 (step r y) q2) (step q2 y))
          (+2 (>2 (step r y) q2) (as Nil2 (R T)))))
      (case (Star p2) (>2 (step p2 y) x))))
(define-fun-rec
  rec
    ((x (R T)) (y (list T))) Bool
    (match y
      (case Nil (eps x))
      (case (Cons z xs) (rec (step x z) xs))))
(define-funs-rec
  ((reck2
      ((p (R T)) (q (R T)) (x (list (Pair (list T) (list T)))))
      (list Bool))
   (reck ((x (R T)) (y (list T))) Bool))
  ((match x
     (case Nil (as Nil (list Bool)))
     (case (Cons y z)
       (match y
         (case (Pair2 l r)
           (Cons (and (reck p l) (rec q r)) (reck2 p q z))))))
   (match x
     (case Nil2 false)
     (case Eps
       (match y
         (case Nil true)
         (case (Cons z x2) false)))
     (case (Atom c)
       (match y
         (case Nil false)
         (case (Cons b2 x3)
           (match x3
             (case Nil (eqT c b2))
             (case (Cons x4 x5) false)))))
     (case (+2 p q) (or (reck p y) (reck q y)))
     (case (>2 r q2) (ors (reck2 r q2 (splits y))))
     (case (Star p2)
       (match y
         (case Nil true)
         (case (Cons x6 x7) (and (not (eps p2)) (rec (>2 p2 x) y))))))))
(assert-not
  (forall ((p (R T)) (q (R T)) (s (list T)))
    (= (rec (Star (+2 p q)) s) (rec (+2 (Star p) (Star q)) s))))
(check-sat)
