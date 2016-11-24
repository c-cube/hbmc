(declare-datatypes (a)
  ((list (Nil) (Cons (Cons_0 a) (Cons_1 (list a))))))
(declare-datatypes () ((T (A) (B))))
(declare-datatypes ()
  ((P (AP (AP_0 P)) (BP (BP_0 P)) (PA) (PB) (PE))))
(declare-datatypes () ((C (C2 (C_0 P) (C_1 P)))))
(define-fun-rec
  (par (a)
    (append
       ((x (list a)) (y (list a))) (list a)
       (match x
         (case Nil y)
         (case (Cons z xs) (Cons z (append xs y)))))))
(define-fun-rec
  linP
    ((x P)) (list T)
    (match x
      (case (AP p)
        (append (append (Cons A (as Nil (list T))) (linP p))
          (Cons A (as Nil (list T)))))
      (case (BP q)
        (append (append (Cons B (as Nil (list T))) (linP q))
          (Cons B (as Nil (list T)))))
      (case PA (Cons A (as Nil (list T))))
      (case PB (Cons B (as Nil (list T))))
      (case PE (as Nil (list T)))))
(define-fun
  linC
    ((x C)) (list T)
    (match x (case (C2 p q) (append (linP p) (linP q)))))
(assert-not
  (forall ((u C) (v C)) (=> (= (linC u) (linC v)) (= u v))))
(check-sat)
