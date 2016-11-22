(declare-datatypes () ((T (A) (B))))
(declare-datatypes ()
  ((list (Nil) (Cons (Cons_0 T) (Cons_1 list)))))
(declare-datatypes ()
  ((P (AP (AP_0 P)) (BP (BP_0 P)) (PA) (PB) (PE))))
(declare-datatypes () ((C (C2 (C_0 P) (C_1 P)))))
(define-fun-rec
  append
    ((x list) (y list)) list
    (match x
      (case Nil y)
      (case (Cons z xs) (Cons z (append xs y)))))
(define-fun-rec
  linP
    ((x P)) list
    (match x
      (case (AP p) (append (append (Cons A Nil) (linP p)) (Cons A Nil)))
      (case (BP q) (append (append (Cons B Nil) (linP q)) (Cons B Nil)))
      (case PA (Cons A Nil))
      (case PB (Cons B Nil))
      (case PE Nil)))
(define-fun
  linC
    ((x C)) list (match x (case (C2 p q) (append (linP p) (linP q)))))
(assert-not
  (forall ((u C) (v C)) (=> (= (linC u) (linC v)) (= u v))))
(check-sat)
