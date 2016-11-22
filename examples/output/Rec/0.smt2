(declare-datatypes ()
  ((list (Nil) (Cons (Cons_0 Bool) (Cons_1 list)))))
(define-fun-rec
  f ((x list)) Bool
    (match x
      (case Nil true)
      (case (Cons y z) (not (f z)))))
(assert-not (forall ((xs list)) (not (f xs))))
(check-sat)
