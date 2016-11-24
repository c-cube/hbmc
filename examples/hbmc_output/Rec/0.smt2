(declare-datatypes (a)
  ((list (Nil) (Cons (Cons_0 a) (Cons_1 (list a))))))
(define-fun-rec
  f ((x (list Bool))) Bool
    (match x
      (case Nil true)
      (case (Cons y z) (not (f z)))))
(assert-not (forall ((xs (list Bool))) (not (f xs))))
(check-sat)
