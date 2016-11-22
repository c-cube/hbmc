(declare-datatypes () ((Tok (C) (D) (X) (Y) (Plus) (Mul))))
(declare-datatypes ()
  ((list (Nil) (Cons (Cons_0 Tok) (Cons_1 list)))))
(declare-datatypes ()
  ((E (+2 (+_0 E) (+_1 E)) (*2 (*_0 E) (*_1 E)) (EX) (EY))))
(define-fun-rec
  assoc
    ((x E)) E
    (match x
      (case default x)
      (case (+2 y c)
        (match y
          (case default (+2 (assoc y) (assoc c)))
          (case (+2 a b) (assoc (+2 a (+2 b c))))))
      (case (*2 a2 b2) (*2 (assoc a2) (assoc b2)))))
(define-fun-rec
  append
    ((x list) (y list)) list
    (match x
      (case Nil y)
      (case (Cons z xs) (Cons z (append xs y)))))
(define-funs-rec
  ((linTerm ((x E)) list)
   (lin ((x E)) list))
  ((match x
     (case default (lin x))
     (case (*2 a b)
       (append (append (Cons C Nil) (lin (+2 a b))) (Cons D Nil))))
   (match x
     (case (+2 a b)
       (append (append (linTerm a) (Cons Plus Nil)) (linTerm b)))
     (case (*2 a3 b2)
       (append (append (lin a3) (Cons Mul Nil)) (lin b2)))
     (case EX (Cons X Nil))
     (case EY (Cons Y Nil)))))
(assert-not
  (forall ((u E) (v E))
    (=> (= (lin u) (lin v)) (= (assoc u) (assoc v)))))
(check-sat)
