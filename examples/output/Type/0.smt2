(declare-datatypes ()
  ((Ty (Arr (Arr_0 Ty) (Arr_1 Ty)) (A) (B) (C))))
(declare-datatypes ()
  ((list (Nil) (Cons (Cons_0 Ty) (Cons_1 list)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((Maybe (Nothing) (Just (Just_0 Ty)))))
(declare-datatypes ()
  ((Expr (App (App_0 Expr) (App_1 Expr) (App_2 Ty))
     (Lam (Lam_0 Expr)) (Var (Var_0 Nat)))))
(define-fun-rec
  index
    ((x list) (y Nat)) Maybe
    (match x
      (case Nil Nothing)
      (case (Cons z xs)
        (match y
          (case Z (Just z))
          (case (S n) (index xs n))))))
(define-fun-rec
  eqType
    ((x Ty) (y Ty)) Bool
    (match x
      (case (Arr a z)
        (match y
          (case default false)
          (case (Arr b y2) (and (eqType a b) (eqType z y2)))))
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
  tc
    ((x list) (y Expr) (z Ty)) Bool
    (match y
      (case (App f x2 tx) (and (tc x f (Arr tx z)) (tc x x2 tx)))
      (case (Lam e)
        (match z
          (case default false)
          (case (Arr tx2 t) (tc (Cons tx2 x) e t))))
      (case (Var x3)
        (match (index x x3)
          (case Nothing false)
          (case (Just tx3) (eqType tx3 z))))))
(assert-not
  (forall ((e Expr))
    (not (tc Nil e (Arr (Arr B C) (Arr (Arr A B) (Arr A C)))))))
(check-sat)
