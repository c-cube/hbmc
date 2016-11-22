(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes ()
  ((Expr (X)
     (Add (Add_0 Expr) (Add_1 Expr)) (Mul (Mul_0 Expr) (Mul_1 Expr))
     (Num (Num_0 Nat)))))
(declare-datatypes ()
  ((Char (PAR1)
     (PAR2) (PLUS) (MULT) (CHARX) (DIG0) (DIG1) (DIG2) (DIG3) (DIG4)
     (DIG5) (DIG6) (DIG7) (DIG8) (DIG9))))
(declare-datatypes ()
  ((Either (Left (Left_0 Char)) (Right (Right_0 Nat)))))
(declare-datatypes () ((Pair (Pair2 (first Char) (second Nat)))))
(declare-datatypes ()
  ((list (Nil) (Cons (Cons_0 Char) (Cons_1 list)))))
(define-fun
  min10
    ((x Nat)) Either
    (match x
      (case Z (Left DIG0))
      (case (S n1)
        (match n1
          (case Z (Left DIG1))
          (case (S n2)
            (match n2
              (case Z (Left DIG2))
              (case (S n3)
                (match n3
                  (case Z (Left DIG3))
                  (case (S n4)
                    (match n4
                      (case Z (Left DIG4))
                      (case (S n5)
                        (match n5
                          (case Z (Left DIG5))
                          (case (S n6)
                            (match n6
                              (case Z (Left DIG6))
                              (case (S n7)
                                (match n7
                                  (case Z (Left DIG7))
                                  (case (S n8)
                                    (match n8
                                      (case Z (Left DIG8))
                                      (case (S n9)
                                        (match n9
                                          (case Z (Left DIG9))
                                          (case (S n92) (Right n92))))))))))))))))))))))
(define-fun-rec
  mod10
    ((x Nat)) Pair
    (match (min10 x)
      (case (Left d) (Pair2 d Z))
      (case (Right n)
        (match (mod10 n) (case (Pair2 d2 m) (Pair2 d2 (S m)))))))
(define-fun-rec
  showNum_num
    ((x list) (y Nat)) list
    (match y
      (case Z x)
      (case (S z)
        (match (mod10 y) (case (Pair2 c n) (showNum_num (Cons c x) n))))))
(define-fun
  showNum
    ((x Nat)) list
    (match x
      (case Z (Cons DIG0 Nil))
      (case (S y) (showNum_num Nil x))))
(define-fun-rec
  append
    ((x list) (y list)) list
    (match x
      (case Nil y)
      (case (Cons z xs) (Cons z (append xs y)))))
(define-funs-rec
  ((showF ((x Expr)) list)
   (show ((x Expr)) list))
  ((match x
     (case default (show x))
     (case (Add y z) (Cons PAR1 (append (show x) (Cons PAR2 Nil)))))
   (match x
     (case X (Cons CHARX Nil))
     (case (Add b c)
       (append (show b) (append (Cons PLUS Nil) (show c))))
     (case (Mul a3 b2)
       (append (showF a3) (append (Cons MULT Nil) (showF b2))))
     (case (Num n) (showNum n)))))
(assert-not
  (forall ((e Expr))
    (distinct (show e)
      (Cons PAR1
        (Cons PAR1
          (Cons CHARX
            (Cons PLUS
              (Cons DIG5
                (Cons PAR2
                  (Cons PLUS
                    (Cons DIG7 (Cons PAR2 (Cons MULT (Cons CHARX Nil))))))))))))))
(check-sat)
