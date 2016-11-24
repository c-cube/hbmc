(declare-datatypes (a)
  ((list (Nil) (Cons (Cons_0 a) (Cons_1 (list a))))))
(declare-datatypes (a b) ((Pair (Pair2 (first a) (second b)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes ()
  ((Expr (X)
     (Add (Add_0 Expr) (Add_1 Expr)) (Mul (Mul_0 Expr) (Mul_1 Expr))
     (Num (Num_0 Nat)))))
(declare-datatypes (a b)
  ((Either (Left (Left_0 a)) (Right (Right_0 b)))))
(declare-datatypes ()
  ((Char (PAR1)
     (PAR2) (PLUS) (MULT) (CHARX) (DIG0) (DIG1) (DIG2) (DIG3) (DIG4)
     (DIG5) (DIG6) (DIG7) (DIG8) (DIG9))))
(define-fun
  min10
    ((x Nat)) (Either Char Nat)
    (match x
      (case Z (as (Left DIG0) (Either Char Nat)))
      (case (S n1)
        (match n1
          (case Z (as (Left DIG1) (Either Char Nat)))
          (case (S n2)
            (match n2
              (case Z (as (Left DIG2) (Either Char Nat)))
              (case (S n3)
                (match n3
                  (case Z (as (Left DIG3) (Either Char Nat)))
                  (case (S n4)
                    (match n4
                      (case Z (as (Left DIG4) (Either Char Nat)))
                      (case (S n5)
                        (match n5
                          (case Z (as (Left DIG5) (Either Char Nat)))
                          (case (S n6)
                            (match n6
                              (case Z (as (Left DIG6) (Either Char Nat)))
                              (case (S n7)
                                (match n7
                                  (case Z (as (Left DIG7) (Either Char Nat)))
                                  (case (S n8)
                                    (match n8
                                      (case Z (as (Left DIG8) (Either Char Nat)))
                                      (case (S n9)
                                        (match n9
                                          (case Z (as (Left DIG9) (Either Char Nat)))
                                          (case (S n92)
                                            (as (Right n92) (Either Char Nat)))))))))))))))))))))))
(define-fun-rec
  mod10
    ((x Nat)) (Pair Char Nat)
    (match (min10 x)
      (case (Left d) (Pair2 d Z))
      (case (Right n)
        (match (mod10 n) (case (Pair2 d2 m) (Pair2 d2 (S m)))))))
(define-fun-rec
  showNum_num
    ((x (list Char)) (y Nat)) (list Char)
    (match y
      (case Z x)
      (case (S z)
        (match (mod10 y) (case (Pair2 c n) (showNum_num (Cons c x) n))))))
(define-fun
  showNum
    ((x Nat)) (list Char)
    (match x
      (case Z (Cons DIG0 (as Nil (list Char))))
      (case (S y) (showNum_num (as Nil (list Char)) x))))
(define-fun-rec
  (par (a)
    (append
       ((x (list a)) (y (list a))) (list a)
       (match x
         (case Nil y)
         (case (Cons z xs) (Cons z (append xs y)))))))
(define-funs-rec
  ((showF ((x Expr)) (list Char))
   (show ((x Expr)) (list Char)))
  ((match x
     (case default (show x))
     (case (Add y z)
       (Cons PAR1 (append (show x) (Cons PAR2 (as Nil (list Char)))))))
   (match x
     (case X (Cons CHARX (as Nil (list Char))))
     (case (Add b c)
       (append (show b)
         (append (Cons PLUS (as Nil (list Char))) (show c))))
     (case (Mul a3 b2)
       (append (showF a3)
         (append (Cons MULT (as Nil (list Char))) (showF b2))))
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
                    (Cons DIG7
                      (Cons PAR2
                        (Cons MULT (Cons CHARX (as Nil (list Char))))))))))))))))
(check-sat)
