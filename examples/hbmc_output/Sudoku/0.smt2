(declare-datatypes (a)
  ((list (Nil) (Cons (Cons_0 a) (Cons_1 (list a))))))
(declare-datatypes (a b) ((Pair (Pair2 (first a) (second b)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes (a) ((Maybe (Nothing) (Just (Just_0 a)))))
(declare-datatypes ()
  ((Cell (C1) (C2) (C3) (C4) (C5) (C6) (C7) (C8) (C9))))
(declare-datatypes ()
  ((Sudoku (Sudoku2 (Sudoku_0 (list (list (Maybe Cell))))))))
(define-fun-rec
  (par (a b)
    (zip
       ((x (list a)) (y (list b))) (list (Pair a b))
       (match x
         (case Nil (as Nil (list (Pair a b))))
         (case (Cons z x2)
           (match y
             (case Nil (as Nil (list (Pair a b))))
             (case (Cons x3 x4) (Cons (Pair2 z x3) (zip x2 x4)))))))))
(define-fun-rec
  (par (a)
    (transpose3
       ((x (list (list a)))) (list (list a))
       (match x
         (case Nil (as Nil (list (list a))))
         (case (Cons y z)
           (match y
             (case Nil (transpose3 z))
             (case (Cons x2 t) (Cons t (transpose3 z)))))))))
(define-fun-rec
  (par (a)
    (transpose2
       ((x (list (list a)))) (list a)
       (match x
         (case Nil (as Nil (list a)))
         (case (Cons y z)
           (match y
             (case Nil (transpose2 z))
             (case (Cons h x2) (Cons h (transpose2 z)))))))))
(define-fun-rec
  (par (a)
    (transpose
       ((x (list (list a)))) (list (list a))
       (match x
         (case Nil (as Nil (list (list a))))
         (case (Cons y xss)
           (match y
             (case Nil (transpose xss))
             (case (Cons z xs)
               (Cons (Cons z (transpose2 xss))
                 (transpose (Cons xs (transpose3 xss)))))))))))
(define-fun-rec
  (par (a)
    (take
       ((x Nat) (y (list a))) (list a)
       (match x
         (case Z (as Nil (list a)))
         (case (S z)
           (match y
             (case Nil (as Nil (list a)))
             (case (Cons x2 x3) (Cons x2 (take z x3)))))))))
(define-fun
  rows
    ((x Sudoku)) (list (list (Maybe Cell)))
    (match x (case (Sudoku2 y) y)))
(define-fun n9 () Nat (S (S (S (S (S (S (S (S (S Z))))))))))
(define-fun n6 () Nat (S (S (S (S (S (S Z)))))))
(define-fun n3 () Nat (S (S (S Z))))
(define-fun-rec
  (par (a)
    (length
       ((x (list a))) Nat
       (match x
         (case Nil Z)
         (case (Cons y xs) (S (length xs)))))))
(define-fun-rec
  isOkayBlock2
    ((x (list (Maybe Cell)))) (list Cell)
    (match x
      (case Nil (as Nil (list Cell)))
      (case (Cons y z)
        (match y
          (case Nothing (isOkayBlock2 z))
          (case (Just n) (Cons n (isOkayBlock2 z)))))))
(define-fun
  (par (t)
    (isJust
       ((x (Maybe t))) Bool
       (match x
         (case Nothing false)
         (case (Just y) true)))))
(define-funs-rec
  ((isSolved3
      ((x (list (list (Maybe Cell)))) (y (list (Maybe Cell))))
      (list Bool))
   (isSolved2 ((x (list (list (Maybe Cell))))) (list Bool)))
  ((match y
     (case Nil (isSolved2 x))
     (case (Cons z x2) (Cons (isJust z) (isSolved3 x x2))))
   (match x
     (case Nil (as Nil (list Bool)))
     (case (Cons y z) (isSolved3 z y)))))
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
  isSudoku2
    ((x (list (list (Maybe Cell))))) (list Bool)
    (match x
      (case Nil (as Nil (list Bool)))
      (case (Cons y z) (Cons (equal (length y) n9) (isSudoku2 z)))))
(define-fun
  eqCell
    ((x Cell) (y Cell)) Bool
    (match x
      (case C1
        (match y
          (case default false)
          (case C1 true)))
      (case C2
        (match y
          (case default false)
          (case C2 true)))
      (case C3
        (match y
          (case default false)
          (case C3 true)))
      (case C4
        (match y
          (case default false)
          (case C4 true)))
      (case C5
        (match y
          (case default false)
          (case C5 true)))
      (case C6
        (match y
          (case default false)
          (case C6 true)))
      (case C7
        (match y
          (case default false)
          (case C7 true)))
      (case C8
        (match y
          (case default false)
          (case C8 true)))
      (case C9
        (match y
          (case default false)
          (case C9 true)))))
(define-funs-rec
  ((isSolutionOf3
      ((x (list (Pair (list (Maybe Cell)) (list (Maybe Cell)))))
       (y (list (Pair (Maybe Cell) (Maybe Cell)))))
      (list Bool))
   (isSolutionOf2
      ((x (list (Pair (list (Maybe Cell)) (list (Maybe Cell))))))
      (list Bool)))
  ((match y
     (case Nil (isSolutionOf2 x))
     (case (Cons z x2)
       (let ((x3 (isSolutionOf3 x x2)))
         (match z
           (case (Pair2 x4 x5)
             (match x4
               (case Nothing x3)
               (case (Just n1)
                 (match x5
                   (case Nothing x3)
                   (case (Just n2) (Cons (eqCell n1 n2) (isSolutionOf3 x x2)))))))))))
   (match x
     (case Nil (as Nil (list Bool)))
     (case (Cons y z)
       (match y
         (case (Pair2 row1 row2) (isSolutionOf3 z (zip row1 row2))))))))
(define-fun-rec
  elem
    ((x Cell) (y (list Cell))) Bool
    (match y
      (case Nil false)
      (case (Cons z ys) (or (eqCell x z) (elem x ys)))))
(define-fun-rec
  unique
    ((x (list Cell))) Bool
    (match x
      (case Nil true)
      (case (Cons y xs) (and (not (elem y xs)) (unique xs)))))
(define-fun
  isOkayBlock
    ((x (list (Maybe Cell)))) Bool (unique (isOkayBlock2 x)))
(define-fun-rec
  isOkay2
    ((x (list (list (Maybe Cell))))) (list Bool)
    (match x
      (case Nil (as Nil (list Bool)))
      (case (Cons y z) (Cons (isOkayBlock y) (isOkay2 z)))))
(define-fun-rec
  (par (a)
    (drop
       ((x Nat) (y (list a))) (list a)
       (match x
         (case Z y)
         (case (S z)
           (match y
             (case Nil (as Nil (list a)))
             (case (Cons x2 x3) (drop z x3))))))))
(define-fun
  difficult
    () Sudoku
    (Sudoku2
      (Cons
        (Cons (Just C8)
          (Cons (as Nothing (Maybe Cell))
            (Cons (as Nothing (Maybe Cell))
              (Cons (as Nothing (Maybe Cell))
                (Cons (as Nothing (Maybe Cell))
                  (Cons (as Nothing (Maybe Cell))
                    (Cons (as Nothing (Maybe Cell))
                      (Cons (as Nothing (Maybe Cell))
                        (Cons (as Nothing (Maybe Cell))
                          (as Nil (list (Maybe Cell))))))))))))
        (Cons
          (Cons (as Nothing (Maybe Cell))
            (Cons (as Nothing (Maybe Cell))
              (Cons (Just C3)
                (Cons (Just C6)
                  (Cons (as Nothing (Maybe Cell))
                    (Cons (as Nothing (Maybe Cell))
                      (Cons (as Nothing (Maybe Cell))
                        (Cons (as Nothing (Maybe Cell))
                          (Cons (as Nothing (Maybe Cell))
                            (as Nil (list (Maybe Cell))))))))))))
          (Cons
            (Cons (as Nothing (Maybe Cell))
              (Cons (Just C7)
                (Cons (as Nothing (Maybe Cell))
                  (Cons (as Nothing (Maybe Cell))
                    (Cons (Just C9)
                      (Cons (as Nothing (Maybe Cell))
                        (Cons (Just C2)
                          (Cons (as Nothing (Maybe Cell))
                            (Cons (as Nothing (Maybe Cell))
                              (as Nil (list (Maybe Cell))))))))))))
            (Cons
              (Cons (as Nothing (Maybe Cell))
                (Cons (Just C5)
                  (Cons (as Nothing (Maybe Cell))
                    (Cons (as Nothing (Maybe Cell))
                      (Cons (as Nothing (Maybe Cell))
                        (Cons (Just C7)
                          (Cons (as Nothing (Maybe Cell))
                            (Cons (as Nothing (Maybe Cell))
                              (Cons (as Nothing (Maybe Cell))
                                (as Nil (list (Maybe Cell))))))))))))
              (Cons
                (Cons (as Nothing (Maybe Cell))
                  (Cons (as Nothing (Maybe Cell))
                    (Cons (as Nothing (Maybe Cell))
                      (Cons (as Nothing (Maybe Cell))
                        (Cons (Just C4)
                          (Cons (Just C5)
                            (Cons (Just C7)
                              (Cons (as Nothing (Maybe Cell))
                                (Cons (as Nothing (Maybe Cell))
                                  (as Nil (list (Maybe Cell))))))))))))
                (Cons
                  (Cons (as Nothing (Maybe Cell))
                    (Cons (as Nothing (Maybe Cell))
                      (Cons (as Nothing (Maybe Cell))
                        (Cons (Just C1)
                          (Cons (as Nothing (Maybe Cell))
                            (Cons (as Nothing (Maybe Cell))
                              (Cons (as Nothing (Maybe Cell))
                                (Cons (Just C3)
                                  (Cons (as Nothing (Maybe Cell))
                                    (as Nil (list (Maybe Cell))))))))))))
                  (Cons
                    (Cons (as Nothing (Maybe Cell))
                      (Cons (as Nothing (Maybe Cell))
                        (Cons (Just C1)
                          (Cons (as Nothing (Maybe Cell))
                            (Cons (as Nothing (Maybe Cell))
                              (Cons (as Nothing (Maybe Cell))
                                (Cons (as Nothing (Maybe Cell))
                                  (Cons (Just C6)
                                    (Cons (Just C8) (as Nil (list (Maybe Cell))))))))))))
                    (Cons
                      (Cons (as Nothing (Maybe Cell))
                        (Cons (as Nothing (Maybe Cell))
                          (Cons (Just C8)
                            (Cons (Just C5)
                              (Cons (as Nothing (Maybe Cell))
                                (Cons (as Nothing (Maybe Cell))
                                  (Cons (as Nothing (Maybe Cell))
                                    (Cons (Just C1)
                                      (Cons (as Nothing (Maybe Cell))
                                        (as Nil (list (Maybe Cell))))))))))))
                      (Cons
                        (Cons (as Nothing (Maybe Cell))
                          (Cons (Just C9)
                            (Cons (as Nothing (Maybe Cell))
                              (Cons (as Nothing (Maybe Cell))
                                (Cons (as Nothing (Maybe Cell))
                                  (Cons (as Nothing (Maybe Cell))
                                    (Cons (Just C4)
                                      (Cons (as Nothing (Maybe Cell))
                                        (Cons (as Nothing (Maybe Cell))
                                          (as Nil (list (Maybe Cell))))))))))))
                        (as Nil (list (list (Maybe Cell)))))))))))))))
(define-fun-rec
  blocks3x34
    ((x (list (list (Maybe Cell))))) (list (list (Maybe Cell)))
    (match x
      (case Nil (as Nil (list (list (Maybe Cell)))))
      (case (Cons y z) (Cons (drop n6 y) (blocks3x34 z)))))
(define-fun-rec
  blocks3x33
    ((x (list (list (Maybe Cell))))) (list (list (Maybe Cell)))
    (match x
      (case Nil (as Nil (list (list (Maybe Cell)))))
      (case (Cons y z) (Cons (take n3 (drop n3 y)) (blocks3x33 z)))))
(define-fun-rec
  blocks3x32
    ((x (list (list (Maybe Cell))))) (list (list (Maybe Cell)))
    (match x
      (case Nil (as Nil (list (list (Maybe Cell)))))
      (case (Cons y z) (Cons (take n3 y) (blocks3x32 z)))))
(define-fun-rec
  blocks2
    ((x (list (list (Maybe Cell))))) (list (list (Maybe Cell)))
    (match x
      (case Nil (as Nil (list (list (Maybe Cell)))))
      (case (Cons y z) (Cons y (blocks2 z)))))
(define-fun-rec
  (par (a)
    (append
       ((x (list a)) (y (list a))) (list a)
       (match x
         (case Nil y)
         (case (Cons z xs) (Cons z (append xs y)))))))
(define-fun-rec
  (par (a)
    (group3
       ((x (list (list a)))) (list (list a))
       (match x
         (case Nil (as Nil (list (list a))))
         (case (Cons xs1 y)
           (match y
             (case Nil (as Nil (list (list a))))
             (case (Cons xs2 z)
               (match z
                 (case Nil (as Nil (list (list a))))
                 (case (Cons xs3 xss)
                   (Cons (append xs1 (append xs2 xs3)) (group3 xss)))))))))))
(define-fun
  blocks3x3
    ((x Sudoku)) (list (list (Maybe Cell)))
    (append (group3 (blocks3x32 (rows x)))
      (append (group3 (blocks3x33 (rows x)))
        (group3 (blocks3x34 (rows x))))))
(define-fun
  blocks
    ((x Sudoku)) (list (list (Maybe Cell)))
    (append (blocks2 (rows x))
      (append (blocks2 (transpose (rows x))) (blocks3x3 x))))
(define-fun-rec
  and2
    ((x (list Bool))) Bool
    (match x
      (case Nil true)
      (case (Cons y xs) (and y (and2 xs)))))
(define-fun isOkay ((x Sudoku)) Bool (and2 (isOkay2 (blocks x))))
(define-fun
  isSolved
    ((x Sudoku)) Bool
    (match x (case (Sudoku2 sud) (and2 (isSolved2 sud)))))
(define-fun
  isSolutionOf
    ((x Sudoku) (y Sudoku)) Bool
    (and (isSolved x)
      (and (isOkay x) (and2 (isSolutionOf2 (zip (rows x) (rows y)))))))
(define-fun
  isSudoku
    ((x Sudoku)) Bool
    (match x
      (case (Sudoku2 sud)
        (and (equal (length sud) n9) (and2 (isSudoku2 sud))))))
(assert-not
  (forall ((s Sudoku))
    (or (not (isSudoku s)) (not (isSolutionOf s difficult)))))
(check-sat)
