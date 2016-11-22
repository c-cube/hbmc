(declare-datatypes ()
  ((Term ($ ($_0 Term) ($_1 Term)) (TheVar) (K) (I) (S) (B) (C))))
(declare-datatypes () ((Nat (Suc (Suc_0 Nat)) (Z))))
(declare-datatypes () ((Maybe (Nothing) (Just (Just_0 Term)))))
(define-fun
  par2
    ((x Term) (y Term) (z Maybe) (x2 Maybe)) Maybe
    (match z
      (case Nothing
        (match x2
          (case Nothing Nothing)
          (case (Just u_red) (Just ($ x u_red)))))
      (case (Just t_red)
        (match x2
          (case Nothing (Just ($ t_red y)))
          (case (Just u_red2) (Just ($ t_red u_red2)))))))
(define-fun-rec
  step
    ((x Term)) Maybe
    (match x
      (case default Nothing)
      (case ($ y z)
        (let ((x2 (par2 y z (step y) (step z))))
          (match y
            (case default x2)
            (case ($ x3 g)
              (match x3
                (case default x2)
                (case ($ x4 f)
                  (match x4
                    (case default x2)
                    (case S (Just ($ ($ f z) ($ g z))))
                    (case B (Just ($ f ($ g z))))
                    (case C (Just ($ ($ f z) g)))))
                (case K (Just g))))
            (case I (Just z)))))))
(define-fun-rec
  cheating
    ((x Term)) Bool
    (match x
      (case default false)
      (case ($ a b) (or (cheating a) (cheating b)))
      (case TheVar true)))
(define-fun-rec
  astep
    ((x Nat) (y Term)) Maybe
    (match x
      (case (Suc n)
        (match (step y)
          (case Nothing Nothing)
          (case (Just u) (astep n u))))
      (case Z (Just y))))
(assert-not
  (forall ((n Nat) (y Term))
    (=> (= (astep n ($ y TheVar)) (Just ($ TheVar ($ y TheVar))))
      (cheating y))))
(check-sat)
