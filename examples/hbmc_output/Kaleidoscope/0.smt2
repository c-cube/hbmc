(declare-datatypes (a)
  ((list (Nil) (Cons (Cons_0 a) (Cons_1 (list a))))))
(declare-datatypes ()
  ((Token (Butterfly) (I) (In) (Me) (Kaleidoscope) (Saw) (The))))
(declare-datatypes () ((N (N_Butterfly) (N_Kaleidoscope))))
(declare-datatypes ()
  ((NP (Pron1) (Det (Det_0 N)) (NP_In (NP_In_0 NP) (NP_In_1 NP)))))
(declare-datatypes ()
  ((VP (See (See_0 NP)) (VP_In (VP_In_0 VP) (VP_In_1 NP)))))
(declare-datatypes () ((S (S2 (p NP) (S_1 VP)))))
(declare-datatypes () ((Case (Subj) (Obj))))
(define-fun
  linN
    ((x N)) (list Token)
    (match x
      (case N_Butterfly (Cons Butterfly (as Nil (list Token))))
      (case N_Kaleidoscope (Cons Kaleidoscope (as Nil (list Token))))))
(define-fun-rec
  (par (a)
    (append
       ((x (list a)) (y (list a))) (list a)
       (match x
         (case Nil y)
         (case (Cons z xs) (Cons z (append xs y)))))))
(define-fun-rec
  linNP
    ((x Case) (y NP)) (list Token)
    (match y
      (case Pron1
        (match x
          (case Subj (Cons I (as Nil (list Token))))
          (case Obj (Cons Me (as Nil (list Token))))))
      (case (Det n) (append (Cons The (as Nil (list Token))) (linN n)))
      (case (NP_In np1 np2)
        (append (append (linNP x np1) (Cons In (as Nil (list Token))))
          (linNP x np2)))))
(define-fun-rec
  linVP
    ((x VP)) (list Token)
    (match x
      (case (See np)
        (append (Cons Saw (as Nil (list Token))) (linNP Obj np)))
      (case (VP_In vp np2)
        (append (append (linVP vp) (Cons In (as Nil (list Token))))
          (linNP Obj np2)))))
(define-fun
  linS
    ((x S)) (list Token)
    (match x (case (S2 np vp) (append (linNP Subj np) (linVP vp)))))
(assert-not
  (forall ((s (list Token)) (t1 S) (t2 S))
    (=> (= s (linS t1)) (=> (= s (linS t2)) (= t1 t2)))))
(check-sat)
