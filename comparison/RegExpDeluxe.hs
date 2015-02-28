module RegExpDeluxe where


import Test.LazySmallCheck
import Prelude hiding ((==))
-- import HBMC

label l x = x

instance Serial Nat where
  series = cons0 Z \/ cons1 S

data Nat
  = Z
  | S Nat
 deriving ( Eq, Show )

data R a
  = Nil
  | Eps
  | Atom a
  | R a :+: R a
  | R a :&: R a
  | R a :>: R a
  | Star (R a)
 deriving ( Eq, Show )

instance Serial a => Serial (R a) where
  series = cons0 Nil \/ cons0 Eps \/ cons1 Atom
        \/ cons2 (:+:) \/ cons2 (:&:) \/ cons2 (:>:)
        \/ cons1 Star

data T = A | B | C
 deriving ( Eq, Ord, Show )

instance Serial T where
  series = cons0 A \/ cons0 B \/ cons0 C

(.+.), (.&.), (.>.) :: R T -> R T -> R T
-- a .+. b = a :+: b
Nil .+. q   = q
p   .+. Nil = p
p   .+. q   = p :+: q

-- a .&. b = a :&: b
Nil .&. q   = Nil
p   .&. Nil = Nil
p   .&. q   = p :&: q

-- a .>. b = a :>: b
Nil .>. q   = Nil
p   .>. Nil = Nil
Eps .>. q   = q
p   .>. Eps = p
p   .>. q   = p :>: q

eps :: R T -> Bool
eps Eps                = True
eps (p :+: q)          = label 1 (eps p) || label 2 (eps q)
eps (p :&: q)          = label 1 (eps p) && label 2 (eps q)
eps (p :>: q)          = label 1 (eps p) && label 2 (eps q)
eps (Star _)           = True
eps _                  = False

epsProp :: R T -> Property
epsProp Eps                = lift True
epsProp (p :+: q)          = label 1 (epsProp p) *|* label 2 (epsProp q)
epsProp (p :&: q)          = label 1 (epsProp p) *&* label 2 (epsProp q)
epsProp (p :>: q)          = label 1 (epsProp p) *&* label 2 (epsProp q)
epsProp (Star _)           = lift True
epsProp _                  = lift False

cond :: Bool -> R T
cond False = Nil
cond True  = Eps

(===) :: T -> T -> Bool
A === A = True
B === B = True
C === C = True
_ === _ = False

isZero :: Nat -> Bool
isZero Z = True
isZero _ = False

{-
fromTo, fromTo' :: R T -> Nat -> Nat -> R T
fromTo  p i j = cond (isZero i) .+. (p .>. fromTo' p i j)

fromTo' p _     Z     = Nil
fromTo' p Z     (S j) = label 1 (fromTo p Z j)
fromTo' p (S i) (S j) = label 1 (fromTo p i j)
-}

minus1 :: Nat -> Nat
minus1 Z     = Z
minus1 (S x) = x

rep :: R T -> Nat -> Nat -> R T
rep p i (S j) = (cond (isZero i) :+: p) :>: rep p (minus1 i) j
rep p i Z = case i of
             Z   -> Eps
             S _ -> Nil



{-
step :: R T -> T -> R T
step (Atom a)  x | a === x = Eps
step (p :+: q) x           =  label 1 (step p x) :+: label 2 (step q x)
step (p :&: q) x           =  label 1 (step p x) :&: label 2 (step q x)
step (p :>: q) x           = (label 1 (step p x) :>: q) :+: (cond (eps p) :>: label 2 (step q x))
step (Star p)  x           =  label 1 (step p x) :>: Star p
step _         x           = Nil
-}

step :: R T -> T -> R T
step (Atom a)  x | a === x = Eps
step (p :+: q) x           =  label 1 (step p x) :+: label 2 (step q x)
step (p :&: q) x           =  label 1 (step p x) :&: label 2 (step q x)
step (p :>: q)x| eps p     = (label 1 (step p x) :>: q) :+: label 2 (step q x)
               | otherwise =  label 1 (step p x) :>: q
step (Star p)  x           =  label 1 (step p x) :>: Star p
step _         x           = Nil

rec :: R T -> [T] -> Property
rec p []     = epsProp p
rec p (x:xs) = rec (step p x) xs

prop_koen p q s = rec (p :>: q) s *=* rec (q :>: p) s

--
-- prop_star_seq p q s = rec (Star (p :>: q)) s *=* rec (Star p :>: Star q) s
--
-- prop_switcheroo p q s = rec (p :+: q) s *=* rec (p :>: q) s
--
-- prop_bad_assoc p q r s = rec (p :+: (q :>: r)) s *=* rec ((p :+: q) :>: r) s

-- 2m48s:
prop_star_plus   p q s = rec (Star (p :+: q)) s *=* rec (Star p :+: Star q) s
prop_star_plus_l p q s = rec (Star (p :+: q)) s *=>* rec (Star p :+: Star q) s
prop_star_plus_r p q s = rec (Star p :+: Star q) s *=>* rec (Star (p :+: q)) s

-- 10s:
-- prop_star_plus p q a b = rec (Star (p :+: q)) [a,b] *=* rec (Star p :+: Star q) [a,b]

prop_Conj p s =
  neg (epsProp p) *=>* neg (rec (p :&: (p :>: p)) s)

prop_Conj' p s =
  neg (epsProp p) *=>* neg (rec (p .&. (p .>. p)) s)

iter :: Nat -> R T -> R T
iter Z     _ = Eps
iter (S n) r = r :>: iter n r

prop_iter i j p s =
  neg (lift (i ==== j)) *=>*
  neg (epsProp p) *=>*
  neg (rec (iter i p :&: iter j p) s)

prop_iter' i j p s =
  neg (lift (i ==== j)) *=>*
  neg (epsProp p) *=>*
  neg (rec (iter i p .&. iter j p) s)

(====) :: Nat -> Nat -> Bool
Z   ==== Z   = True
Z{} ==== S{} = False
S{} ==== Z{} = False
S n ==== S m = n ==== m

{-
prop_FromToConj p i i' j j' s =
  eps p *=* False ==>
  i  *=* S Z ==>
  i' *=* S (S Z) ==>
  j  *=* S (S Z) ==>
  j' *=* S (S (S Z)) ==>
    rec (rep p i j .&. rep p i' j') s *=* rec (rep p (maxx i i') (minn j j')) s
-}

i  = S Z
i' = S (S Z)
j  = S (S Z)
j' = S (S (S Z))

prop_FromToConj' p s =
  neg (epsProp p)
    *=>* rec (rep p i j .&. rep p i' j') s
    *=*  rec (rep p (maxx i i') (minn j j')) s

prop_FromToConj p a b =
  neg (epsProp p)
    *=>* rec (rep p i j .&. rep p i' j') [a,b]
    *=>* rec (rep p (maxx i i') (minn j j')) [a,b]

maxx :: Nat -> Nat -> Nat
maxx Z     b     = b
maxx (S a) Z     = S a
maxx (S a) (S b) = S (maxx a b)

minn :: Nat -> Nat -> Nat
minn Z     b     = Z
minn S{}   Z     = Z
minn (S a) (S b) = S (minn a b)
