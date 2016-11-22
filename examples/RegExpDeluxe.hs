module RegExpDeluxe where

import Tip hiding ((.&.))
import Prelude hiding ((==))

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

data T = A | B | C
 deriving ( Eq, Show )

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

-- FLAGS: meps
eps :: R T -> Bool
eps Eps                = True
eps (p :+: q)          = eps p || eps q
eps (p :&: q)          = eps p && eps q
eps (p :>: q)          = eps p && eps q
eps (Star _)           = True
eps _                  = False

cond :: Bool -> R T
cond False = Nil
cond True  = Eps

eqT :: T -> T -> Bool
A `eqT` A = True
B `eqT` B = True
C `eqT` C = True
_ `eqT` _ = False

eqNat :: Nat -> Nat -> Bool
Z   `eqNat` Z   = True
Z{} `eqNat` S{} = False
S{} `eqNat` Z{} = False
S n `eqNat` S m = n `eqNat` m

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


iter :: Nat -> R T -> R T
iter Z     _ = Eps
iter (S n) r = r :>: iter n r

{-
prop_iter i j p s =
  i `eqNat` j === False ==>
  eps p === False ==>
  rec (iter i p :&: iter j p) s === False

prop_iter' i j p s =
  i `eqNat` j === False ==>
  eps p === False ==>
  rec (iter i p .&. iter j p) s === False
  -}

{-
step :: R T -> T -> R T
step (Atom a)  x | a `eqT` x = Eps
step (p :+: q) x           =  label 1 (step p x) :+: label 2 (step q x)
step (p :&: q) x           =  label 1 (step p x) :&: label 2 (step q x)
step (p :>: q) x           = (label 1 (step p x) :>: q) :+: (cond (eps p) :>: label 2 (step q x))
step (Star p)  x           =  label 1 (step p x) :>: Star p
step _         x           = Nil
-}

step :: R T -> T -> R T
step (Atom a)  x | a `eqT` x = Eps
step (p :+: q) x           =  (step p x) .+. (step q x)
step (p :&: q) x           =  (step p x) .&. (step q x)
step (p :>: q) x           = ((step p x) .>. q) .+. if eps p then step q x else Nil
step (Star p)  x           =  (step p x) .>. Star p
step _         x           = Nil

rec :: R T -> [T] -> Bool
rec p []     = eps p
rec p (x:xs) = rec (step p x) xs


{-

-- 2m48s:
prop_star_plus p q s = rec (Star (p :+: q)) s === rec (Star p :+: Star q) s

prop_koen p q s = rec (p :>: q) s === rec (q :>: p) s


-- 10s:
prop_star_plus p q a b = rec (Star (p :+: q)) [a,b] === rec (Star p :+: Star q) [a,b]

--
-- prop_star_seq p q s = rec (Star (p :>: q)) s === rec (Star p :>: Star q) s
--
-- prop_switcheroo p q s = rec (p :+: q) s === rec (p :>: q) s
--
-- prop_bad_assoc p q r s = rec (p :+: (q :>: r)) s === rec ((p :+: q) :>: r) s

prop_Conj p s =
  eps p === False ==>
    rec (p :&: (p :>: p)) s === False

prop_Conj' p s =
  eps p === False ==>
    rec (p .&. (p .>. p)) s === False

-}

prop_FromToConj_difficult p i i' j j' s =
  eps p === False ==>
    rec (rep p i j :&: rep p i' j') s === rec (rep p (maxx i i') (minn j j')) s

{-
i  = Z
j  = S Z
i' = S (S Z)
j' = S (S Z)

{-
prop_FromToConj p s =
  eps p === False ==>
    rec (rep p i j .&. rep p i' j') s === rec (rep p (S (S Z)) (S (S Z)) {- (maxx i i') (minn j j') -}) s
    -}

prop_FromToConj p s =
  eps p === False ==>
    rec (rep p i j :&: rep p i' j') s === rec (rep p (maxx i i') (minn j j')) s
    -}

maxx :: Nat -> Nat -> Nat
maxx Z     b     = b
maxx (S a) Z     = S a
maxx (S a) (S b) = S (maxx a b)

minn :: Nat -> Nat -> Nat
minn Z     b     = Z
minn S{}   Z     = Z
minn (S a) (S b) = S (minn a b)

