module RegExp where

import HBMC

data R a
  = Nil
  | Eps
  | Atom a
  | R a :+: R a
  | R a :>: R a
  | Star (R a)
 deriving (Eq, Ord, Show)

infixl 7 .+.
infixl 8 .>.

(.+.),(.>.) :: R a -> R a -> R a
Nil .+. q   = q
p   .+. Nil = p
p   .+. q   = p :+: q

Nil .>. q   = Nil
p   .>. Nil = Nil
Eps .>. q   = q
p   .>. Eps = p
p   .>. q   = p :>: q

eps :: R a -> Bool
eps Eps       = True
eps (p :+: q) = label 1 (eps p) || label 2 (eps q)
eps (p :>: q) = label 1 (eps p) && label 2 (eps q)
eps (Star _)  = True
eps _         = False

epsR :: R a  -> R a
epsR p | eps p     = Eps
       | otherwise = Nil

data T = A | B | C
 deriving (Eq, Ord, Show)

(===) :: T -> T -> Bool
A === A = True
B === B = True
C === C = True
_ === _ = False

step :: R T -> T -> R T
step (Atom a)  x | a === x  = Eps
                 | otherwise = Nil
step (p :+: q) x =             (label 1 (step p x)) :+:       (label 2 (step q x))
step (p :>: q) x =             (label 1 (step p x) :>: q) :+: (if eps p then label 2 (step q x) else Nil)
{-
step (p :>: q) x | eps p     = (label 1 (step p x)  :>: q) :+: label 2 (step q x)
                 | otherwise =  label 1 (step p x)  :>: q
-}
step (Star p)  x =             (label 1 (step p x)) :>: Star p
step _         x = Nil

rec :: R T -> [T] -> Bool
rec p []     = eps p
rec p (x:xs) = rec (step p x) xs

-- prop_koen_easy p q a b  = rec (p :>: q) [a,b] =:= rec (q :>: p) [a,b]
--
prop_koen p q s = rec (p :>: q) s =:= rec (q :>: p) s
--
-- prop_star_plus p q s = rec (Star (p :+: q)) s =:= rec (Star p :+: Star q) s
--
-- prop_star_plus_1 p q s = rec (Star (p :+: q)) s =:= True ==> rec (Star p :+: Star q) s =:= True
-- prop_star_plus_2 p q s = rec (Star p :+: Star q) s =:= True ==> rec (Star (p :+: q)) s =:= True
--
-- prop_star_plus_easy_1 p q a b = rec (Star (p :+: q)) [a,b] =:= True ==> rec (Star p :+: Star q) [a,b] =:= True
-- prop_star_plus_easy_2 p q a b = rec (Star p :+: Star q) [a,b] =:= True ==> rec (Star (p :+: q)) [a,b] =:= True
--
-- prop_star_plus_easy p q a b = rec (Star (p :+: q)) [a,b] =:= rec (Star p :+: Star q) [a,b]
--
-- prop_star_seq p q s = rec (Star (p :>: q)) s =:= rec (Star p :>: Star q) s
--
-- prop_switcheroo p q s = rec (p :+: q) s =:= rec (p :>: q) s
--
-- prop_bad_assoc p q r s = rec (p :+: (q :>: r)) s =:= rec ((p :+: q) :>: r) s

{-
reck :: R C -> [C] -> Bool
reck Eps       []  = True
reck (Atom a)  [b] = a == b
reck (p :+: q) s   = reck p s || reck q s
reck (p :>: q) s   = reck_seq p q (splits s)
reck (Star p)  []  = True
reck (Star p)  s   | not (eps p) = rec (p :>: Star p) s
reck _ _  = False

okay :: R C -> Bool
okay (p :+: q) = okay p && okay q
okay (p :>: q) = okay p && okay q
okay (Star p)  = okay p && not (eps p)
okay _         = True

reck_seq :: R C -> R C -> [([C],[C])] -> Bool
reck_seq p q []          = False
reck_seq p q ((l,r):lrs) = if reck p l && reck q r then True else reck_seq p q lrs

splits :: [a] -> [([a],[a])]
splits []     = [([],[])]
splits (x:xs) = ([],x:xs) : splits2 x (splits xs)

splits2 :: a -> [([a],[a])] -> [([a],[a])]
splits2 x xs = [ (x:as,bs) | (as,bs) <- xs ]

prop_same p s = rec p s =:= reck p s
-}

{-
instance Arbitrary C where
  arbitrary = elements [A,B,C]
-}

{-
instance Arbitrary a => Arbitrary (R a) where
  arbitrary = sized go
    where
      go s = frequency
        [(1,return Nil)
        ,(1,return Eps)
        ,(3,Atom `fmap` arbitrary)
        ,(s,liftM2 (:+:) (go s2) (go s2))
        ,(s,liftM2 (:>:) (go s2) (go s2))
        ,(s,liftM  Star  (go s1))
        ]
        where
         s2 = s`div`2
         s1 = pred s
-}
