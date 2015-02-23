{-# LANGUAGE PatternGuards #-}
module Type where

import Tip.DSL

label :: Int -> a -> a
label c x = x

data Expr = App Expr Expr Ty | Lam Expr | Var Nat

data Ty = Ty :-> Ty | A | B | C deriving Eq

infixr 9 :->
infix  4 ===

(===) :: Ty -> Ty -> Bool
A === A = True
B === B = True
C === C = True
(a :-> x) === (b :-> y) = a === b && x === y
_ === _ = False

tc :: [Ty] -> Expr -> Ty -> Bool
tc env (Var x)      t | Just tx <- env `index` x = tx === t
tc env (App f x tx) t          = label 1 (tc env f (tx :-> t)) && tc env x tx
tc env (Lam e)      (tx :-> t) = label 1 (tc (tx:env) e t)
tc _   _            _ = False

-- prop_A0 e = tc [] e ((A :-> A :-> B) :-> (B :-> C) :-> (A :-> C)) =:= False
--
-- prop_A1 e = tc [] e ((A :-> B) :-> (B :-> B :-> C) :-> (A :-> C)) =:= False
--
-- prop_A2 e = tc [] e ((A :-> A :-> B) :-> (B :-> B :-> C) :-> (A :-> C)) =:= False

prop_B e  = tc [] e ((B :-> C) :-> (A :-> B) :-> (A :-> C)) =:= False

prop_I e  = tc [] e (A :-> A) =:= False

prop_K e  = tc [] e (A :-> B :-> A) =:= False

prop_S e  = tc [] e ((A :-> B :-> C) :-> (A :-> B) :-> A :-> C) =:= False

prop_W e  = tc [] e ((A :-> A :-> B) :-> (A :-> B)) =:= False

prop_C e  = tc [] e ((A :-> B :-> C) :-> (B :-> A :-> C)) =:= False

prop_M e  = tc [] e ((A :-> B) :-> (A :-> A :-> B)) =:= False

prop_N e  = tc [] e (A :-> (A :-> A) :-> A) =:= False

prop_D e  = tc [] e ((A :-> B) :-> (A :-> B)) =:= False

prop_K1 e = tc [] e (A :-> B :-> B) =:= False


-- nats --

data Nat = S Nat | Z
  deriving Show

index :: [a] -> Nat -> Maybe a
index (x:xs) Z     = Just x
index (x:xs) (S n) = index xs n
index []     _     = Nothing

-- show --

instance Show Expr where
  show = showExpr []

showExpr env (Var v)     = case env `index` v of Just x -> x; Nothing -> "?"
showExpr env (App a b t) = "(" ++ showExpr env a ++ " " ++ showExpr env b ++ ")"
showExpr env (Lam e)     = "(\\" ++ v ++ " -> " ++ showExpr (v:env) e ++ ")"
 where
  v = head [ x | x <- vars, x `notElem` env ]
  vars = [ "x", "y", "z", "v", "w" ] ++ [ "x" ++ show i | i <- [1..] ]

