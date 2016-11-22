module Nat where

import Prelude hiding ((+),(*),(-),(<),id)
import Tip

data Nat = Z | S Nat

infixl 6 -
infixl 6 +
infixl 7 *

(+) :: Nat -> Nat -> Nat
S n + m = S (n + m)
Z   + m = m

(*) :: Nat -> Nat -> Nat
S n * m = m + (n * m)
Z   * m = Z

-- | Truncated subtraction
(-) :: Nat -> Nat -> Nat
S n - S m = n - m
S m - Z   = S m
Z   - Z   = Z
Z   - _   = Z

(<) :: Nat -> Nat -> Bool
Z < _     = True
--Z{} < Z   = False
--S{} < Z   = False
S n < S m = n < m

(=:=) :: Nat -> Nat -> Bool
Z   =:= Z   = True
--Z{} =:= S{} = False
--S{} =:= Z{} = False
S n =:= S m = n =:= m

id :: Nat -> Nat
id Z = Z
id (S n) = S (id n)

prop_id x = Z === id x
plus_dumb x = x + Z === x

plus_idem x = x + x === x
plus_not_idem x = x + x === x ==> True === False
plus_inf x =  S x === x
plus_ninf x =  S x === x ==> True === False

mul_idem  x = x * x === x

silly x y z = x * (y + z) === (x * y) + z

sub_assoc x y z = x - (y - z) === (x - y) - z

not_trans x y z = x < y === True ==> y < z === True ==> x < z === False

sub_comm  x y   = x - y === y - x
