{-# LANGUAGE TypeFamilies, GeneralizedNewtypeDeriving, MultiParamTypeClasses, FlexibleInstances, RankNTypes #-}
module Prolog where

import Control.Applicative
import Control.Monad
import Data.IORef
import Data.List
import qualified MiniSat as M
import MiniSat ( Solver, Lit )

--------------------------------------------------------------------------------

data Env =
  Env
  { sat   :: Solver
  , here  :: Bit
  , posts :: IORef [(Bit,H ())] -- reversed queue
  , aggr  :: Bool
  }

newtype H a = H (Env -> IO a)

instance Applicative H where
  pure  = return
  (<*>) = ap

instance Functor H where
  fmap = liftM

instance Monad H where
  return x  = H (\_   -> return x)
  H m >>= k = H (\env -> do x <- m env
                            let H m' = k x
                            m' env)

--------------------------------------------------------------------------------

run :: H a -> IO a
run (H m) =
  M.withNewSolver $ \s ->
    do ref <- newIORef []
       m (Env s tt ref True)

trySolve :: H (Maybe Bool)
trySolve =
  H $ \env -> 
    do putStrLn ("==> Try solve")
       ps <- readIORef (posts env)
       putStrLn ("Found " ++ show (length ps) ++ " points.")
       tryAll
         [ findCounterExample env ps
         , findContradiction env ps
         , findMustExpansions env ps
         , findMayExpansions env ps
         ]
 where
  tryAll []     = return Nothing
  tryAll (m:ms) = do ma <- m
                     case ma of
                       Nothing -> tryAll ms
                       Just x  -> return x

findCounterExample :: Env -> [(Bit,H())] -> IO (Maybe (Maybe Bool))
findCounterExample env ps =
  do putStrLn "Searching for real counter example..."
     b <- solveBit (sat env) (here env : [ nt b | (b, _) <- ps ])
     if b then
       do return (Just (Just True))
      else
       do return Nothing

findContradiction :: Env -> [(Bit,H())] -> IO (Maybe (Maybe Bool))
findContradiction env ps =
  do putStrLn "Searching for contradiction..."
     b <- solveBit (sat env) [here env]
     if not b then
       do return (Just (Just False))
      else
       do return Nothing

findMustExpansions :: Env -> [(Bit,H())] -> IO (Maybe (Maybe Bool))
findMustExpansions env ps =
  do putStrLn "Finding necessary expansion points..."
     vs <- find ps
     let n = length vs
     if n > 0 then
       do putStrLn ("Expanding " ++ show n ++ " necessary points...")
          writeIORef (posts env) [ p | p@(w,_) <- ps, w `notElem` vs ]
          sequence_ [ m env{ here = w } | (w,H m) <- ps, w `elem` vs ]
          return (Just Nothing)
      else
       do return Nothing
 where
  find (p@(w,H m):ps) =
    do b <- solveBit (sat env) [here env, nt w]
       if not b then
         do vs <- find ps
            return (w:vs)
        else
         do bs <- sequence [ let H m = get w in m env | (w,_) <- ps ]
            find [ p | (True, p) <- bs `zip` ps ]
  
  find [] =
    do return []

findMayExpansions :: Env -> [(Bit,H())] -> IO (Maybe (Maybe Bool))
findMayExpansions env ps =
  do putStrLn "Finding possible expansion points..."
     find 0 (map fst (reverse ps))
 where
  find thr (w:ws) =
    do b <- solveBit (sat env) [here env, w]
       if not b then
         do find (thr+1) ws
        else
         let musts w ws =
               do b <- solveBit (sat env) (here env : w : [ nt w | w <- ws ])
                  if b then
                    do return []
                   else
                    do cfl <- M.conflict (sat env)
                       let vs1 = [ w | w <- ws, w `elem` map Lit cfl || w == tt ]
                       vs2 <- musts w (filter (`notElem` vs1) ws)
                       return (vs1 ++ vs2)
          in do if thr > 0 then
                  putStrLn ("Thrown away " ++ show thr ++ " points.")
                 else
                  return ()
                putStrLn "Found point; finding friends..."
                vs <- musts w ws
                putStrLn ("Expanding " ++ show (length (w:vs)) ++ " points.")
                writeIORef (posts env) [ p | p@(l,_) <- ps, l `elem` ws, l `notElem` (w:vs) ]
                sequence_ [ m (env{ here = l }) | (l,H m) <- ps, l `elem` (w:vs) ]
                return Nothing

solve' :: H () -> H Bool
solve' h =
  do h
     mb <- trySolve
     case mb of
       Nothing -> solve' h
       Just b  -> return b

solve :: H Bool
solve = solve' (return ())

postpone :: H () -> H ()
postpone h = h

postponeReal :: H () -> H ()
postponeReal m =
  H $ \env ->
    do ps <- readIORef (posts env)
       let p = (here env, aggressive m)
       writeIORef (posts env) (p:ps)

io :: IO a -> H a
io m = H (\_ -> m)

withSolver :: (Solver -> IO a) -> H a
withSolver h = H (\env -> h (sat env))

context :: H Bit
context = H (\env -> return (here env))

inContext :: Bit -> H () -> H ()
inContext c _ | c == ff = return ()
inContext c (H m) = H (\env -> m env{ here = c })

addClauseHere :: [Bit] -> H ()
addClauseHere xs =
  do c <- context
     [c] ==> xs

impossible :: H ()
impossible = addClauseHere []

noop :: a -> H ()
noop _ = return ()

choice :: [H ()] -> H ()
choice [h] = h
choice hs =
  do xs <- sequence [ newBit | h <- hs ]
     addClauseHere xs
     a <- context
     sequence_ [ do inContext x (do addClauseHere [a]; calm h) | (x,h) <- xs `zip` hs ]

ifThenElse :: Bit -> (H (), H ()) -> H ()
ifThenElse b (yes,no) =
  choice [ do addClauseHere [b]; yes, do addClauseHere [nt b]; no ]

calm, aggressive :: H a -> H a
calm       (H h) = H (\env -> h (env{ aggr = False }))
aggressive (H h) = H (\env -> h (env{ aggr = True }))

ifAggressive :: H a -> H a -> H a
ifAggressive (H yes) (H no) =
  --H no
  H (\env -> if aggr env then yes env else no env)

--------------------------------------------------------------------------------

class Constructive a where
  new :: H a

instance Constructive () where
  new = return ()

instance Constructive Bit where
  new = newBit

instance (Constructive a, Constructive b) => Constructive (a,b) where
  new = liftM2 (,) new new

--------------------------------------------------------------------------------

class Equal a where
  equal        :: a -> a -> H Bit
  equalHere    :: a -> a -> H ()
  notEqualHere :: a -> a -> H ()

  equal x y =
    do q <- newBit
       inContext q      $ equalHere    x y
       inContext (nt q) $ notEqualHere x y
       return q

  equalHere x y =
    do q <- equal x y
       addClauseHere [q]

  notEqualHere x y =
    do q <- equal x y
       addClauseHere [nt q]

equalPred :: Equal a => a -> a -> Bit -> H ()
equalPred x y q =
  do q' <- equal x y
     equalHere q q'

instance Equal () where
  equalHere    _ _ = return ()
  notEqualHere _ _ = addClauseHere []

instance Equal Bit where
  equalHere x y
    | x == y    = return ()
    | x == nt y = addClauseHere []
    | otherwise = do addClauseHere [nt x, y]
                     addClauseHere [nt y, x]

  notEqualHere x y = equalHere x (nt y)

instance (Equal a, Equal b) => Equal (a,b) where
  equalHere (x1,x2) (y1,y2) = 
    do equalHere x1 y1
       equalHere x2 y2

  notEqualHere (x1,x2) (y1,y2) = 
    choice
    [ notEqualHere x1 y1
    , notEqualHere x2 y2
    ]

--------------------------------------------------------------------------------

class Value a where
  type Type a
  dflt :: a -> Type a
  get  :: a -> H (Type a)

instance Value () where
  type Type () = ()
  dflt _ = ()
  get  _ = return ()

instance Value a => Value [a] where
  type Type [a] = [Type a]
  dflt _ = []
  get xs = sequence [ get x | x <- xs ]

instance (Value a, Value b) => Value (a,b) where
  type Type (a,b) = (Type a, Type b)
  dflt ~(x,y) = (dflt x, dflt y)
  get   (x,y) = liftM2 (,) (get x) (get y)

instance Value Bit where
  type Type Bit = Bool
  dflt _ = False
  get (Bool b) = return b
  get (Lit x)  = do Just b <- withSolver (\s -> M.modelValue s x)
                    return b

--------------------------------------------------------------------------------

data Bit = Lit Lit | Bool Bool
 deriving ( Eq, Ord )

instance Show Bit where
  show (Bool b) = if b then "T" else "F"
  show (Lit v)  = show v

newBit :: H Bit
newBit = withSolver (\s -> Lit `fmap` M.newLit s)

ff, tt :: Bit
ff = Bool False
tt = Bool True

nt :: Bit -> Bit
nt (Bool b) = Bool (not b)
nt (Lit x)  = Lit (M.neg x)

andl, orl :: [Bit] -> H Bit
andl xs
  | ff `elem` xs = return ff
  | otherwise    = withSolver (\s -> andl' s [ x | Lit x <- xs ])
 where
  andl' s []  = do return tt
  andl' s [x] = do return (Lit x)
  andl' s xs  = do y <- M.newLit s
                   M.addClause s (y : map M.neg xs)
                   sequence_ [ M.addClause s [M.neg y, x] | x <- xs ]
                   return (Lit y)

orl xs = nt `fmap` andl (map nt xs)

addClause :: [Bit] -> H ()
addClause xs
  | tt `elem` xs = do return ()
  | otherwise    = do withSolver (\s -> M.addClause s [ x | Lit x <- xs ])
                      return ()

(==>) :: [Bit] -> [Bit] -> H ()
xs ==> ys = addClause (map nt xs ++ ys)

solveBit :: Solver -> [Bit] -> IO Bool
solveBit s xs | ff `elem` xs =
  -- should really also set the conflict clause... :-(
  do return False

solveBit s xs =
  do M.solve s [ x | Lit x <- xs ]

--------------------------------------------------------------------------------

data Thunk a = This a | Delay (IORef (Either (H ()) a))

this :: a -> Thunk a
this x = This x

delay :: H a -> H (Thunk a)
delay (H m) =
  do c <- context
     ref <- io $ newIORef undefined
     io $ writeIORef ref (Left (H (\env -> m (env{ here = c }) >>= (writeIORef ref . Right))))
     return (Delay ref)

poke :: Thunk a -> H ()
poke (This _)    = do return ()
poke (Delay ref) =
  do ema <- io $ readIORef ref
     case ema of
       Left m  -> m
       Right _ -> return ()

peek :: Thunk a -> H (Maybe a)
peek (This x)    = return (Just x)
peek (Delay ref) =
  do ema <- io $ readIORef ref
     return $ case ema of
       Left _  -> Nothing
       Right a -> Just a

force :: Thunk a -> H a
force th =
  do poke th
     Just x <- peek th
     return x

ifForce :: Thunk a -> (a -> H ()) -> H ()
ifForce (This x)       h = h x
ifForce th@(Delay ref) h =
  do ema <- io $ readIORef ref
     case ema of
       Left m  -> ifAggressive
                    (do a <- force th
                        h a)
                    (do c <- context
                        io $ writeIORef ref $ Left $
                          do m
                             Just a <- peek th
                             inContext c (h a)
                        postponeReal (poke th))
       Right a -> h a

instance Constructive a => Constructive (Thunk a) where
  new = delay new

instance Equal a => Equal (Thunk a) where
  equalHere    = zipThunk equalHere
  notEqualHere = zipThunk notEqualHere

{-
zipThunk :: (a -> b -> H ()) -> Thunk a -> Thunk b -> H ()
zipThunk f t1 t2 =
  do ma <- peek t1
     mb <- peek t2
     case (ma, mb) of
       (Just a, Just b) ->
         do f a b

       _ ->
         postpone $
           do a <- force t1
              b <- force t2
              f a b
              -}

{-
zipThunk :: (a -> b -> H ()) -> Thunk a -> Thunk b -> H ()
zipThunk f t1 t2 =
  do ma <- peek t1
     mb <- peek t2
     case (ma, mb) of
       (Nothing, Nothing) ->
         postpone $
           do a <- force t1
              b <- force t2
              f a b

       _ ->
         do a <- force t1
            b <- force t2
            f a b
    -}

zipThunk :: (a -> b -> H ()) -> Thunk a -> Thunk b -> H ()
zipThunk f t1 t2 =
  ifForce t1 $ \a ->
    ifForce t2 $ \b ->
      f a b

instance Value a => Value (Thunk a) where
  type Type (Thunk a) = Type a

  dflt x = dflt (unThunk x)
   where
    unThunk :: Thunk a -> a
    unThunk ~(This x) = x

  get (This x)    = get x
  get (Delay ref) =
    do ema <- io $ readIORef ref
       case ema of
         Left _  -> return (dflt (either undefined id ema))
         Right x -> get x

--------------------------------------------------------------------------------

newtype Val a = Val [(Bit,a)] -- sorted on a
 deriving ( Eq, Ord )

instance Show a => Show (Val a) where
  show (Val xs) = concat (intersperse "|" [ show x | (_,x) <- xs ])

val :: a -> Val a
val x = Val [(tt,x)]

(=?) :: Eq a => Val a -> a -> Bit
Val []         =? x  = ff
Val ((a,y):xs) =? x
  | x == y      = a
  | otherwise   = Val xs =? x

domain :: Val a -> [a]
domain (Val xs) = map snd xs

newVal :: Ord a => [a] -> H (Val a)
newVal xs =
  do as <- lits (length ys)
     return (Val (as `zip` ys))
 where
  ys = map head . group . sort $ xs

  lits 1 =
    do return [tt]

  lits 2 =
    do a <- newBit
       return [a,nt a]

  lits n =
    do as <- sequence [ newBit | i <- [1..n] ]
       addClause as
       atMostOne n as
       return as

  atMostOne n as | n <= 5 =
    do sequence_ [ addClause [nt x, nt y] | (x,y) <- pairs as ]
   where
    pairs (x:xs) = [ (x,y) | y <- xs ] ++ pairs xs
    pairs _      = []

  atMostOne n as =
    do a <- newBit
       atMostOne (k+1) (a : take k as)
       atMostOne (n-k+1) (nt a : drop k as)
   where
    k = n `div` 2

instance Ord a => Equal (Val a) where
  equalHere (Val xs) (Val ys) = eq xs ys
   where
    eq [] ys = sequence_ [ addClauseHere [nt y] | (y,_) <- ys ]
    eq xs [] = sequence_ [ addClauseHere [nt x] | (x,_) <- xs ]
    eq ((x,a):xs) ((y,b):ys) =
      case a `compare` b of
        LT -> do addClauseHere [nt x]
                 eq xs ((y,b):ys)
        EQ -> do addClauseHere [nt x, y]
                 eq xs ys
        GT -> do addClauseHere [nt y]
                 eq ((x,a):xs) ys
  
  notEqualHere (Val xs) (Val ys) = neq xs ys
   where
    neq [] ys = return ()
    neq xs [] = return ()
    neq ((x,a):xs) ((y,b):ys) =
      case a `compare` b of
        LT -> do neq xs ((y,b):ys)
        EQ -> do addClauseHere [nt x, nt y]
                 neq xs ys
        GT -> do neq ((x,a):xs) ys
  
instance Value (Val a) where
  type Type (Val a) = a
  
  dflt _ = error "no default value for Val" -- URK
  
  get (Val xs) =
    do bs <- sequence [ get x | (x,_) <- xs ]
       return (head [ a | (True,(_,a)) <- bs `zip` xs ])

--------------------------------------------------------------------------------

data Data c a = Con (Val c) a

con :: Ord c => c -> a -> Thunk (Data c a)
con c a = this (Con (val c) a)

unr :: a
unr = error "UNR"

isCon :: Ord c => c -> Thunk (Data c a) -> (a -> H ()) -> H ()
isCon c t h =
  ifForce t $ \(Con vc a) ->
    do let x = vc =? c
       addClauseHere [x]
       if x == ff then return () else aggressive (h a)

class (Show c, Ord c) => ConstructiveData c where
  constrs :: [c]

instance (ConstructiveData c, Constructive a) => Constructive (Data c a) where
  new = do vc <- newVal constrs
           a  <- new
           return (Con vc a)

class ConstructiveData c => EqualData c a where
  equalData :: (forall x . Equal x => x -> x -> H ()) ->
               [([c], a -> a -> H ())]

instance EqualData c a => Equal (Data c a) where
  equalHere (Con c1 x1) (Con c2 x2) =
    do equalHere c1 c2
       c <- context
       sequence_
         [ do x <- new
              sequence_ [ addClauseHere [nt (c1 =? c), x] | c <- cs ]
              inContext x (do addClauseHere [c]; calm $ f x1 x2)
         | (cs, f) <- equalData equalHere
         , any (`elem` allcs) cs
         ]
   where
    allcs = domain c1 `intersect` domain c2

  notEqualHere (Con c1 x1) (Con c2 x2) =
    choice
    [ do notEqualHere c1 c2
    , do equalHere c1 c2
         choice
           [ do addClauseHere [ c1 =? c | c <- cs ]
                f x1 x2
           | (cs, f) <- equalData notEqualHere
           , any (`elem` allcs) cs
           ]
     ]
   where
    allcs = domain c1 `intersect` domain c2

getData :: (c -> a -> H b) -> b -> Thunk (Data c a) -> H b
getData f d t =
  do md <- peek t
     case md of
       Nothing -> return d
       Just (Con c a) ->
         do x <- get c
            f x a

--------------------------------------------------------------------------------

{-
newtype List a = List (Thunk (Data L (a, List a)))
 deriving ( Constructive, Equal )
data L = Nil | Cons
 deriving ( Eq, Ord, Show )

nil       = List (con Nil unr)
cons x xs = List (con Cons (x, xs))

isNil  (List xs) h = isCon Nil  xs $ \_ -> h
isCons (List xs) h = isCon Cons xs $ \(a,as) -> h a as

instance ConstructiveData L where
  constrs = [Nil, Cons]

instance Equal a => EqualData L (a, List a) where
  equalData h = [ ([Cons], \(x,_)  (y,_)  -> h x y)
                , ([Cons], \(_,xs) (_,ys) -> postpone $ h xs ys)
                ]

instance Value a => Value (List a) where
  type Type (List a) = [Type a]
  
  dflt _ = []

  get (List t) = getData f [] t
   where
    f Nil  _ = return []
    f Cons a = do (x,xs) <- get a; return (x:xs)

--------------------------------------------------------------------------------

newtype Nat = Nat (Thunk (Data N Nat))
 deriving ( Constructive, Equal )
data N = Zero | Succ
 deriving ( Eq, Ord, Show )

nat 0 = Nat (con Zero unr)
nat i = Nat (con Succ (nat (i-1)))

isZero (Nat n) h = isCon Zero n $ \_ -> h
isSucc (Nat n) h = isCon Succ n $ \n' -> h n'

instance ConstructiveData N where
  constrs = [Zero, Succ]

instance EqualData N Nat where
  equalData h = [([Succ], \t1 t2 -> postpone $ h t1 t2)]

instance Value Nat where
  type Type Nat = Integer
  
  dflt _ = 0

  get (Nat t) = getData f 0 t
   where
    f Zero _ = return 0
    f Succ a = do n <- get a; return (n+1)

--------------------------------------------------------------------------------

newtype Tree a = Tree (Thunk (Data T (a, (Tree a, Tree a))))
 deriving ( Constructive, Equal )
data T = Empty | Node
 deriving ( Eq, Ord, Show )

empty      = Tree (con Empty unr)
node x p q = Tree (con Node (x, (p,q)))

isEmpty (Tree t) h = isCon Empty t $ \_ -> h
isNode  (Tree t) h = isCon Node  t $ \(a,(p,q)) -> h a p q

instance ConstructiveData T where
  constrs = [Empty, Node]

instance Equal a => EqualData T (a, (Tree a, Tree a)) where
  equalData h = [ ([Node], \(x,_)  (y,_)  -> h x y)
                , ([Node], \(_,pp) (_,qq) -> postpone $ h pp qq)
                ]

data Tr a = Emp | Nod a (Tr a) (Tr a) deriving ( Eq, Ord, Show )

instance Value a => Value (Tree a) where
  type Type (Tree a) = Tr (Type a)
  
  dflt _ = Emp

  get (Tree t) = getData f Emp t
   where
    f Empty _ = return Emp
    f Node  a = do (x,(p,q)) <- get a; return (Nod x p q)
-}

--------------------------------------------------------------------------------

