module Main where

import Symbolic
import MiniSat

import Control.Applicative

bruijn :: Integral i => i -> SymTerm
bruijn 0 = z
bruijn n = s (bruijn (n-1))

tnat = TApp "Nat" []
nat  = Data tnat [("Z",[]),("S",[tnat])]

texpr = TApp "Expr" []
expr  = Data texpr [ ("App2",[tnat,texpr,texpr])
                   , ("Case",[tnat,texpr,texpr])
                   , ("Cons",[texpr,texpr])
                   , ("Nil", [])
                   , ("Var", [tnat])
                   ]

z   = Con nat (val "Z") []
s x = Con nat (val "S") [(x,tnat)]

app2  f x y = Con expr (val "App2") [(f,tnat), (x,texpr), (y,texpr)]
ecase v x y = Con expr (val "Case") [(v,tnat), (x,texpr), (y,texpr)]
econs   x y = Con expr (val "Cons") [   (x,texpr), (y,texpr)]
enil        = Con expr (val "Nil")  [       ]
evar  v     = Con expr (val "Var")  [(v,tnat)      ]

type Expr = SymTerm

eval :: Solver -> List Expr -> List (List Nat) -> Expr -> IO (List Nat)
eval s p env e = do
    (arg1,(env1,arg2)) <- switch s e
        [ ("Var",  \_ [v]     -> return (UNR,(UNR,UNR)))
        , ("App2", \_ [f,x,y] -> return (The x,(The env,The y)))
        , ("Case", \b [v,n,c] -> do
            i <- index s v env
            caseList' s [b] i
                (return (The n,(The env,UNR)))
                (\ _ a as -> return (The c,(The ((a `cons` Nil) `cons` (as `cons` env)),UNR)))
          )
        , ("Cons", \_ [x,xs]  -> return (The x,(The env,The xs)))
        , ("Nil",  \_ []      -> return (UNR,(UNR,UNR)))
        ]
    f1 <- eval s p (the env1) (the arg1)
    f2 <- eval s p env (the arg2)
    switch s e
        [ ("Var",  \_ [v]     -> index s v env)
        , ("App2", \_ [f,x,y] -> eval s p (cons f1 (cons f2 Nil)) =<< index s f p)
        , ("Case", \b [v,n,c] -> return f1)
        , ("Cons", \_ [x,xs]  -> caseList s f1
            (return (cons (fromInt 0) f2))
            (\ _ y _ -> return (cons y f2))
          )
        , ("Nil",  \_ []      -> return Nil)

        ]
{-
  case e of
    Var v          -> index v env

    App2 f x y     -> let a = eval p env x
                          b = eval p env y
                       in eval p [a,b] (index f p)

    Case v nil cns -> case index v env of
                        []   -> eval p env nil
                        a:as -> eval p ([a]:as:env) cns

    Cons x xs      -> let a  = eval p env x
                          as = eval p env xs
                       in (case a of
                             []  -> 0
                             y:_ -> y) : as

    Nil            -> []
    -}

newProg :: Solver -> Int -> Int -> IO (List Expr)
newProg s e_size i = case i of
    0 -> return Nil
    _ -> do
        e <- newExpr s i e_size [0,1] [] 0
        es <- newProg s (i-1) e_size
        return (cons e es)

newBaseExpr :: Solver -> [Int] -> IO Expr
newBaseExpr s scope = choices s (enil:map (evar . bruijn) scope)

newExpr :: Solver -> Int -> Int -> [Int] -> [Int] -> Int -> IO Expr
newExpr s f size scope rec inarg = case size of
    0 -> newBaseExpr s scope
    _ -> do
        xs <- sequence $
            [ newBaseExpr s scope
            , econs <$> go <*> go
            ] ++
            -- recursive call, first argument must be one of the allowed ones:
            [ app2 (bruijn f) (evar (bruijn rec_var)) <$> go
            | rec_var <- rec
            ]
            ++
            -- case: if you case on the input argument,
            -- you may now recurse on the tail
            [ ecase (evar (bruijn v)) <$> go
                <*> go' (0:1:map (+2) scope)
                        (if v `elem` (inarg:rec)
                            then 1:map (+2) rec
                            else map (+2) rec)
                        (inarg + 2)
            | v <- scope
            ] ++
            -- non-recursive calls:
            [ app2 (bruijn g) <$> go <*> go
            | g <- [0..f-1]
            ]
        choices s xs
      where
        go' = newExpr s f (size-1)
        go  = go' scope rec inarg

index :: Symbolic a => Solver -> SymTerm -> List a -> IO a
index s i (ConsNil c x xs) =
  do addClauseBit s [nt c]
     switch s i
       [ ("Z", \_ _   -> return x)
       , ("S", \_ [j] -> index s j xs)
       ]

fromList :: Symbolic a => [a] -> List a
fromList = foldr cons Nil

fromIntList :: [Integer] -> List Nat
fromIntList = fromList . map fromInt

makeEnv :: [[Integer]] -> List (List Nat)
makeEnv = fromList . map fromIntList

main :: IO ()
main = do
    s <- newSolver
    eliminate s True

    putStrLn "Creating problem..."
    prog <- newProg s 2 10

    let a === b = equal s (fromIntList a) =<< eval s prog (makeEnv [b,[]])
                                                          (app2 (bruijn 0) (evar (bruijn 0)) (evar (bruijn 1)))

    fact_1 <- [1,2,3,4] === reverse [1,2,3,4]

    addClauseBit s [fact_1]

    putStrLn "Solving..."
    b <- solve s []
    if b then
      do putStrLn "Solution!"
         print =<< get s prog
     else
      do putStrLn "No solution."

    deleteSolver s

{-
prog =
  [ App (S Z) [Var Z, Nil]
  , Case Z (Var (S Z)) (App (S Z) [Var (S Z), Cons (Var Z) (Var (S (S (S Z))))])
  ]
-}

{-
data Expr
  = App Int [Expr]
  | Case Int Expr Expr
  | Cons Expr Expr
  | Nil
  | Var Int
 deriving ( Eq, Ord, Show )

showExpr :: [String] -> [String] -> Expr -> String
showExpr prg env (App f xs) =
  index f prg ++ "(" ++ concat (L.intersperse "," (map (showExpr prg env) xs)) ++ ")"

showExpr prg env (Case v nil cns) =
  "case " ++ index v env ++ " of { [] -> " ++ showExpr prg env nil
          ++ "; " ++ x ++ ":" ++ xs ++ " -> " ++ showExpr prg (x:xs:env) cns ++ " }"
 where
  x:xs:_ = new env

showExpr prg env (Cons a as) =
  "(" ++ showExpr prg env a ++ ":" ++ showExpr prg env as ++ ")"

showExpr prg env Nil =
  "[]"

showExpr prg env (Var v) =
  index v env

new :: [String] -> [String]
new vs = (["x","y","z","v","w","p","q","r"] ++ ["x" ++ show i | i <- [1..] ]) L.\\ L.nub vs

showProg :: Program -> String
showProg prg = unlines
  [ f ++ " = " ++ showExpr fs env e
  | (f,e) <- fs `zip` prg
  ]
 where
  fs  = ["f" ++ show i | i <- [1..] ]
  env = ["a" ++ show i | i <- [1..10] ]

-}

--------------------------------------------------------------------------------


