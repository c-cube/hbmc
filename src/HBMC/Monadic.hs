{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module HBMC.Monadic where

import Data.Foldable (Foldable)
import Data.Traversable (Traversable)

import Tip.Core
import Tip.Fresh
import Tip.Utils

import HBMC.Identifiers hiding (Con,Proj,Var)
import HBMC.Identifiers (Var())

import HBMC.Bool
import Tip.Passes

import Data.Generics.Geniplate

import HBMC.ToSimple

import Data.List

import Control.Monad

import Tip.Pretty
import Tip.Pretty.SMT ()

import Debug.Trace

-- Translation to constraint-generation DSL:

data Verbosity = Quiet | Verbose deriving (Eq,Ord,Show,Read)

data Func a = Func a [a] a a Bool (Mon a)
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

data Prop a = Prop [a] (Mon a)
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

data Pred a = a :=? a
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

data Guard = When | Unless
  deriving (Eq,Ord,Show)

data Rhs a
  = New Bool a
  | Call a [Simp a]
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

data BinPrim = EqualHere | NotEqualHere
  deriving (Eq,Ord,Show)

data Act a
  = Guard Guard [Pred a] (Mon a)
  | CaseData a (Simp a) a a (Mon a)
  | Simp a :>>>: a
  | a :<-: Rhs a
  | BinPrim BinPrim (Simp a) (Simp a)
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

data Simp a
  = Con a a [Simp a]
  | Proj Int a
  | Var a
  deriving (Eq,Ord,Show,Functor,Traversable,Foldable)

simpMon :: Eq a => Mon a -> Mon a
simpMon = map simpAct . collapse . filter (not . nullAct)
  where
  collapse m =
    case
      [ (l ++ [ab'] ++ m ++ r)
      | (l,a,r1) <- cursor m
      , (m,b,r)  <- cursor r1
      , Just ab' <- [collapseAct a b] ] of
      m':_ -> collapse m'
      []   -> m

simpAct :: Eq a => Act a -> Act a
simpAct (Guard g p m)         = Guard g p (simpMon m)
simpAct (CaseData tc s v c m) = CaseData tc s v c (simpMon m)
simpAct a = a

su :: (Eq a,Functor f) => a -> a -> f a -> f a
su for what = fmap (\ x -> if x == what then for else x)

nullAct :: Act a -> Bool
nullAct (CaseData _ _ _ _ m) = all nullAct m
nullAct (Guard When [] _)    = True
nullAct (Guard g p m)        = all nullAct m
nullAct _ = False

collapseAct :: Eq a => Act a -> Act a -> Maybe (Act a)
collapseAct
  (Guard When a m)
  (Guard When b n)
  | m == n = Just (Guard When (a ++ b) m)

collapseAct
  (Guard g1 a m)
  (Guard g2 b n)
  | g1 == g2 && a == b = Just (Guard g1 a (m ++ n))

collapseAct
  (CaseData tc s1 v1 c1 m1)
  (CaseData _  s2 v2 c2 m2)
  | s1 == s2 = Just (CaseData tc s1 v1 c1 (m1 ++ map (su v1 v2 . su c1 c2) m2))

collapseAct _ _ = Nothing

type Mon a = [Act a]

-- Simple termination check: there is some argument that always decreases
-- Not working for mutually recursive groups!
terminates :: Var          -- function name
           -> [Var]        -- arguments
           -> Expr Var -- body as a simple expression
           -> Bool
terminates _ [] _ = True
terminates f as e =
  or [ and [ chase a (es !! i)
           | Gbl (Global f' _ _) :@: es <- universeBi e
           , f == f' ]
     | (a,i) <- as `zip` [0..] ]
  where
  chase needle (Gbl (Global g _ _) :@: [Lcl (Local x _)])
    | Just{} <- unproj g
    = needle == x
  chase _ _ = False

trFunction :: Function Var -> Fresh (Func Var)
trFunction Function{..} =
  do r <- fresh
     let args = map lcl_name func_args
     let chk = not (terminates func_name args func_body)
     body <- trExpr func_body (Just r)
     return (Func func_name args r (tyConOf func_res) chk (simpMon body))
       {- let tt = modTyCon wrapData . trType
         in H.TySig func_name
              [ H.TyCon s [H.TyVar tv]
              | tv <- func_tvs
              , s <- [api "Equal",prelude "Ord",api "Constructive"]
              ]
              (nestedTyTup (map (tt . lcl_type) func_args)
               `TyArr` (H.TyCon (api "H") [tt func_res]))
       -}

{-
superSimple :: Expr a -> Bool
superSimple e =
  case e of
    Lcl _   -> True
    _ :@: _ -> True
    Let _ (_ :@: _) r -> superSimple r
    _ -> False
    -}

trFormula :: Formula Var -> Fresh (Prop Var)
trFormula fm =
  case fm of
    Formula r      (_:_) e -> error "trFormula, TODO: translate type variables"
    Formula Prove  []    e -> trFormula (Formula Assert [] (neg e))
    Formula Assert []    e ->
      do let (vs,e') = fmap neg (forallView (neg e))
         let cs      = conjuncts (ifToBoolOp e')
         let news    = [ x :<-: New True (tyConOf t) | Local x t <- vs ]
         asserts <- mapM trToTrue cs
         return (Prop (map lcl_name vs) (simpMon (news ++ concat asserts)))

trToTrue :: Expr Var -> Fresh (Mon Var)
trToTrue e0 =
  case e0 of
    Builtin Equal    :@: ~[e1,e2] -> tr True  e1 e2
    Builtin Distinct :@: ~[e1,e2] -> tr False e1 e2
    _                             -> tr True  e0 (booly True)
  where
  tr pol e1 e2 =
    do (lets1,s1) <- collectLets <$> toExprSimpleEnd (addBool (boolOpToIf e1))
       (lets2,s2) <- collectLets <$> toExprSimpleEnd (addBool (boolOpToIf e2))
       let equal_fn = blankGlobal
                        (api (if pol then "equalHere" else "notEqualHere"))
                        (error "trToTrue global type")
       trExpr (makeLets (lets1 ++ lets2) (Gbl equal_fn :@: [s1,s2])) Nothing

conjuncts :: Expr a -> [Expr a]
conjuncts e0 =
  case e0 of
    Builtin And :@: es                            -> concatMap conjuncts es
    Builtin Not :@: [Builtin Or :@: es]           -> concatMap conjuncts es
    Builtin Not :@: [Builtin Implies :@: [e1,e2]] -> concatMap conjuncts [e1,neg e2]
    _                                             -> [e0]

-- [[ e ]]=> r
trExpr :: Expr Var -> Maybe Var -> Fresh (Mon Var)
trExpr e00 mr =
  let (lets,rest) = collectLets e00
      (matches,fn_calls)  = partition (isMatch . snd) lets
  in  ([x :<-: New False (tyConOf t) | (Local x t,_) <- matches ] ++)
         <$> go (makeLets (fn_calls ++ matches) rest)
  where
  go e0 =
    case e0 of
      Let x (Match s brs) e ->
        (:) <$> trMatch s brs (Just (lcl_name x)) <*> go e

      Let x (Gbl (Global f _ _) :@: ss) e ->
        (lcl_name x :<-: Call f (map trSimple ss) :) <$> go e

      Match s brs -> (:[]) <$> trMatch s brs mr

      Gbl (Global (SystemCon "noop" _) _ _) :@: _ -> return []

      Gbl (Global (Api "equalHere") _ _) :@: [s1,s2] ->
        return [BinPrim EqualHere (trSimple s1) (trSimple s2)]

      Gbl (Global (Api "notEqualHere") _ _) :@: [s1,s2] ->
        return [BinPrim NotEqualHere (trSimple s1) (trSimple s2)]

      s | Just r <- mr -> return [trSimple s :>>>: r]

      _ -> error $ "trExpr " ++ ppRender e0

trMatch :: Expr Var -> [Case Var] -> Maybe Var -> Fresh (Act Var)
trMatch e brs mr | TyCon tc _ <- exprType e =
  do c <- fresh
     s <- fresh

     let ls = Local s (exprType e)

     let ctors = [ k | Case (ConPat (Global k _ _) _) _ <- brs ]

     brs' <- mapM (trCase c mr ctors . replaceProj e ls) brs

     -- waitCase e $ \ (Con c s) ->
     --   ...
     --   when (c =? K_i) $ do [[ br_i (sel s // sel e) ]]=> r
     --   ...

     return $ CaseData tc (trSimple e) c s (concat brs')

trMatch _ _ _ = error "trMatch: Not a TyCon!"

-- sel s // sel e
replaceProj :: Expr Var -> Local Var -> Case Var -> Case Var
replaceProj e s (Case p rhs) =
  Case p $ (`transformExprIn` rhs) $
    \ e0 -> case e0 of
      hd@(Gbl (Global g _ _)) :@: [e'] | e == e', Just{} <- unproj g -> hd :@: [Lcl s]

      _ -> e0

trSimple :: Expr Var -> Simp Var
trSimple s =
  case s of
    Lcl (Local x _) -> Var x
    Gbl (Global k _ _) :@: [s] | Just i <- unproj k -> Proj i (let Var x = trSimple s in x)
    Gbl (Global k (PolyType _ _ (TyCon tc _)) _) :@: ss -> Con tc k (map trSimple ss)
    _ -> error $ "trSimple, not simple: " ++ ppRender s

trCase :: Var -> Maybe Var -> [Var] -> Case Var -> Fresh (Mon Var)
trCase c mr cons (Case pat rhs) =
  do body <- trExpr rhs mr
     return $
       case body of
         [] -> []
         _  ->
           return $
             case pat of
               Default                 -> Guard Unless [c :=? k | k <- cons] body
               ConPat (Global k _ _) _ -> Guard When   [c :=? k] body

isMatch :: Expr a -> Bool
isMatch Match{} = True
isMatch _       = False

tyConOf :: Type a -> a
tyConOf (TyCon x _) = x
