{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}
module Main where

import Control.Monad
import Control.Applicative
import Data.Ord
import qualified Data.Foldable as F
import System.Environment
import Text.PrettyPrint
import Text.Show.Pretty hiding (Name)
import Tip
import Tip.CommuteMatch
import Tip.Delambda
import Tip.Fresh
import Tip.HaskellFrontend
import Tip.Id
import Tip.Lift
import Tip.Params
import Tip.Pretty
import Tip.Simplify
import Tip.Utils.Renamer

import Control.Monad.Writer hiding ((<>))

import Data.Generics.Geniplate
import Data.Char

import TipLift
import TipMonadic
import TipTarget hiding (Expr(Lam))
-- import TipExample
import TipToSimple
import TipData
-- Main


main :: IO ()
main = do
    f:es <- getArgs
    thy <- readHaskellFile Params
      { file = f
      , include = []
      , flags = [] -- [PrintCore,PrintProps,PrintExtraIds]
      , only = es -- []
      , extra = []
      , extra_trans = [] -- es
      }
    -- putStrLn (ppRender thy)
    let remove_labels = any (== "unlabel") es

    let thy0 = straightLabel remove_labels (addBoolToTheory (renameWith disambigId thy))

    let thy1 = (simplifyExpr aggressively <=< delambda) `vifne` thy0

    putStrLn "{-"
    ppp thy1
    putStrLn "-}"

    let thy2 = commuteMatch `vifne` thy1

    let (dis,_) = unzip (map dataInfo (thy_data_decls thy2))
        di      = concat dis

    let thy3 = (removeLabelsFromTheory <=< projectPatterns di) `vifne` thy2

    putStrLn "{-"
    ppp thy3
    putStrLn "-}"

    let func_decls = [ fn | fn <- thy_func_decls thy3, Tip.func_name fn /= labelName ]

    let data_decls =
          [ d | d <- thy_data_decls thy3
              , and [ False | Tip.BuiltinType Tip.Integer :: Tip.Type Var <- universeBi d ]
              ]

    let decls = runFreshFrom (maximumOn varMax thy3) $
          do fn_decls <- mapM trFun func_decls
             dt_decls <- mapM trDatatype data_decls
             (prop_names,prop_decls) <- mapAndUnzipM trProp (thy_form_decls thy3)
             let main_decl = funDecl mainFun []
                   (mkDo [Stmt (Apply (api "run") [var p]) | p <- prop_names] Noop)
             return (Decls (concat fn_decls ++ concat dt_decls ++ prop_decls ++ [main_decl]))

    putStrLn "{-# LANGUAGE ScopedTypeVariables #-}"
    putStrLn "{-# LANGUAGE TypeFamilies #-}"
    putStrLn "{-# LANGUAGE FlexibleInstances #-}"
    putStrLn "{-# LANGUAGE MultiParamTypeClasses #-}"
    putStrLn "{-# LANGUAGE GeneralizedNewtypeDeriving #-}"
    putStrLn "import qualified Prelude"
    putStrLn "import LibHBMC"
    ppp decls

vifne :: F.Foldable f => (f Var -> Fresh a) -> f Var -> a
f `vifne` x = runFreshFrom (maximumOn varMax x) (f x)

maximumOn :: (F.Foldable f,Ord b) => (a -> b) -> f a -> b
maximumOn f = f . F.maximumBy (comparing f)

data Var
  = Var String | Refresh Var Int
  | Api String | Prelude String
  | Label | Skip | Call | Cancel | Proj Var Int | MProj Var Int
 deriving (Show,Eq,Ord)

instance Booly Var where
  true  = Var "True"
  false = Var "False"
  bool  = Var "Bool"

varMax :: Var -> Int
varMax Var{}         = 0
varMax (Refresh v i) = varMax v `max` i
varMax _             = 0

instance Interface Var where
  api     = Api
  prelude = Prelude

  proj = Proj
  unproj (Proj v i) = Just (v,i)
  unproj _          = Nothing
  mproj = MProj

  mainFun     = Var "main"

  conLabel  f = Var $ "L_" ++ ppRender f
  conRepr   f = Var $ ppRender f
  thunkRepr f = Var $ "Thunk_" ++ ppRender f
  wrapData  f = Var $ "D_" ++ ppRender f
  caseData  f = Var $ "case" ++ ppRender f
  mkCon     f = Var $ "con" ++ ppRender f

instance Pretty Var where
  pp x =
    case x of
      Var ""      -> text "x"
      Var xs      -> text (escape xs)
      Refresh v i -> pp v <> int i
      Proj x i    -> "proj" {- <> pp x <> "_" -} <> pp (i+1)
      MProj x i   -> "mproj" {- <> pp x <> "_" -} <> pp (i+1)
      Api x       -> text x
      Prelude x   -> "Prelude." <> text x
      _           -> text (show x)


isSym x = x `elem` ":!@#$%^&*\\/=?><+-"

escape :: String -> String
escape (':':xs) | all isSym xs = "(:" ++ xs ++ ")"
escape (':':xs) = 'K':escape xs
escape xs = case concatMap escChar xs of
               y:ys | not (isAlpha y) -> 'a':y:ys
               ys                     -> ys

escChar :: Char -> String
escChar x | isAlphaNum x || x == '\'' || x == '_' = [x]
          | otherwise = show (ord x)

disambigId :: Id -> [Var]
disambigId i = vs : [ Refresh vs x | x <- [0..] ]
  where
    vs = case ppId i of
           "label" -> Label
           []      -> Var "x"
           xs      -> Var xs

instance Name Var where
  fresh     = refresh (Var "")
  refresh v = Refresh v `fmap` fresh

instance Call Var where
  labelName  = Label
  skipName   = Skip
  callName   = Call
  cancelName = Cancel

straightLabel :: forall f a . (TransformBi (Expr a) (f a),Call a) => Bool -> f a -> f a
straightLabel remove_labels = transformExprIn $ \ e0 ->
  case e0 of
    (projAt -> Just (projAt -> Just (projGlobal -> Just (x,g),e1),e2))
      | x == labelName
      -> if remove_labels then e2 else g :@: [e1,e2]
    _ -> e0


projAt :: Expr a -> Maybe (Expr a,Expr a)
projAt (Builtin (At 1) :@: [a,b]) = Just (a,b)
projAt _                          = Nothing

projGlobal :: Expr a -> Maybe (a,Head a)
projGlobal (hd@(Gbl (Global x _ _ _)) :@: []) = Just (x,hd)
projGlobal _                                  = Nothing

memosAndChecks :: Theory Var -> (Theory Var,([Var],[Var]))
memosAndChecks = runWriter . transformBiM trf
 where
  trf :: Function Var -> Writer ([Var],[Var]) (Function Var)
  trf fn@Function{..} =
    case func_body of
      (projAt -> Just (projGlobal -> Just (x,_),e))
        | x == Var "memo"  -> tell ([func_name],[]) >> again
        | x == Var "check" -> tell ([],[func_name]) >> again
       where again = trf fn{func_body=e}
      _ -> return fn

-- add bool

class Booly a where
  bool  :: a
  true  :: a
  false :: a

instance Booly String where
  bool  = "Bool"
  true  = "True"
  false = "False"

addBool :: forall f a . (TransformBi (Pattern a) (f a),TransformBi (Head a) (f a),Booly a) => f a -> f a
addBool = transformBi f . transformBi g
  where
    f :: Head a -> Head a
    f (Builtin (Lit (Bool b))) = Gbl (gbl b)
    f hd                       = hd

    g :: Pattern a -> Pattern a
    g (Tip.LitPat (Bool b))    = Tip.ConPat (gbl b) []
    g pat                      = pat

    gbl b =
      Global
        (if b then true else false)
        (PolyType [] [] (Tip.TyCon bool []))
        []
        ConstructorNS

addBoolToTheory :: Booly a => Theory a -> Theory a
addBoolToTheory Theory{..} = addBool Theory{thy_data_decls=bool_decl:thy_data_decls,..}
  where
    bool_decl = Datatype bool [] [Constructor false [],Constructor true []]

-- project

projectPatterns :: Interface a => DataInfo a -> Theory a -> Fresh (Theory a)
projectPatterns di Theory{..}
  = do fns <- sequence
         [ do body <- projectExpr di func_body
              return Function{func_body=body,..}
         | Function{..} <- thy_func_decls ]
       return Theory{thy_func_decls=fns,..}

projectExpr :: Interface a => DataInfo a -> Tip.Expr a -> Fresh (Tip.Expr a)
projectExpr di = go
 where
  go e0 =
    case e0 of
      Match e alts ->
        do x <- fresh
           let lx = Local x (exprType e)
           make_let lx e =<< fmap (Match (Lcl lx))
             (sequence
               [ case pat of
                   Default -> Case Default <$> go rhs
                   Tip.ConPat k vars
                     | Just (tc,ixs) <- lookup (gbl_name k) di
                     -> do rhs' <-
                             substMany
                               [ (v,Gbl (Global
                                           (proj tc i)
                                           (PolyType [] [] (lcl_type v))
                                           [] FunctionNS)
                                    :@: [Lcl lx])
                               | (v,i) <- vars `zip` ixs
                               ]
                               rhs
                           Case (Tip.ConPat k []) <$> go rhs'
                   _ -> error $ "projectPatterns: " ++ ppShow di ++ "\n" ++ ppRender e0
               | Case pat rhs <- alts
               ])
      hd :@: args -> (hd :@:) <$> mapM go args
      Lam args e  -> Lam args <$> go e
      Let l e1 e2 -> Let l <$> go e1 <*> go e2
      Quant q l e -> Quant q l <$> go e
      Lcl l       -> return (Lcl l)

  make_let x (Lcl y) e = (Lcl y // x) e
  make_let x b       e = return (Let x b e)

-- example

pprint :: Show a => a -> IO ()
pprint = putStrLn . ppShow

ppp :: Pretty a => a -> IO ()
ppp = putStrLn . ppRender

instance Pretty String where
  pp = text

instance Call String where
  labelName  = "label"
  skipName   = "skip"
  callName   = "call"
  cancelName = "cancel"

instance Name String where
  fresh     = refresh "u"
  refresh x = fresh >>= \ i -> return (x ++ "_" ++ show (i :: Int))

{-
instance Proj String where
  proj tc i = "proj_" ++ tc ++ "_" ++ show i
  unproj ('p':'r':'o':'j':'_':s) =
    case break ('_' ==) (reverse s) of
      (i,'_':rtc) | [(n,[])] <- reads (reverse i) -> Just (reverse rtc,n)
      _ -> Nothing
  unproj _ = Nothing
-}

{-
instance Monadic String where
  memofun   f = "memo_" ++ f
  construct f = "con_" ++ f
  conLabel  f = "lbl_" ++ f
  returnH   = "return"
  newCall   = "newCall"
  new       = "new"
  waitCase  = "waitCase"
  con       = "Con"
  memcpy    = "memcpy"
  whenH     = "when"
  unlessH   = "unless"
  (=?)      = "(=?)"
-}
