{-# LANGUAGE ScopedTypeVariables, FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
module HBMC.Bool where

import Tip.Core hiding (bool)

import Data.Generics.Geniplate

class Booly a where
  bool    :: a
  true    :: a
  false   :: a
  isTrue  :: a
  isFalse :: a

boolyGbl :: Booly a => Bool -> Global a
boolyGbl b = Global
  (if b then true else false)
  (PolyType [] [] (TyCon bool []))
  []

booly :: Booly a => Bool -> Expr a
booly b = Gbl (boolyGbl b) :@: []

addBool :: forall f a . (TransformBi (Type a) (f a),TransformBi (Pattern a) (f a),TransformBi (Head a) (f a),Booly a) => f a -> f a
addBool = transformBi h . transformBi f . transformBi g
  where
    f :: Head a -> Head a
    f (Builtin (Lit (Bool b))) = Gbl (boolyGbl b)
    f hd                       = hd

    g :: Pattern a -> Pattern a
    g (LitPat (Bool b))    = ConPat (boolyGbl b) []
    g pat                  = pat

    h :: Type a -> Type a
    h (BuiltinType Boolean) = TyCon bool []
    h ty                    = ty

addBoolToTheory :: Booly a => Theory a -> Theory a
addBoolToTheory Theory{..} = addBool Theory{thy_datatypes=bool_decl:thy_datatypes,..}
  where
    bool_decl = Datatype bool [] [Constructor false isFalse [],Constructor true isTrue []]
