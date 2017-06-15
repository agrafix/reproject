{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE ConstraintKinds #-}
module Data.Reproject
    ( Proj(..)
    , Projection(..)
    , HasProj, MakeTuple
    , proj, Proxy(..), projVal
    )
where

import Data.Proxy
import Data.Typeable
import GHC.Exts
import GHC.TypeLits
import Labels
import Labels.Internal
import Text.Read hiding (get)

-- | A named projection on a type. Very similar to 'Has' but w/o a setter
class Proj (label :: Symbol) value ty | label ty -> value where
  applyProj :: Proxy label -> ty -> value

data Projection t (a :: [Symbol]) (v :: [*]) where
    ProjNil :: Projection t '[] '[]
    Combine ::
        (KnownSymbol a, Proj a v t, Cons a v (MakeTuple b w))
        => Proxy (a :: Symbol)
        -> Projection t b w
        -> Projection t (a ': b) (v ': w)

deriving instance Show (Projection t a v)
deriving instance Eq (Projection t a v)
deriving instance Typeable (Projection t a v)

instance Read (Projection t '[] '[]) where
    readListPrec = readListPrecDefault
    readPrec =
        parens app
        where
          app =
              prec appPrec $
              do Ident "ProjNil" <- lexP
                 pure ProjNil
          appPrec = 10

instance (Proj a b t, KnownSymbol a, Read (Projection t as bs), Cons a b (MakeTuple as bs)) => Read (Projection t (a ': as) (b ': bs)) where
    readListPrec = readListPrecDefault
    readPrec =
        parens app
        where
          app =
              prec upPrec $
              do Ident "Combine" <- lexP
                 prxy <- step readPrec
                 more <- step readPrec
                 pure (Combine prxy more)
          upPrec = 5

type family HasProj (a :: [Symbol]) (v :: [*]) t :: Constraint where
    HasProj '[] '[] t = 'True ~ 'True
    HasProj (x ': xs) (y ': ys) t = (Proj x y t, HasProj xs ys t)

type family MakeTuple k v where
    MakeTuple '[] '[] = ()
    MakeTuple (x ': xs) (y ': ys) = Consed x y (MakeTuple xs ys)

loadFields :: forall a v t. (HasProj a v t) => t -> Projection t a v -> MakeTuple a v
loadFields ty pro =
    case pro of
      ProjNil -> ()
      Combine (lbl :: Proxy sym) (p2 :: Projection t b w) ->
          cons (lbl := applyProj (Proxy :: Proxy sym) ty) (loadFields ty p2)

proj :: forall a v t r. (HasProj a v t, r ~ MakeTuple a v) => t -> Projection t a v -> r
proj = loadFields

projVal :: Has label value record => Proxy label -> record -> value
projVal = get
