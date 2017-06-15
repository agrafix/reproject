{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
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
    , (@@)
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
class Proj (label :: Symbol) ty where
    type ProjVal label ty :: *
    applyProj :: Proxy label -> ty -> ProjVal label ty

data Projection t (a :: [Symbol]) where
    ProjNil :: Projection t '[]
    Combine ::
        (KnownSymbol a, Proj a t, Cons a (ProjVal a t) (MakeTuple t b))
        => Proxy (a :: Symbol)
        -> Projection t b
        -> Projection t (a ': b)

(@@) :: (KnownSymbol a, Proj a t, Cons a (ProjVal a t) (MakeTuple t b))
        => Proxy (a :: Symbol)
        -> Projection t b
        -> Projection t (a ': b)
(@@) = Combine

infixr 5 @@

deriving instance Show (Projection t v)
deriving instance Eq (Projection t v)
deriving instance Typeable (Projection t v)

instance Read (Projection t '[]) where
    readListPrec = readListPrecDefault
    readPrec =
        parens app
        where
          app =
              prec appPrec $
              do Ident "ProjNil" <- lexP
                 pure ProjNil
          appPrec = 10

instance (Proj a t, KnownSymbol a, Read (Projection t as), Cons a (ProjVal a t) (MakeTuple t as)) => Read (Projection t (a ': as)) where
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

type family HasProj (a :: [Symbol]) t :: Constraint where
    HasProj '[] t = 'True ~ 'True
    HasProj (x ': xs) t = (Proj x t, HasProj xs t)

type family MakeTuple t k where
    MakeTuple t '[] = ()
    MakeTuple t (x ': xs) = Consed x (ProjVal x t) (MakeTuple t xs)

loadFields :: forall a t. (HasProj a t) => t -> Projection t a -> MakeTuple t a
loadFields ty pro =
    case pro of
      ProjNil -> ()
      Combine (lbl :: Proxy sym) (p2 :: Projection t b) ->
          cons (lbl := applyProj (Proxy :: Proxy sym) ty) (loadFields ty p2)

proj :: forall a t r. (HasProj a t, r ~ MakeTuple t a) => Projection t a -> t -> r
proj = flip loadFields

projVal :: Has label value record => Proxy label -> record -> value
projVal = get
