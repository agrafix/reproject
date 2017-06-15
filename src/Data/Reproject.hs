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
module Data.Reproject where

import Data.Proxy
import GHC.Exts
import GHC.TypeLits
import Labels
import Labels.Internal

data SomeType
    = SomeType
    { st_foo :: Int
    , st_bar :: Bool
    }

-- | A named projection on a type. Very similar to 'Has' but w/o a setter
class Proj (label :: Symbol) value ty | label ty -> value where
  applyProj :: Proxy label -> ty -> value

instance Proj "st_foo" Int SomeType where
    applyProj Proxy = st_foo

instance Proj "st_bar" Bool SomeType where
    applyProj Proxy = st_bar

type family Append (a :: [k]) (b :: [k]) where
    Append x '[] = x
    Append '[] x = x
    Append (x ': xs) ys = (x ': Append xs ys)

data Projection t (a :: [Symbol]) (v :: [*]) where
    Project :: (KnownSymbol a, Proj a v t) => Proxy (a :: Symbol) -> Projection t '[a] '[v]
    Combine ::
        (KnownSymbol a, Proj a v t, Cons a v (MakeTuple b w))
        => Proxy (a :: Symbol)
        -> Projection t b w
        -> Projection t (a ': b) (v ': w)

type family HasConstr (a :: [Symbol]) (v :: [*]) t :: Constraint where
    HasConstr '[] '[] t = True ~ True
    HasConstr (x ': xs) (y ': ys) t = (Proj x y t, HasConstr xs ys t)

type family MakeTuple k v where
    MakeTuple '[] '[] = ()
    MakeTuple (x ': xs) (y ': ys) = Consed x y (MakeTuple xs ys)

loadFields :: forall a v t. (HasConstr a v t) => t -> Projection t a v -> MakeTuple a v
loadFields ty pro =
    case pro of
      Project (lbl :: Proxy sym) ->
          cons (lbl := applyProj (Proxy :: Proxy sym) ty) ()
      Combine (lbl :: Proxy sym) (p2 :: Projection t b w) ->
          cons (lbl := applyProj (Proxy :: Proxy sym) ty) (loadFields ty p2)

proj :: forall a v t r. (HasConstr a v t, r ~ MakeTuple a v) => t -> Projection t a v -> r
proj = loadFields

getOne :: Projection SomeType '["st_foo"] '[Int]
getOne = Project #st_foo

getBoth :: Projection SomeType '["st_foo", "st_bar"] '[Int, Bool]
getBoth = Combine #st_foo (Project #st_bar)

demo :: SomeType
demo =
    SomeType
    { st_foo = 1
    , st_bar = True
    }

test1 = get #st_foo $ proj demo getOne
test2 = get #st_foo $ proj demo getBoth
test3 = get #st_bar $ proj demo getBoth
