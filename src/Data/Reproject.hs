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
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE ConstraintKinds #-}
module Data.Reproject where

import Data.Proxy
import GHC.Exts
import GHC.TypeLits
import Labels

data SomeType
    = SomeType
    { st_foo :: Int
    , st_bar :: Bool
    }

instance Has "st_foo" Int SomeType where
    get Proxy = st_foo
    set Proxy val x = x { st_foo = val }

instance Has "st_bar" Bool SomeType where
    get Proxy = st_bar
    set Proxy val x = x { st_bar = val }

type family Append (a :: [k]) (b :: [k]) where
    Append x '[] = x
    Append '[] x = x
    Append (x ': xs) ys = (x ': Append xs ys)

data Projection t (a :: [Symbol]) (v :: [*]) where
    Project :: (KnownSymbol a, Has a v t) => Proxy (a :: Symbol) -> Projection t '[a] '[v]

    Combine :: (KnownSymbol a, Has a v t) => Proxy (a :: Symbol) -> Projection t b w -> Projection t (a ': b) (v ': w)

type family HasConstr (a :: [Symbol]) (v :: [*]) t :: Constraint where
    HasConstr '[] '[] t = True ~ True
    HasConstr (x ': xs) (y ': ys) t = (Has x y t, HasConstr xs ys t)


data Rec k v where
    RNil :: Rec '[] '[]
    RCons :: KnownSymbol k => Proxy k -> v -> Rec ks vs -> Rec (k ': ks) (v ': vs)

type family RecToTuple k v where
    RecToTuple '[] '[] = ()
    RecToTuple (x ': xs) (y ': ys) = (x := y, RecToTuple xs ys)

recToTuple :: Rec a v -> RecToTuple a v
recToTuple r =
    case r of
      RNil -> ()
      RCons k v r -> (k := v, recToTuple r)

loadFields :: forall a v t. (HasConstr a v t) => t -> Projection t a v -> Rec a v
loadFields ty pro =
    case pro of
      Project (lbl :: Proxy sym) ->
          RCons lbl (get (Proxy :: Proxy sym) ty) RNil
      Combine (lbl :: Proxy sym) (p2 :: Projection t b w) ->
          RCons lbl (get (Proxy :: Proxy sym) ty) (loadFields ty p2)

proj :: forall a v t r. (HasConstr a v t, r ~ RecToTuple a v) => t -> Projection t a v -> r
proj t = recToTuple . loadFields t

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
