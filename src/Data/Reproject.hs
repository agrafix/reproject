{-# LANGUAGE FunctionalDependencies #-}
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
    , proj, projVal
    , (@@)
      -- * Helpers
    , LblProxy(..), ReadRec(..), RecValTy, IsEqLabel
    )
where

import Data.Typeable
import GHC.Exts
import GHC.OverloadedLabels
import GHC.TypeLits hiding (Nat)
import Text.Read hiding (get)

-- | A named projection on a type. Very similar to 'Has' but w/o a setter
class Proj (label :: Symbol) value ty | label ty -> value where
    applyProj :: LblProxy label -> ty -> value

-- | A list of projections to be applied to a type
data Projection t (a :: [Symbol]) (v :: [*]) where
    ProjNil :: Projection t '[] '[]
    Combine ::
        (KnownSymbol a, Proj a v t)
        => LblProxy (a :: Symbol)
        -> Projection t b w
        -> Projection t (a ': b) (v ': w)


-- | Infix alias for 'Combine'
(@@) :: (KnownSymbol a, Proj a v t)
        => LblProxy (a :: Symbol)
        -> Projection t b w
        -> Projection t (a ': b) (v ': w)
(@@) = Combine

infixr 5 @@

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

instance (Proj a b t, KnownSymbol a, Read (Projection t as bs)) => Read (Projection t (a ': as) (b ': bs)) where
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

-- | Construct a constraint that asserts that for all labels a projection for
-- type t exists
type family HasProj (a :: [Symbol]) (v :: [*]) t = (r :: Constraint) where
    HasProj '[] '[] t = 'True ~ 'True
    HasProj (x ': xs) (y ': ys) t = (Proj x y t, HasProj xs ys t)

-- | Tuple containing information about record field types
type family MakeTuple (k :: [Symbol]) (v :: [*]) = (r :: [(Symbol, *)]) | r -> k v where
    MakeTuple '[] '[] = '[]
    MakeTuple (x ': xs) (y ': ys) = ('(x, y) ': MakeTuple xs ys)

data Rec (r :: [(Symbol, *)]) where
    RNil :: Rec '[]
    RCons :: KnownSymbol s => LblProxy s -> v -> Rec xs -> Rec ('(s, v) ': xs)

loadFields :: forall a v t. HasProj a v t => t -> Projection t a v -> Rec (MakeTuple a v)
loadFields ty pro =
    case pro of
      ProjNil -> RNil
      Combine (lbl :: LblProxy sym) (p2 :: Projection t b w) ->
          RCons lbl (applyProj (LblProxy :: LblProxy sym) ty) (loadFields ty p2)

-- | Apply all projections to a type and return them in a "Labels" compatible tuple. USe
-- 'projVal' to read single projections from it. Using OverloadedLabels is advised.
proj :: forall a v t. (HasProj a v t) => Projection t a v -> t -> Rec (MakeTuple a v)
proj = flip loadFields

type family RecValTy label (r :: [(Symbol, *)]) where
    RecValTy label ('(label, t) ': as) = t
    RecValTy label ('(foo, bar) ': as) = RecValTy label as

type family IsEqLabel (label :: Symbol) (label2 :: Symbol) = (r :: Bool) where
    IsEqLabel l l = 'True
    IsEqLabel l l2 = 'False

-- | Read a projection from a projection record
projVal ::
    forall label key r more v.
    ( ReadRec label (IsEqLabel key label) (Rec ('(key, r) : more)) v
    ) => LblProxy label -> Rec ('(key, r) ': more) -> v
projVal l r =
    let stop :: Proxy (IsEqLabel key label)
        stop = Proxy
    in projVal' l stop r

class ReadRec (label :: Symbol) (eq :: Bool) r v | label r -> v where
    projVal' :: LblProxy label -> p eq -> r -> v

instance (r ~ v) => ReadRec label 'True (Rec ('(key, r) ': more)) v where
    projVal' _ _ (RCons _ val _ ) = val

instance (RecValTy label ('(key, r) ': more) ~ v, ReadRec label (IsEqLabel key label) (Rec ('(key, r) ': more)) v) => ReadRec label 'False (Rec (x ': '(key, r) ': more)) v where
    projVal' x _ (RCons _ _ (more :: Rec ('(key, r) ': more))) =
        let stop :: Proxy (IsEqLabel key label)
            stop = Proxy
        in projVal' x stop more

data LblProxy (t :: Symbol)
    = LblProxy
    deriving (Show, Read, Eq, Ord, Typeable)

instance l ~ l' => IsLabel (l :: Symbol) (LblProxy l') where
    fromLabel _ = LblProxy
