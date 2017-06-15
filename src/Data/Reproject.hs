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
    , Proxy(..)
      -- * Internal machinery
    , IsEqLabel, ReadRec, RecValTy
    )
where

import Data.Typeable
import GHC.Exts
import GHC.TypeLits hiding (Nat)
import Labels
import Text.Read hiding (get)

-- | A named projection on a type. Very similar to 'Has' but w/o a setter
class Proj (label :: Symbol) value ty | label ty -> value where
    applyProj :: Proxy label -> ty -> value

-- | A list of projections to be applied to a type
data Projection t (a :: [Symbol]) (v :: [*]) where
    ProjNil :: Projection t '[] '[]
    Combine ::
        (KnownSymbol a, Proj a v t)
        => Proxy (a :: Symbol)
        -> Projection t b w
        -> Projection t (a ': b) (v ': w)


-- | Infix alias for 'Combine'
(@@) :: (KnownSymbol a, Proj a v t)
        => Proxy (a :: Symbol)
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
type family MakeTuple (k :: [Symbol]) (v :: [*]) = (r :: *) | r -> k v where
    MakeTuple '[] '[] = ()
    MakeTuple (x ': xs) (y ': ys) = (x := y, MakeTuple xs ys)

loadFields :: forall a v t. HasProj a v t => t -> Projection t a v -> MakeTuple a v
loadFields ty pro =
    case pro of
      ProjNil -> ()
      Combine (lbl :: Proxy sym) (p2 :: Projection t b w) ->
          (lbl := applyProj (Proxy :: Proxy sym) ty, (loadFields ty p2))

-- | Apply all projections to a type and return them in a "Labels" compatible tuple. USe
-- 'projVal' to read single projections from it. Using OverloadedLabels is advised.
proj :: forall a v t. (HasProj a v t) => Projection t a v -> t -> MakeTuple a v
proj = flip loadFields

type family RecValTy label r where
    RecValTy label (label := t) = t
    RecValTy label (label := t, more) = t
    RecValTy label (label2 := t, more) = RecValTy label more

type family IsEqLabel (label :: Symbol) (label2 :: Symbol) = (r :: Bool) where
    IsEqLabel l l = 'True
    IsEqLabel l l2 = 'False

-- | Read a projection from a projection record
projVal ::
    forall label key r more v.
    ( ReadRec label (IsEqLabel key label) (key := r, more) v
    ) => Proxy label -> (key := r, more) -> v
projVal l r =
    let stop :: Proxy (IsEqLabel key label)
        stop = Proxy
    in projVal' l stop r

class ReadRec (label :: Symbol) (eq :: Bool) r v | label r -> v where
    projVal' :: Proxy label -> p eq -> r -> v

instance (r ~ v) => ReadRec label 'True (key := r, more) v where
    projVal' _ _ (_ := val, _) = val

instance (RecValTy label (key := r, more) ~ v
         , ReadRec label (IsEqLabel key label) (key := r, more) v
         ) => ReadRec label 'False (x, (key := r, more)) v where
    projVal' x _ (_, more :: (key := r, more)) =
        let stop :: Proxy (IsEqLabel key label)
            stop = Proxy
        in projVal' x stop more
