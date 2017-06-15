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
    , HasProj
    , proj, projVal
    , (@@)
      -- * Helpers
    , LblProxy(..), ReadRec(..), RecValTy, IsEqLabel, Rec(..)
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

data Rec (labels :: [Symbol]) (types :: [*]) where
    RNil :: Rec '[] '[]
    RCons :: KnownSymbol s => LblProxy s -> v -> Rec ss vs -> Rec (s ': ss) (v ': vs)

instance Eq (Rec c '[]) where
    _ == _ = True

instance (Eq v, Eq (Rec ls vs)) => Eq (Rec (l ': ls) (v ': vs)) where
    (RCons _ v vs) == (RCons _ q qs) = q == v && qs == vs

instance Show (Rec c '[]) where
    showsPrec d RNil =
        showParen (d > 10) $ showString "RNil"

instance (Show v, Show (Rec ls vs)) => Show (Rec (l ': ls) (v ': vs)) where
    showsPrec d (RCons prx v vs) =
        showParen (d > 5) $
           showsPrec 6 (symbolVal prx ++ " := " ++ show v) .
           showString " <:> " .
           showsPrec 6 vs

deriving instance Typeable Rec

type family AllHave (c :: * -> Constraint) (xs :: [*]) :: Constraint where
    AllHave c '[] = 'True ~ 'True
    AllHave c (x ': xs) = (c x, AllHave c xs)

loadFields :: forall a v t. (HasProj a v t) => t -> Projection t a v -> Rec a v
loadFields ty pro =
    case pro of
      ProjNil -> RNil
      Combine (lbl :: LblProxy sym) (p2 :: Projection t b w) ->
          RCons lbl (applyProj (LblProxy :: LblProxy sym) ty) (loadFields ty p2)

-- | Apply all projections to a type and return them in a "Labels" compatible tuple. USe
-- 'projVal' to read single projections from it. Using OverloadedLabels is advised.
proj :: forall a v t. (HasProj a v t) => Projection t a v -> t -> Rec a v
proj = flip loadFields

type family RecValTy label (r :: [Symbol]) (v :: [*]) where
    RecValTy label (label ': as) (t ': bs) = t
    RecValTy label (foo ': as) (t ': bs) = RecValTy label as bs

type family IsEqLabel (label :: Symbol) (label2 :: Symbol) = (r :: Bool) where
    IsEqLabel l l = 'True
    IsEqLabel l l2 = 'False

-- | Read a projection from a projection record
projVal ::
    forall label key r more vmore v.
    ( ReadRec label (IsEqLabel key label) (Rec (key ': more) (r ': vmore)) v
    ) => LblProxy label -> Rec (key ': more) (r ': vmore) -> v
projVal l r =
    let stop :: Proxy (IsEqLabel key label)
        stop = Proxy
    in projVal' l stop r

class ReadRec (label :: Symbol) (eq :: Bool) r v | label r -> v where
    projVal' :: LblProxy label -> p eq -> r -> v

instance (r ~ v) => ReadRec label 'True (Rec (key ': more) (r ': rs)) v where
    projVal' _ _ (RCons _ val _ ) = val

instance
    ( RecValTy label (key ': more) (r ': vmore) ~ v
    , ReadRec label (IsEqLabel key label) (Rec (key ': more) (r ': vmore)) v
    ) => ReadRec label 'False (Rec (l1 ': key ': more) (v1 ': r ': vmore)) v where
    projVal' x _ (RCons _ _ (more :: Rec (key ': more) (r ': vmore))) =
        let stop :: Proxy (IsEqLabel key label)
            stop = Proxy
        in projVal' x stop more

data LblProxy (t :: Symbol)
    = LblProxy
    deriving (Show, Read, Eq, Ord, Typeable)

instance l ~ l' => IsLabel (l :: Symbol) (LblProxy l') where
    fromLabel _ = LblProxy
