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
      -- * Type lifting
    , AnyProj(..), AnyRec(..)
    , runAnyProj, anyToTypedProj, anyToTypedProjM
      -- * Internal helpers
    , LblProxy(..), ReadRec(..), RecValTy, IsEqLabel, Rec(..)
    )
where

import Data.Typeable
import GHC.Exts
import GHC.OverloadedLabels
import GHC.TypeLits hiding (Nat)
import Text.Read hiding (get)

data LblProxy (t :: Symbol)
    = LblProxy
    deriving (Show, Read, Eq, Ord, Typeable)

instance l ~ l' => IsLabel (l :: Symbol) (LblProxy l') where
    fromLabel _ = LblProxy

-- | A named projection on a type. Very similar to 'Has' but w/o a setter
class Proj (label :: Symbol) ty where
    type ProjTy label ty
    applyProj :: LblProxy label -> ty -> ProjTy label ty

-- | A list of projections to be applied to a type
data Projection t (a :: [Symbol]) where
    ProjNil :: Projection t '[]
    Combine ::
        (KnownSymbol a, Proj a t)
        => LblProxy (a :: Symbol)
        -> Projection t b
        -> Projection t (a ': b)


-- | Infix alias for 'Combine'
(@@) :: (KnownSymbol a, Proj a t)
        => LblProxy (a :: Symbol)
        -> Projection t b
        -> Projection t (a ': b)
(@@) = Combine

infixr 5 @@

deriving instance Show (Projection t a)
deriving instance Eq (Projection t a)
deriving instance Typeable (Projection t a)

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

instance (Proj a t, KnownSymbol a, Read (Projection t as)) => Read (Projection t (a ': as)) where
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
type family HasProj (a :: [Symbol]) t = (r :: Constraint) where
    HasProj '[] t = 'True ~ 'True
    HasProj (x ': xs) t = (Proj x t, HasProj xs t)

data Rec t (labels :: [Symbol]) where
    RNil :: Rec t '[]
    RCons :: KnownSymbol s => LblProxy s -> ProjTy s t -> Rec t ss -> Rec t (s ': ss)


instance Eq (Rec c '[]) where
    _ == _ = True

instance (Eq (Rec t ls), Eq (ProjTy l t)) => Eq (Rec t (l ': ls)) where
    (RCons _ v vs) == (RCons _ q qs) = q == v && qs == vs

instance Show (Rec c '[]) where
    showsPrec d RNil =
        showParen (d > 10) $ showString "RNil"

instance (Show (ProjTy l t), Show (Rec t ls)) => Show (Rec t (l ': ls)) where
    showsPrec d (RCons prx v vs) =
        showParen (d > 5) $
           showsPrec 6 (symbolVal prx ++ " := " ++ show v) .
           showString " <:> " .
           showsPrec 6 vs

deriving instance Typeable Rec

loadFields :: forall t lbls. (HasProj lbls t) => t -> Projection t lbls -> Rec t lbls
loadFields ty pro =
    case pro of
      ProjNil -> RNil
      Combine (lbl :: LblProxy sym) p2 ->
          RCons lbl (applyProj (LblProxy :: LblProxy sym) ty) (loadFields ty p2)


-- | Apply all projections to a type and return them in a "Labels" compatible tuple. USe
-- 'projVal' to read single projections from it. Using OverloadedLabels is advised.
proj :: forall t lbls. (HasProj lbls t) => Projection t lbls -> t -> Rec t lbls
proj = flip loadFields


type family RecValTy label (t :: *) (lbls :: [Symbol]) where
    RecValTy label t lbls = RecValTyH label lbls (RecTys t lbls)

type family RecValTyH label (r :: [Symbol]) (v :: [*]) where
    RecValTyH label (label ': as) (t ': bs) = t
    RecValTyH label (foo ': as) (t ': bs) = RecValTyH label as bs

type family RecTys (t :: *) (lbls :: [Symbol]) :: [*] where
    RecTys t '[] = '[]
    RecTys t (a ': as) = (ProjTy a t ': RecTys t as)

type family IsEqLabel (label :: Symbol) (label2 :: Symbol) = (r :: Bool) where
    IsEqLabel l l = 'True
    IsEqLabel l l2 = 'False

class ReadRec (label :: Symbol) (eq :: Bool) r v | label r -> v where
    projVal' :: LblProxy label -> p eq -> r -> v

instance (ProjTy key t ~ v) => ReadRec label 'True (Rec t (key ': more)) v where
    projVal' _ _ (RCons _ val _ ) = val

instance
    ( RecValTy label t (key ': more) ~ v
    , ReadRec label (IsEqLabel key label) (Rec t (key ': more)) v
    ) => ReadRec label 'False (Rec t (l1 ': key ': more)) v where
    projVal' x _ (RCons _ _ (more :: Rec t (key ': more))) =
        let stop :: Proxy (IsEqLabel key label)
            stop = Proxy
        in projVal' x stop more

-- | Read a projection from a projection record
projVal ::
    forall label key more v t.
    ( ReadRec label (IsEqLabel key label) (Rec t (key ': more)) v
    ) => LblProxy label -> Rec t (key ': more) -> v
projVal l r =
    let stop :: Proxy (IsEqLabel key label)
        stop = Proxy
    in projVal' l stop r

data AnyProj t
    = forall x. (Typeable x, HasProj x t) =>
    AnyProj
    { unAnyProj :: Projection t x }

data AnyRec t
    = forall x. Typeable x =>
    AnyRec
    { unAnyRec :: Rec t x }

runAnyProj :: t -> AnyProj t -> AnyRec t
runAnyProj ty (AnyProj p) =
    AnyRec $ proj p ty

anyToTypedProj ::
    forall t (x :: [Symbol]). (HasProj x t, Typeable x, Typeable t)
    => (AnyProj t -> AnyRec t) -> Projection t x -> Rec t x
anyToTypedProj go pp =
    case go (AnyProj pp) of
      AnyRec r ->
          case cast r of
            Just (rt :: Rec t x) -> rt
            Nothing -> error "Reproject: This should never happen"

anyToTypedProjM ::
    forall m t (x :: [Symbol]). (Monad m, HasProj x t, Typeable x, Typeable t)
    => (AnyProj t -> m (AnyRec t)) -> Projection t x -> m (Rec t x)
anyToTypedProjM go pp =
    go (AnyProj pp) >>= \(AnyRec r) ->
    case cast r of
       Just (rt :: Rec t x) -> pure rt
       Nothing -> fail "Reproject: This should never happen"
