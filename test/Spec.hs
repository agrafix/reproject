{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}
import Data.Reproject
import Data.Reproject.TH

import Data.Typeable
import GHC.TypeLits
import Test.Hspec

data SomeType
    = SomeType
    { st_foo :: Int
    , st_bar :: Bool
    }

$(deriveFieldProjections ''SomeType)

instance Proj "st_custom" SomeType where
    type ProjTy "st_custom" SomeType = Bool
    applyProj LblProxy = not . st_bar

getOne :: Projection SomeType '["st_foo"]
getOne = #st_foo @@ ProjNil

getBoth :: Projection SomeType '["st_foo", "st_bar", "st_custom"]
getBoth = #st_foo @@ #st_bar @@ #st_custom @@ ProjNil

demo :: SomeType
demo =
    SomeType
    { st_foo = 1
    , st_bar = True
    }

test1 :: Int
test1 = projVal #st_foo $ proj getOne demo

test11 :: Int
test11 = projVal #st_foo $ proj (#st_foo @@ ProjNil) demo

test2 :: Int
test2 = projVal #st_foo $ proj getBoth demo

test3 :: Bool
test3 = projVal #st_bar $ proj getBoth demo

test4 :: Bool
test4 = projVal #st_custom $ proj getBoth demo

main :: IO ()
main = hspec $
    do it "read show matches" $
           do read (show test4) `shouldBe` test4
              read (show test1) `shouldBe` test1
       it "applies correct projection for field" $
           do test1 `shouldBe` 1
              test11 `shouldBe` 1
              test2 `shouldBe` 1
              test3 `shouldBe` True
       it "applies correct projection for custom projections" $
              test4 `shouldBe` False

class SomeClass m where
    evalRec :: (Typeable req, Typeable res) => DummyCompDef req res -> m (DummyComp req res)

instance SomeClass IO where
    evalRec (DummyCompDef f) = pure (DummyComp f)

data DummyCompDef req res
    = DummyCompDef
    { fun :: req -> res }

data DummyComp req res
    = DummyComp
    { exec :: req -> res }

data AnyProj
    = forall x. (Typeable x, HasProj x SomeType) =>
    AnyProj
    { unAnyProj :: Projection SomeType x }

data AnyRec
    = forall x. Typeable x =>
    AnyRec
    { unAnyRec :: Rec SomeType x }

dc1 :: DummyCompDef AnyProj AnyRec
dc1 = DummyCompDef $ \(AnyProj x) ->
    AnyRec $ proj x demo

proxyOf :: t -> Proxy t
proxyOf _ = Proxy

runInAny ::
    forall (x :: [Symbol]). (HasProj x SomeType, Typeable x)
    => (AnyProj -> AnyRec) -> Projection SomeType x -> Rec SomeType x
runInAny go pp =
    case go (AnyProj pp) of
      AnyRec r ->
          case cast r of
            Just (rt :: Rec SomeType x) -> rt
            Nothing -> error "OH SHIT!"

dc2 :: DummyComp AnyProj AnyRec -> DummyCompDef Int Bool
dc2 (DummyComp go) = DummyCompDef $ \_ ->
    projVal #st_bar $ runInAny go (#st_bar @@ ProjNil)

{-
    case go (AnyProj getBoth) of
      AnyRec (r :: Rec SomeType x) ->
          case cast r of
            Just (rt :: Rec SomeType '["st_foo", "st_bar", "st_custom"]) -> projVal #st_bar rt
            Nothing -> error "OH SHIT!"
-}
{-
          case eqT of
            Just (Refl :: '["st_foo", "st_bar", "st_custom"] :~: x) -> projVal #st_bar r
            Nothing -> error "OH SHIT!"
-}
fooFun :: IO ()
fooFun =
    do d1 <- evalRec dc1
       _ <- evalRec (dc2 d1)
       pure ()
