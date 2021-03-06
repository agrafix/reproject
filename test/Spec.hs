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
       it "should work with the any wrappers" $
           do r <- fooFun
              r `shouldBe` True

class SomeClass m where
    evalRec :: (Typeable req, Typeable res) => DummyCompDef req res -> m (DummyComp req res)

instance SomeClass IO where
    evalRec (DummyCompDef f) = pure (DummyComp f)

data DummyCompDef req res
    = DummyCompDef
    { _fun :: req -> res }

data DummyComp req res
    = DummyComp
    { _exec :: req -> res }

dc1 :: DummyCompDef (AnyProj SomeType) (AnyRec SomeType)
dc1 = DummyCompDef $ \(AnyProj x) ->
    AnyRec $ proj x demo

dc2 :: DummyComp (AnyProj SomeType) (AnyRec SomeType) -> DummyCompDef Int Bool
dc2 (DummyComp go) = DummyCompDef $ \_ ->
    projVal #st_bar $ anyToTypedProj go (#st_bar @@ ProjNil)

fooFun :: IO Bool
fooFun =
    do d1 <- evalRec dc1
       (DummyComp d2) <- evalRec (dc2 d1)
       pure (d2 12)
