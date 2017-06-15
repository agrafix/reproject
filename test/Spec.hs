{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedLabels #-}
import Data.Reproject

import Test.Hspec

data SomeType
    = SomeType
    { st_foo :: Int
    , st_bar :: Bool
    }

instance Proj "st_foo" Int SomeType where
    applyProj Proxy = st_foo

instance Proj "st_bar" Bool SomeType where
    applyProj Proxy = st_bar

instance Proj "st_custom" Bool SomeType where
    applyProj Proxy = not . st_bar

type GetOne = Projection SomeType '["st_foo"] '[Int]
type GetBoth = Projection SomeType '["st_foo", "st_bar", "st_custom"] '[Int, Bool, Bool]

getOne :: Projection SomeType '["st_foo"] '[Int]
getOne = Combine #st_foo ProjNil

getBoth :: Projection SomeType '["st_foo", "st_bar", "st_custom"] '[Int, Bool, Bool]
getBoth = Combine #st_foo (Combine #st_bar (Combine #st_custom ProjNil))

demo :: SomeType
demo =
    SomeType
    { st_foo = 1
    , st_bar = True
    }

test1 :: Int
test1 = projVal #st_foo $ proj demo getOne

test2 :: Int
test2 = projVal #st_foo $ proj demo getBoth

test3 :: Bool
test3 = projVal #st_bar $ proj demo getBoth

test4 :: Bool
test4 = projVal #st_custom $ proj demo getBoth

main :: IO ()
main = hspec $
    do it "read show matches" $
           do read (show test4) `shouldBe` test4
              read (show test1) `shouldBe` test1
       it "applies correct projection for field" $
           do test1 `shouldBe` 1
              test2 `shouldBe` 1
              test3 `shouldBe` True
       it "applies correct projection for custom projections" $
              test4 `shouldBe` False
