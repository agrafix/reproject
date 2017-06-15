{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TemplateHaskell #-}
import Data.Reproject
import Data.Reproject.TH

import Test.Hspec

data SomeType
    = SomeType
    { st_foo :: Int
    , st_bar :: Bool
    }

$(deriveFieldProjections ''SomeType)

instance Proj "st_custom" Bool SomeType where
    applyProj LblProxy = not . st_bar

getOne :: Projection SomeType '["st_foo"] '[Int]
getOne = #st_foo @@ ProjNil

getBoth :: Projection SomeType '["st_foo", "st_bar", "st_custom"] '[Int, Bool, Bool]
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
