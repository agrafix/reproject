{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
module Data.Reproject.TH
    ( deriveFieldProjections )
where

import Data.Reproject

import Control.Monad
import Language.Haskell.TH

getRecordFields :: Info -> [(String, [(Name, Strict, Type)])]
getRecordFields (TyConI (DataD _ _ _ _ cons _)) = concatMap getRF' cons
getRecordFields _ = []

getRF' :: Con -> [(String, [(Name, Strict, Type)])]
getRF' (RecC name fields) = [(nameBase name, fields)]
getRF' _ = []

-- | Derive record projections for a type. This gives you projections with the same
-- name as the field accessor
deriveFieldProjections :: Name -> Q [Dec]
deriveFieldProjections n =
    do rfs <- fmap getRecordFields $ reify n
       case rfs of
         [(_, fields)] -> concat <$> forM fields (mkSingleDecl n)
         _ -> fail "deriveFieldProjections does not support Sum types at the moment"

mkSingleDecl :: Name -> (Name, Strict, Type) -> Q [Dec]
mkSingleDecl n (name, _, ty) =
    [d|
     instance Proj $(litT (strTyLit (nameBase name))) $(pure ty) $(conT n) where
         applyProj Proxy = $(varE name)
     |]
