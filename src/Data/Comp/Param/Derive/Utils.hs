--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Derive.Utils
-- Copyright   :  (c) 2016 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines some utility functions for deriving instances
-- for functor based type classes.
--
--------------------------------------------------------------------------------
module Data.Comp.Param.Derive.Utils where

import Language.Haskell.TH

-- | Auxiliary function to extract the first and second argument of a
-- binary type application (the third argument of this function). If
-- the second argument is @Nothing@ or not of the right shape, the
-- first two arguments are returned as a default.

getBinaryFArgs :: Type -> Type -> Maybe Type -> (Type,Type)
getBinaryFArgs _ _ (Just (AppT (AppT _ t1)  t2)) = (t1, t2)
getBinaryFArgs t1 t2 _ = (t1, t2)
