{-# LANGUAGE TemplateHaskell, FlexibleInstances, IncoherentInstances,
  ScopedTypeVariables, UndecidableInstances, KindSignatures #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Multi.Derive.Show
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Automatically derive instances of @ShowHD@.
--
--------------------------------------------------------------------------------
module Data.Comp.Param.Multi.Derive.Show
    (
     ShowHD(..),
     makeShowHD
    ) where

import Data.Comp.Param.Derive.Utils
import Data.Comp.Derive.Utils
import Data.Comp.Param.Multi.FreshM hiding (Name)
import qualified Data.Comp.Param.Multi.FreshM as FreshM
import Data.Comp.Param.Multi.HDifunctor
import Control.Monad
import Language.Haskell.TH hiding (Cxt, match)
import qualified Data.Traversable as T

{-| Signature printing. An instance @ShowHD f@ gives rise to an instance
  @Show (Term f i)@. -}
class ShowHD f where
    showHD :: f FreshM.Name (K (FreshM String)) i -> FreshM String

newtype Dummy = Dummy String

instance Show Dummy where
  show (Dummy s) = s

{-| Derive an instance of 'ShowHD' for a type constructor of any parametric
  kind taking at least three arguments. -}
makeShowHD :: Name -> Q [Dec]
makeShowHD fname = do
  Just (DataInfo _ name args constrs _) <- abstractNewtypeQ $ reify fname
  let args' = init args
  -- covariant argument
  let coArg :: Type = VarT $ tyVarBndrName $ last args'
  -- contravariant argument
  let conArg :: Type = VarT $ tyVarBndrName $ last $ init args'
  let argNames = map (VarT . tyVarBndrName) (init $ init args')
  let complType = foldl AppT (ConT name) argNames
  let classType = AppT (ConT ''ShowHD) complType
  constrs' :: [(Name,[Type], Maybe Type)] <- mapM normalConExp constrs
  showHDDecl <- funD 'showHD (map (showHDClause conArg coArg) constrs')
  let context = map (\arg -> mkClassP ''Show [arg]) argNames
  return [mkInstanceD context classType [showHDDecl]]
      where showHDClause :: Type -> Type -> (Name,[Type], Maybe Type) -> ClauseQ
            showHDClause conArg' coArg' (constr, args, gadtTy) = do
              varXs <- newNames (length args) "x"
              -- Pattern for the constructor
              let patx = ConP constr $ map VarP varXs
              let (conArg, coArg) = getBinaryFArgs conArg' coArg' gadtTy
              body <- showHDBody (nameBase constr) conArg coArg (zip varXs args)
              return $ Clause [patx] (NormalB body) []
            showHDBody :: String -> Type -> Type -> [(Name, Type)] -> ExpQ
            showHDBody constr conArg coArg x =
                [|liftM (unwords . (constr :) .
                         map (\x -> if elem ' ' x then "(" ++ x ++ ")" else x))
                        (sequence $(listE $ map (showHDB conArg coArg) x))|]
            showHDB :: Type -> Type -> (Name, Type) -> ExpQ
            showHDB conArg coArg (x, tp)
                | not (containsType tp conArg) &&
                  not (containsType tp coArg) =
                    [| return $ show $(varE x) |]
                | otherwise =
                    case tp of
                      AppT a _ 
                          | a == coArg -> [| unK $(varE x) |]
                      AppT (AppT ArrowT (AppT a _)) _
                          | a == conArg ->
                              [| withName (\v -> do body <- (unK . $(varE x)) v
                                                    return $ "\\" ++ show v ++ " -> " ++ body) |]
                      SigT tp' _ ->
                          showHDB conArg coArg (x, tp')
                      _ ->
                          if containsType tp conArg then
                              [| showHD $(varE x) |]
                          else
                              [| liftM show $ T.mapM (liftM Dummy . unK) $(varE x) |]
