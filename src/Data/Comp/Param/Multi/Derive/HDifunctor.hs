{-# LANGUAGE TemplateHaskell, ScopedTypeVariables #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Multi.Derive.HDifunctor
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Automatically derive instances of @HDifunctor@.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Multi.Derive.HDifunctor
    (
     HDifunctor,
     makeHDifunctor
    ) where

import Data.Comp.Derive.Utils
import Data.Comp.Param.Derive.Utils
import Data.Comp.Param.Multi.HDifunctor
import Language.Haskell.TH

{-| Derive an instance of 'HDifunctor' for a type constructor of any parametric
  kind taking at least three arguments. -}
makeHDifunctor :: Name -> Q [Dec]
makeHDifunctor fname = do
  Just (DataInfo _ name args constrs _) <- abstractNewtypeQ $ reify fname
  let args' = init args
  -- covariant argument
  let coArg :: Type = VarT $ tyVarBndrName $ last args'
  -- contravariant argument
  let conArg :: Type = VarT $ tyVarBndrName $ last $ init args'
  let argNames = map (VarT . tyVarBndrName) (init $ init args')
  let complType = foldl AppT (ConT name) argNames
  let classType = AppT (ConT ''HDifunctor) complType
  constrs' :: [(Name,[Type], Maybe Type)] <- mapM normalConExp constrs
  hdimapDecl <- funD 'hdimap (map (hdimapClause conArg coArg) constrs')
  return [mkInstanceD [] classType [hdimapDecl]]
      where hdimapClause :: Type -> Type -> (Name,[Type], Maybe Type) -> ClauseQ
            hdimapClause conArg' coArg' (constr, args, gadtTy) = do
              fn <- newName "_f"
              gn <- newName "_g"
              varNs <- newNames (length args) "x"
              let f = varE fn
              let g = varE gn
              let fp = VarP fn
              let gp = VarP gn
              -- Pattern for the constructor
              let pat = ConP constr $ map VarP varNs
              let (conArg, coArg) = getBinaryFArgs conArg' coArg' gadtTy
              body <- hdimapArgs conArg coArg f g (zip varNs args) (conE constr)
              return $ Clause [fp, gp, pat] (NormalB body) []
            hdimapArgs :: Type -> Type -> ExpQ -> ExpQ
                      -> [(Name, Type)] -> ExpQ -> ExpQ
            hdimapArgs _ _ _ _ [] acc =
                acc
            hdimapArgs conArg coArg f g ((x,tp):tps) acc =
                hdimapArgs conArg coArg f g tps
                          (acc `appE` (hdimapArg conArg coArg tp f g `appE` varE x))
            hdimapArg :: Type -> Type -> Type -> ExpQ -> ExpQ -> ExpQ
            hdimapArg conArg coArg tp f g
                | not (containsType tp conArg) &&
                  not (containsType tp coArg) = [| id |]
                | otherwise =
                    case tp of
                      AppT a _ | a == conArg -> f
                                      | a == coArg -> g
                      AppT (AppT ArrowT tp1) tp2 -> do
                          xn <- newName "x"
                          let ftp1 = hdimapArg conArg coArg tp1 f g
                          let ftp2 = hdimapArg conArg coArg tp2 f g
                          lamE [varP xn]
                               (infixE (Just ftp2)
                                       [|(.)|]
                                       (Just $ infixE (Just $ varE xn)
                                                      [|(.)|]
                                                      (Just ftp1)))
                      SigT tp' _ ->
                          hdimapArg conArg coArg tp' f g
                      _ ->
                          if containsType tp conArg then
                              [| hdimap $f $g |]
                          else
                              [| fmap $g |]
