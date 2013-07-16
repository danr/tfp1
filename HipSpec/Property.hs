-- | Properties, represented with the simple language
{-# LANGUAGE RecordWildCards #-}
module HipSpec.Property
    ( Literal
    , Property(..)
    , trProperty
    , trProperties
    ) where

import Control.Monad.Error

import Name

import Lang.Simple as S
import Lang.RichToSimple as S
import Lang.SimplifyRich as R
import Lang.Rich as R

import Lang.Utils

import Lang.CoreToRich

import Lang.PrettyRich as R
import Text.PrettyPrint (render,text)

import HipSpec.Translate
import HipSpec.ParseDSL
import HipSpec.Theory

import CoreSyn as C
import Var as C
import TysWiredIn (trueDataConId)

import Data.List (intercalate)

data Literal = S.Expr (S.Var Name) :=: S.Expr (S.Var Name)

showExpr :: S.Expr (S.Var Name) -> String
showExpr = render . R.ppExpr 0 (k,k) . S.injectExpr
  where
    k = text . ppRename . forget_type

instance Show Literal where
    show (e1 :=: e2) = showExpr e1 ++ " = " ++ showExpr e2

data Property = Property
    { prop_name     :: String
    -- ^ Name (e.g. prop_rotate)
    , prop_tvs      :: [Rename Name]
    -- ^ Type variables
    , prop_vars     :: [S.Var Name]
    -- ^ Quantified variables (typed)
    , prop_goal     :: Literal
    -- ^ Goal
    , prop_assums   :: [Literal]
    -- ^ Assumptions
    , prop_repr     :: String
    -- ^ Representation (e.g. rotate (len xs) xs == xs)
    , prop_var_repr :: [String]
    -- ^ Representation of variables (e.g ["xs"])
    }

instance Show Property where
    show Property{..} = concatMap (++ "\n    ")
        [ "Property"
        , "{ prop_name = " ++ prop_name
        , ", prop_tvs = " ++ comma (map ppRename prop_tvs)
        , ", prop_vars = " ++ comma (map (render . R.ppTyped (text . ppRename)) prop_vars)
        , ", prop_goal = " ++ show prop_goal
        , ", prop_assums = " ++ comma (map show prop_assums)
        , ", prop_repr = " ++ prop_repr
        , ", prop_var_repr = " ++ comma prop_var_repr
        , "}"
        ]
     where
       comma = intercalate ","

data Problem
    = CoreToRich Err
    | CannotParse CoreExpr
    | NestedAssumptions CoreExpr
    | Internal String

instance Error Problem where
    strMsg = Internal

instance Show Problem where
    show (CoreToRich err)      = show err
    show (CannotParse e)       = "Cannot parse this as a property: " ++ showOutputable e
    show (NestedAssumptions e) = "Nested assumptions: " ++ showOutputable e
    show (Internal s)          = s

trProperties
    :: ArityMap -> [(C.Var,CoreExpr)]
    -> Either Problem (ArityMap,[Property],[Subtheory])
trProperties am []           = return (am,[],[])
trProperties am ((v,e):vses) = do
    (am',p,s) <- trProperty am v e
    (am'',ps,ss) <- trProperties am' vses
    return (am'',p:ps,s++ss)

-- | Translates a property
--
-- The returned subtheories are local theories for this property
--   (e.g lifted lambdas etc as in
--      filter p (filter q xs) == filter (\ x -> p && q) xs),
-- and for this reason the ArityMap is updated, too.
trProperty :: ArityMap -> C.Var -> CoreExpr
           -> Either Problem (ArityMap,Property,[Subtheory])
trProperty am0 v e0 = do
    let (ghc_tvs,ghc_vars,e) = collectTyAndValBinders e0

        tvs = map (Old . C.varName) ghc_tvs

    vars <- either (Left . CoreToRich)
                   (Right . map (fmap Old))
                   (mapM trVar ghc_vars)

    (assums,goal) <- parseProperty e

    (goal':assums',fnss) <- mapAndUnzipM (trCoreLit vars) (goal:assums)

    let fns :: [S.Function (S.Var Name)]
        fns = concat fnss

    let amf = am0 `combineArityMap` am'
        (am',subthys) = trSimpFuns amf fns

    return
        ( amf
        , Property
            { prop_name     = varToString v
            , prop_tvs      = tvs
            , prop_vars     = vars
            , prop_goal     = goal'
            , prop_assums   = assums'
            , prop_repr     = intercalate " => " (map show (assums' ++ [goal']))
            , prop_var_repr = map varToString ghc_vars
            }
        , subthys
        )

type CoreLit = (CoreExpr,CoreExpr)

parseProperty :: CoreExpr -> Either Problem ([CoreLit],CoreLit)
parseProperty e = case C.collectArgs e of
    (C.Var x,[Type _,l,r]) | isEquals x    -> return ([],(l,r))
    (C.Var x,[l])   | isProveBool x -> return ([],(l,C.Var trueDataConId))
    (C.Var x,[Type _,b,q]) | isGivenBool x -> do
        (as,gl) <- parseProperty q
        return ((b,C.Var trueDataConId):as,gl)
    (C.Var x,[Type _,Type _,p,q]) | isGiven x     -> do
        (nested_as,a) <- parseProperty p
        unless (null nested_as) (throwError (NestedAssumptions e))
        (as,gl) <- parseProperty q
        return (a:as,gl)
    _ -> throwError (CannotParse e)

trCoreLit :: [S.Var Name] -> CoreLit ->
    Either Problem (Literal,[S.Function (S.Var Name)])
trCoreLit scope (e1,e2) = do
    (e1',fs1) <- trCoreExpr scope e1
    (e2',fs2) <- trCoreExpr scope e2
    return (e1' :=: e2',fs1++fs2)

trCoreExpr :: [S.Var Name] -> CoreExpr ->
    Either Problem (S.Expr (S.Var Name),[S.Function (S.Var Name)])
trCoreExpr scope e0 = case trExpr e0 of
    Left err -> throwError (CoreToRich err)
    Right e  -> return (runRTSWithScope scope (rtsExpr (fmap (fmap Old) e')))
      where
        e' :: R.Expr (Typed Name)
        e' = simpExpr e

