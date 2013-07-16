-- | Properties, represented with the simple language
{-# LANGUAGE RecordWildCards, PatternGuards #-}
module HipSpec.Property
    ( Literal(..)
    , mapLiteral
    , Property(..)
    , trProperty
    , trProperties
    ) where

import Control.Monad.Error

import Name

import Lang.Simple as S
import Lang.RichToSimple as S
import Lang.PrettyRich as R

import Text.PrettyPrint hiding (comma)

import HipSpec.ParseDSL
import HipSpec.Theory
import HipSpec.Pretty

import TysWiredIn (trueDataCon,boolTyConName)
import DataCon (dataConName)

import Data.List (intercalate)

data Literal = S.Expr TypedName' :=: S.Expr TypedName'

mapLiteral :: (S.Expr TypedName' -> S.Expr TypedName') -> Literal -> Literal
mapLiteral f (a :=: b) = f a :=: f b

instance Show Literal where
    show (e1 :=: e2) = showExpr e1 ++ " = " ++ showExpr e2

data Property = Property
    { prop_name     :: String
    -- ^ Name (e.g. prop_rotate)
    , prop_tvs      :: [Name']
    -- ^ Type variables
    , prop_vars     :: [TypedName']
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

data Err
    = CannotParse (S.Expr (S.Var Name))
    | NestedAssumptions (S.Expr (S.Var Name))
    | PropertyWithCase (S.Body (S.Var Name))
    | Internal String

instance Error Err where
    strMsg = Internal

instance Show Err where
    show err = case err of
        CannotParse e       -> "Cannot parse this as a property: " ++ showExpr e
        NestedAssumptions e -> "Nested assumptions: " ++ showExpr e
        PropertyWithCase b  -> "Property with a case: " ++ showBody b
        Internal s          -> s

trProperties :: [S.Function (S.Var Name)] -> Either Err [Property]
trProperties = mapM trProperty

-- | Translates a property that has been translated to a simple function earlier
trProperty :: S.Function (S.Var Name) -> Either Err Property
trProperty (S.Function (p ::: t) args b) = case b of
    Case{} -> throwError (PropertyWithCase b)
    Body e -> do

        let (tvs,_) = collectForalls t

        (assums,goal) <- parseProperty e

        return Property
            { prop_name     = ppRename p
            , prop_tvs      = tvs
            , prop_vars     = args
            , prop_goal     = goal
            , prop_assums   = assums
            , prop_repr     = intercalate " => " (map show (assums ++ [goal]))
            , prop_var_repr = map (ppRename . S.forget_type) args
            }

parseProperty :: S.Expr (S.Var Name) -> Either Err ([Literal],Literal)
parseProperty e = case collectArgs e of
    (Var (Old x ::: _) _,args)
        | isEquals x,    [l,r] <- args -> return ([],l :=: r)
        | isProveBool x, [l]   <- args -> return ([],l :=: true)
        | isGivenBool x, [l,q] <- args -> do
            (as,gl) <- parseProperty q
            return (((l :=: true):as),gl)
        | isGiven x,     [p,q] <- args -> do
            (nested_as,a) <- parseProperty p
            unless (null nested_as) (throwError (NestedAssumptions e))
            (as,gl) <- parseProperty q
            return (a:as,gl)
    _ -> throwError (CannotParse e)
  where
    true = Var (Old (dataConName (trueDataCon)) ::: TyCon (Old boolTyConName) []) []

