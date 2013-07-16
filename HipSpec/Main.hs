-- | HipSpec 3.0
{-# LANGUAGE RecordWildCards #-}
module Main where

import HipSpec.Theory
import HipSpec.Translate
import HipSpec.Read
import HipSpec.Calls
import HipSpec.ParseDSL
import HipSpec.Pretty
import HipSpec.Property

import Lang.PrettyRich as R
import Text.PrettyPrint (render,text)

import qualified Lang.Simple as S
import qualified Lang.RichToSimple as S

import Lang.Unfoldings
import Lang.RemoveDefault
import Lang.Uniquify
import Lang.Escape
import Lang.FreeTyCons

import TyCon (isAlgTyCon)

import Lang.PrettyAltErgo
import Text.PrettyPrint

import System.Environment

import UniqSupply

import Control.Monad

import Data.List (partition)

main :: IO ()
main = do
    [file] <- getArgs

    prop_vars <- execute file

    us0 <- mkSplitUniqSupply 'h'

    let dsl x = not $ any ($x) [isEquals, isGiven, isGivenBool, isProveBool]

        vars = filterVarSet dsl $
               unionVarSets (map transCalls prop_vars)

        (binds,_us1) = initUs us0 $ sequence
            [ fmap ((,) v) (runUQ . uqExpr <=< rmdExpr $ e)
            | v <- varSetElems vars
            , Just e <- [maybeUnfolding v]
            ]

        tcs = filter isAlgTyCon (exprsTyCons (map snd binds))

        (am,data_thy) = trTyCons tcs

        -- Now, split these into properties and non-properties

        simp_fns = toSimp binds

        is_prop (S.Function (_ S.::: t) _ _) =
            case res of
                S.TyCon (S.Old p) _ -> typeIsProp p
                _                   -> False

          where
            (_tvs,t')   = S.collectForalls t
            (_args,res) = S.collectArrTy t'

        (props,fns) = partition is_prop simp_fns

    putStrLn "\nDefinitions\n"
    mapM_ (putStrLn . showSimp) fns

    putStrLn "\nProperties\n"

    case trProperties props of
        Right props -> mapM_ print props
        Left err -> print err

{-

        (amf,binds_thy) = trBinds am binds

        thy = appThy : data_thy ++ binds_thy

        cls = sortClauses (concatMap clauses thy)

        pp_alt_ergo = render . vcat . map (ppClause (text . escape . polyname))

    putStrLn (pp_alt_ergo cls)

    case trProperties amf [ (v,unfolding v) | v <- prop_vars ] of
        Left err -> error (show err)
        Right (_amf',ps,ss) -> do
            putStrLn "\nProperty subtheories:"
            putStrLn (pp_alt_ergo (sortClauses (concatMap clauses ss)))

            putStrLn "\nProperties:"
            mapM_ print ps

-}
