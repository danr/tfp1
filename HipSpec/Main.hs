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
import HipSpec.Plain
import HipSpec.Trim

import qualified Lang.Simple as S
import qualified Lang.RichToSimple as S

import Lang.Unfoldings
import Lang.RemoveDefault
import Lang.Uniquify
import Lang.FreeTyCons

import TyCon (isAlgTyCon)

import System.Environment

import UniqSupply

import Control.Monad

import Data.List (partition)

import System.Process

main :: IO ()
main = do
    [file] <- getArgs

    prop_vars <- execute file

    us0 <- mkSplitUniqSupply 'h'

    let not_dsl x = not $ any ($x) [isEquals, isGiven, isGivenBool, isProveBool]

        vars = filterVarSet not_dsl $
               unionVarSets (map transCalls prop_vars)

        (binds,_us1) = initUs us0 $ sequence
            [ fmap ((,) v) (runUQ . uqExpr <=< rmdExpr $ e)
            | v <- varSetElems vars
            , Just e <- [maybeUnfolding v]
            ]

        tcs = filter (\ x -> isAlgTyCon x && not (typeIsProp x))
                     (exprsTyCons (map snd binds))

        (am_tcs,data_thy) = trTyCons tcs

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

    let am_fin = am_fns `combineArityMap` am_tcs
        (am_fns,binds_thy) = trSimpFuns am_fin fns

        thy = appThy : data_thy ++ binds_thy

        trimmer = trim thy

        cls = sortClauses (concatMap clauses thy)

    putStrLn "\nDefinitions in clauses\n"
    putStrLn (ppAltErgo cls)

    putStrLn "\nProperties\n"
    case trProperties props of
        Right props' -> forM_ props' $ \ prop -> do
            print prop
            let pls = plain am_fin prop
                ss = trimmer (dependencies pls)
                goal = ppAltErgo (sortClauses (concatMap clauses (pls:ss)))
                mlw = "/tmp/goal.mlw"
            putStrLn goal
            writeFile mlw goal
            (_exc,out,err) <- readProcessWithExitCode "alt-ergo" [mlw,"-timelimit","1","-triggers-var"] ""
            putStrLn out
            putStrLn err
        Left err -> print err

