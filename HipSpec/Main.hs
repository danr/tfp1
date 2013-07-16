-- | HipSpec 3.0
{-# LANGUAGE RecordWildCards #-}
module Main where

import HipSpec.Theory
import HipSpec.Translate
import HipSpec.Read
import HipSpec.Calls
import HipSpec.ParseDSL
import HipSpec.Property

import Lang.Unfoldings
import Lang.Escape
import Lang.FreeTyCons

import TyCon (isAlgTyCon)

import Lang.PrettyAltErgo
import Text.PrettyPrint

import System.Environment

main :: IO ()
main = do
    [file] <- getArgs

    prop_vars <- execute file

    let dsl x = not $ any ($x) [isEquals, isGiven, isGivenBool, isProveBool]

        vars = filterVarSet dsl $
               unionVarSets (map transCalls prop_vars) `minusVarSet`
               mkVarSet prop_vars

        binds = [ (v,unfolding v) | v <- varSetElems vars ]

        tcs = filter isAlgTyCon (exprsTyCons (map snd binds))

        (am,data_thy) = trTyCons tcs

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

