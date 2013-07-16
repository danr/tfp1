{-# LANGUAGE RecordWildCards,ViewPatterns #-}
module HipSpec.Translate where

import HipSpec.Theory

import qualified Lang.Rich as R

import Lang.CoreToRich
import Lang.SimplifyRich
import Lang.RichToSimple hiding (Var)
import qualified Lang.RichToSimple as S

import Lang.Simple as S
import qualified Lang.FunctionalFO as FO

import Lang.SimpleToFO as FO
import Lang.Deappify

import qualified Lang.ToPolyFOL as P

import Name
import CoreSyn

import qualified Data.Map as M
import qualified Data.Set as S

import Var

import TyCon

appThy :: Subtheory
appThy = Subtheory
    { defines = AppThy
    , clauses = P.appAxioms
    , deps    = S.empty
    }

-- | Translates the type constructors
trTyCons :: [TyCon] -> (ArityMap,[Subtheory])
trTyCons tcs = case mapM trTyCon tcs of
    Right data_types -> (con_arities,subthys)
      where
        subthys = concat
            [ [ calcDeps subtheory
                { defines = Datatype data_ty_con
                , clauses = cls
                }
              ] ++ (concat
              [ [ Subtheory
                  { defines = Definition dc
                  , clauses = []
                  , deps    = S.singleton (Datatype data_ty_con)
                  }
                , calcDeps subtheory
                  { defines = Pointer dc
                  , clauses = dc_ptr_cls
                  }
                ]
              | (dc,dc_ptr_cls) <- dc_ptr_clss
              ])
            | dt@R.Datatype{..} <- data_types
            , let (cls,dc_ptr_clss) = P.trDatatype (fmap Old dt)
            ]

        con_arities = M.fromList
            [ (Old (R.con_name dc),length (R.con_args dc))
            | dt <- data_types
            , dc <- R.data_cons dt
            ]
    Left err -> error $ "trTyCons: " ++ show err

{-
-- | Given an initial arity map (of constructors),
--   translates these binds and returns the final arity map
trBinds :: ArityMap -> [(Var,CoreExpr)] -> (ArityMap,[Subtheory])
trBinds am0 binds = (am',concat subthyss)
  where
    (amf,subthyss) = unzip (map (uncurry (trBind am')) binds)
    am' = M.unions (am0:amf)
    -}

-- | Translates Var/Expr-pairs to simple functions
toSimp :: [(Var,CoreExpr)] -> [S.Function (S.Var Name)]
toSimp = concatMap (uncurry to_simp)
  where
    to_simp v e = case trDefn v e of
        Right fn -> uncurry (:) . runRTS . rtsFun . fmap (fmap Old) $ simpFun fn
        Left err -> error $ "toSimp: " ++ show err

-- | Translates a bunch of simple functions into subtheories
trSimpFuns :: ArityMap -> [S.Function (Typed (Rename Name))] -> (ArityMap,[Subtheory])
trSimpFuns am simp_fns = (new_arities,subthys)
  where
    fo_fns :: [FO.Function (Rename Name)]
    fo_fns = map stfFun simp_fns

    new_arities :: ArityMap
    new_arities = M.fromList
        [ (fn_name,length fn_args) | FO.Function{..} <- fo_fns ]

    fo_fns_zapped :: [FO.Function (Rename Name)]
    fo_fns_zapped = mapM zapFn fo_fns (`M.lookup` am)

    subthys = concat
        [ [ calcDeps subtheory
            { defines = Definition fn_name
            , clauses = fn_cls
            }
          , calcDeps subtheory
            { defines = Pointer fn_name
            , clauses = ptr_cls
            }
          ]
        | f@FO.Function{..} <- fo_fns_zapped
        , let (fn_cls,ptr_cls) = P.trFun f
        ]

