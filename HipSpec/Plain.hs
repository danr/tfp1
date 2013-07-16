-- | Plain, definitional equality
{-# LANGUAGE RecordWildCards #-}
module HipSpec.Plain where

import HipSpec.Theory as T
import HipSpec.Literal
import HipSpec.Property

import Lang.PolyFOL as P
import Lang.ToPolyFOL
import Lang.Simple
import Lang.RichToSimple as S
import Lang.Type as T

plain :: ArityMap -> Property -> Subtheory
plain am prop@Property{..} = calcDepsIgnoring ignore subtheory
    { defines = T.Conjecture
    , clauses = goal_cl : sorts
    }
  where
    (expr_substs,ty_substs) = unzip
        [ (exprTySubst tv tc,tc /// tv)
        | tv <- prop_tvs
        , let tc = T.TyCon tv []
        ]

    sorts       = [ SortSig (Id tv) 0 | tv <- prop_tvs ]
    ignore      = [ Datatype tv       | S.Old tv <- prop_tvs ]

    expr_subst  = foldr (.) id expr_substs

    scope       = map forget_type prop_vars

    goal:assums = map (trLiteral am scope . mapLiteral expr_subst)
                      (prop_goal:prop_assums)

    ty_subst    = foldr (.) id ty_substs

    quants      = [ (Id x,trType (ty_subst t)) | x ::: t <- prop_vars ]

    goal_cl
        = Clause Nothing P.Conjecture (map Id prop_tvs)
        $ forAlls quants (assums ===> goal)

