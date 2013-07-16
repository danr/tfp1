{-# LANGUAGE ViewPatterns #-}
module HipSpec.Theory where

import Lang.RichToSimple (Rename(..),Loc(..))
import Lang.PolyFOL
import Lang.ToPolyFOL (Poly(..))
import Lang.Utils
import Unique

import Name

import Data.Set (Set)
import qualified Data.Set as S

import Data.List (sortBy)
import Data.Ord (comparing)

import Data.Map (Map)
import qualified Data.Map as M

type LogicId = Poly (Rename Name)

type ArityMap = Map (Rename Name) Int

combineArityMap :: ArityMap -> ArityMap -> ArityMap
combineArityMap = M.union

data Content
    = Definition (Rename Name)
    -- ^ Function definition, or a constructor,
    --   with no clauses and only depends on its parent data type
    | Datatype Name
    -- ^ Axioms for a data type
    | Pointer (Rename Name)
    -- ^ Pointer to some defined name
    | Lemma Int
    -- ^ A lemma
    | Conjecture
    -- ^ The conjecture
    | AppThy
    -- ^ Defines app and fn
  deriving (Eq,Ord)

data Subtheory = Subtheory
    { defines :: Content
    , clauses :: [Clause LogicId]
    , deps    :: Set Content
    }

-- | A dummy subtheory to initialise without dependencies
subtheory :: Subtheory
subtheory = Subtheory err err err
  where
    err = error "subtheory uninitialised field"

-- | Calculates and sets the dependencies for a subtheory
calcDeps :: Subtheory -> Subtheory
calcDeps s = s { deps = S.unions [datatypes,app,ptrs,defs] }
  where
    (S.toList -> ty_cons,S.toList -> fns) = clsDeps (clauses s)

    datatypes = S.fromList [ Datatype x | Id (Old x) <- ty_cons ]

    app = S.fromList $ [ AppThy | TyFn <- ty_cons ] ++ [ AppThy | App <- fns ]

    ptrs = S.fromList [ Pointer x | Ptr x <- fns ]

    defs = S.fromList . map Definition $
        [ x | Id x <- fns ] ++ [ x | Proj x _ <- fns ]

-- | Printing names
polyname :: LogicId -> String
polyname x0 = case x0 of
    Id x     -> ppRename x
    Ptr x    -> ppRename x ++ "_ptr"
    App      -> "app"
    TyFn     -> "fn"
    Proj x i -> "proj_" ++ show i ++ "_" ++ ppRename x
    QVar i   -> 'x':show i

ppName :: Name -> String
ppName nm = getOccString nm ++ '_':showOutputable (getUnique nm)

ppRename :: Rename Name -> String
ppRename (Old nm)   = ppName nm
ppRename (New ls x) = concatMap ((++ "_") . loc) ls ++ show x
  where
    loc :: Loc (Rename Name) -> String
    loc lc = case lc of
        CaseLoc   -> "case"
        LamLoc    -> "lambda"
        LetLoc nm -> ppRename nm

sortClauses :: [Clause a] -> [Clause a]
sortClauses = sortBy (comparing rank)
  where
    rank :: Clause a -> Int
    rank SortSig{} = 0
    rank TypeSig{} = 1
    rank _         = 2

