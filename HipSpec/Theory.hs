{-# LANGUAGE ViewPatterns,RecordWildCards #-}
module HipSpec.Theory where

import HipSpec.Pretty

import Lang.RichToSimple (Rename(..))
import Lang.Type (Typed(..))
import Lang.PolyFOL hiding (Conjecture)
import Lang.ToPolyFOL (Poly(..))

import Name

import Data.Set (Set)
import qualified Data.Set as S

import Data.Map (Map)
import qualified Data.Map as M

type Name' = Rename Name

type TypedName' = Typed Name'

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

instance Show Content where
    show ctnt = case ctnt of
        Definition rn -> "Definition " ++ ppRename rn
        Datatype nm   -> "Datatype " ++ ppName nm
        Pointer rn    -> "Pointer " ++ ppRename rn
        Lemma i       -> "Lemma " ++ show i
        Conjecture    -> "Conjecture"
        AppThy        -> "AppThy"

data Subtheory = Subtheory
    { defines :: Content
    , clauses :: [Clause LogicId]
    , deps    :: Set Content
    }

dependencies :: Subtheory -> [Content]
dependencies = S.toList . deps

instance Show Subtheory where
    show Subtheory{..} = concatMap (++ "\n    ")
        [ "Subtheory"
        , "{ defines = " ++ show defines
        , ", clauses = " ++ ppAltErgo clauses
        , ", deps = " ++ show (S.toList deps)
        , "}"
        ]

-- | A dummy subtheory to initialise without dependencies
subtheory :: Subtheory
subtheory = Subtheory err err err
  where
    err = error "subtheory uninitialised field"

-- | Calculates and sets the dependencies for a subtheory
calcDeps :: Subtheory -> Subtheory
calcDeps = calcDepsIgnoring []

-- | Calculate depedencies, ignoring some content
calcDepsIgnoring :: [Content] -> Subtheory -> Subtheory
calcDepsIgnoring ctnt s = s
    { deps = S.unions [datatypes,app,ptrs,defs] S.\\ S.fromList ctnt }
  where
    (S.toList -> ty_cons,S.toList -> fns) = clsDeps (clauses s)

    datatypes = S.fromList [ Datatype x | Id (Old x) <- ty_cons ]

    app = S.fromList $ [ AppThy | TyFn <- ty_cons ] ++ [ AppThy | App <- fns ]

    ptrs = S.fromList [ Pointer x | Ptr x <- fns ]

    defs = S.fromList . map Definition $
        [ x | Id x <- fns ] ++ [ x | Proj x _ <- fns ]

