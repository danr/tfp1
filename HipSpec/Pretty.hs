module HipSpec.Pretty where

import HipSpec.Theory

import Text.PrettyPrint

import qualified Lang.Simple as S
import qualified Lang.PrettyRich as R
import qualified Lang.PrettyUtils as P

import Lang.ToPolyFOL (Poly(..))

import Lang.RichToSimple (Rename(..),Loc(..))
import qualified Lang.RichToSimple as S

import Name
import Unique
import Lang.Utils

simpKit :: P.Kit (S.Var Name)
simpKit = let k = text . ppRename . S.forget_type in (k,k)

showSimp :: S.Function (S.Var Name) -> String
showSimp = render . R.ppFun simpKit . S.injectFn

showExpr :: S.Expr (S.Var Name) -> String
showExpr = render . R.ppExpr 0 simpKit . S.injectExpr

showBody :: S.Body (S.Var Name) -> String
showBody = render . R.ppExpr 0 simpKit . S.injectBody

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
