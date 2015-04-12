module Loop where
import Data.List
import Syntax
import LPTM
import qualified Data.Set as S

closed :: Subst -> [Form] -> [Term] -> Bool
closed subst env queries =
  let norm = reduce env $ map (apply subst) queries
      norm' = reduce env $ map (apply subst) norm in
  S.fromList norm' `S.isSubsetOf` S.fromList norm


testCl = closed [(Var "y", (App (App (Fun "cmp") (Var "x")) (Var "y")))] [axiom] [a1]

