module Analyzer.Interface where
import Analyzer.Syntax
import Analyzer.Stable
import Analyzer.Narrowing
import Analyzer.PrettyPrint
import Analyzer.LPTM
import qualified Data.Set as S
import Data.List

closed :: Subst -> [Form] -> [Term] -> Maybe [Term]
closed subst env queries =
  let norm = reduce env $ map (apply subst) queries
      norm' = reduce env $ map (apply subst) norm in
  if S.fromList norm' `S.isSubsetOf` S.fromList norm then Just norm'
  else Nothing

-- to get the success substitution, modified this code.
condLoop :: Subst -> [Form] -> [Term] -> Bool
condLoop sub env qs = case closed sub env qs of
                        Nothing -> False
                        Just ns -> fst $ runLPUnif env ns 

testCl = closed [(Var "y", (App (App (Fun "cmp") (Var "x")) (Var "y")))] [axiom] [a1]

filtering :: [Rule] -> [Rule]
filtering rs = [ a | a@(Rule _ l r) <- rs, not (hasApp r)]

loopCheck :: [Form] -> [Rule] -> [Rule] -> [(Rule, Bool)]
loopCheck env rules [] = []
loopCheck env rules (a@(Rule cds l r):ls) =
  let res = runNarrowing rules cds l r
      in helper res
  where helper ress = 
          case ress of
            [] -> (a, False) : loopCheck env rules ls
            (m, _, rels, l, r):xs ->
              if condLoop m env cds then (a, True):loopCheck env rules ls
              else helper xs 

labelForm :: [Form] -> [(Rule, Bool)] -> [(Form, Bool)]
labelForm (a@(Form h bs) : fs) ls =
  if helper h ls then (a, True) : labelForm fs ls
  else (a, False) : labelForm fs ls
  where helper head [] = False
        helper head ((Rule _ l r, b):ps) | alphaEq head l && b = True
                                         | otherwise = helper head ps
        
stable :: [Form] -> [(Form, Bool)]
stable rls = let dpPair = dpGen rls
                 rules = ruleExtension dpPair
                 axioms = axiomExtension rules
                 rules' = filtering rules
                 result = labelForm rls $ loopCheck axioms rules' rules'
             in result
                 
