module Analyzer.Interface where
import Analyzer.Syntax
import Analyzer.Stable
import Analyzer.Narrowing
import Analyzer.PrettyPrint
import Text.PrettyPrint
import Analyzer.LPTM
import qualified Data.Set as S
import Data.List hiding(head)
import Prelude hiding(head)

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

loopCheck :: [Form] -> [Rule] -> [(Rule, Bool)]
loopCheck env [] = []
loopCheck env (a@(Rule cds l r):ls) =
  case simpLoop a of
    Nothing -> (a, False) : loopCheck env ls
    Just m -> if condLoop m env cds then (a, True):loopCheck env ls
              else (a, False) : loopCheck env ls

labelForm :: [Form] -> [(Rule, Bool)] -> [(Form, Bool)]
labelForm [] ls = []
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
                 lc = loopCheck axioms rules'
                 result = labelForm rls lc
             in result
                 
p111 = Form (App (Pred "Eq") (App (Fun "S") (Var "x"))) [(App (Pred "Eq") (Var "x"))]
p112 = Form (App (Pred "Eq") (Var "x")) [(App (Pred "Eq") (App (Fun "S") (Var "x")))]

r1' = Form (App (Pred "Eq") (App (App (Fun "Fix") (Var "F")) (Var "G"))) [t7]
r2' = Form (App (Pred "Eq") (App (App (App (Fun "Cmp") (Var "F")) (Var "G")) (Var "A")))
      [(App (Pred "Eq") (App (Var "F") (App (Var "G") (Var "A"))))]
     
r3' = Form (App (Pred "Eq") (App (App (Fun "Gs") (Var "A")) (Var "R"))) [(App (Pred "Eq") (Var "A"))]     

r4' = Form (App (Pred "Eq") (App (App (Fun "Gs") (Var "A")) (Var "R"))) [(App (Pred "Eq") (Var "R")), (App (Pred "Eq") (Var "A"))]     

r5' = Form (App (Pred "Eq") (App (Fun "Pair") (Var "A"))) [(App (Pred "Eq") (Var "A"))]

forms = text "Horn Formulas:\n" $$ (vcat $ map disp [r1', r2', r4', r5'])
testS = text "result for simple loop detection:\n" $$ vcat (map (\ (a, b) -> text "(" <> disp a <+> text "," <+> disp b <> text ")") $ stable [r1', r2', r4', r5'])  


