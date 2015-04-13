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
labelForm [] ls = []
labelForm (a@(Form h bs) : fs) ls =
  if helper h ls then (a, True) : labelForm fs ls
  else (a, False) : labelForm fs ls
  where helper head [] = False
        helper head ((Rule _ l r, b):ps) | alphaEq head l && b = True
                                         | otherwise = helper head ps
        
-- stable :: [Form] -> [(Form, Bool)]
stable rls = let dpPair = dpGen rls
                 rules = ruleExtension dpPair
                 axioms = axiomExtension rules
                 rules' = filtering rules
                 lc = loopCheck axioms rules' rules'
                 result = labelForm rls lc
             in axioms
                 
p111 = Form (App (Pred "Eq") (App (Fun "S") (Var "x"))) [(App (Pred "Eq") (Var "x"))]
p112 = Form (App (Pred "Eq") (Var "x")) [(App (Pred "Eq") (App (Fun "S") (Var "x")))]

r1' = Form (App (Pred "Eq") (App (App (Fun "Fix") (Var "F")) (Var "G"))) [t7]
r2' = Form (App (Pred "Eq") (App (App (App (Fun "Cmp") (Var "F")) (Var "G")) (Var "A")))
      [(App (Pred "Eq") (App (Var "F") (App (Var "G") (Var "A"))))]
     
r3' = Form (App (Pred "Eq") (App (App (Fun "Gs") (Var "A")) (Var "R"))) [(App (Pred "Eq") (Var "A"))]     

r4' = Form (App (Pred "Eq") (App (App (Fun "Gs") (Var "A")) (Var "R"))) [(App (Pred "Eq") (Var "R"))]     

r5' = Form (App (Pred "Eq") (App (Fun "Pair") (Var "A"))) [(App (Pred "Eq") (Var "A"))]
testS = stable [r1', r2', r3', r4', r5']  -- [p111, p112]


as = [Form {head = App (App (Pred "Xi") (Fun "Gs")) (App (Pred "Eq") (App (App Star (Var "A")) (Var "R"))), body = []},Form {head = App (App (Pred "Xi") (App (Fun "Gs") (Var "A"))) (App (Pred "Eq") (App Star (Var "R"))), body = []},Form {head = App (App (Pred "Xi") (Fun "Pair")) (App (Pred "Eq") (App Star (Var "A"))), body = []},Form {head = App (App (Pred "Xi") (App (App (Fun "Cmp") (Var "F")) (Var "G"))) (App (Pred "Eq") (App Star (Var "A"))), body = [App (App (Pred "Xi") (Var "F")) (App (Pred "Eq") (App Star (Var "y1"))),App (App (Pred "Xi") (Var "G")) (App (Pred "Eq") (App Star (Var "y2")))]}]

rls = [Rule {cond = [], left = App (Pred "Eq") (App (App (Fun "Gs") (Var "A")) (Var "R")), right = App (Pred "Eq") (Var "A")},Rule {cond = [], left = App (Pred "Eq") (App (App (Fun "Gs") (Var "A")) (Var "R")), right = App (Pred "Eq") (Var "R")},Rule {cond = [], left = App (Pred "Eq") (App (Fun "Pair") (Var "A")), right = App (Pred "Eq") (Var "A")},Rule {cond = [App (App (Pred "Xi") (Var "F")) (App (Pred "Eq") (App Star (Var "y1")))], left = App (Pred "Eq") (App (App (Fun "Fix") (Var "F")) (Var "G")), right = App (Pred "Eq") (App (App (Fun "Fix") (App (App (Fun "Cmp") (Var "G")) (Var "F"))) (Var "G"))},Rule {cond = [App (App (Pred "Xi") (Var "F")) (App (Pred "Eq") (App Star (Var "y1"))),App (App (Pred "Xi") (Var "G")) (App (Pred "Eq") (App Star (Var "y2")))], left = App (Pred "Eq") (App (App (App (Fun "Cmp") (Var "F")) (Var "G")) (Var "A")), right = App (Pred "Eq") (Var "A")}]

test111 = let 
              l = App (Pred "Eq") (App (App (Fun "Gs") (Var "A")) (Var "R"))
              r = App (Pred "Eq") (Var "A")
--              (m, _, cds', l', r'):xs = runNarrowing rls [] l r
              
          in loopCheck as rls rls --runNarrowing rls [] l r -- loopCheck as rls [rls !! 3]
--          disp m <+> text "\n" <+>disp l' <+> text "->" <+> disp r' <+> text "\n" <+> vcat (map disp cds')

-- loopCheck :: [Form] -> [Rule] -> [Rule] -> [(Rule, Bool)]
