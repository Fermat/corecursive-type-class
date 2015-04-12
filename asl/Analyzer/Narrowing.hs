module Analyzer.Narrowing where
import Data.List
import Analyzer.PrettyPrint
import Text.PrettyPrint
import Analyzer.Syntax
import Analyzer.LPTM
import Control.Monad.State
import qualified Data.Set as S

quantify' :: [Rule] -> [([Term], Rule)]
quantify' [] = []
quantify' (f@(Rule cds l r):fs) =
  let vars = fv l `S.union` (S.unions $ map fv cds) `S.union` fv r in
  (S.toList vars, f) : quantify' fs 

freshRule :: ([Term], Rule) -> State Int Rule
freshRule (xs, t@(Rule cds h b)) =
  if null xs
  then return t
  else do
   newVars <- mapM (\ x -> makeName "x") xs
   let substs = zip xs (map (\ y -> Var y) newVars)
       h' = apply substs h
       b' = apply substs b
       cds' = map (apply substs) cds in
     return $ Rule cds' h' b'

-- narrowStep :: Subst -> [Term] -> [([Term], Rule)] -> Term -> State Int [(Subst, [Term], Term)]
-- instantiate rule's vars    
narrowStep s1 trs [] p = return []
narrowStep s1 trs (f1:env) p  = do
  f1' <- freshRule f1
  case unify (left f1') p of
    Nothing -> narrowStep s1 trs env p 
    Just s -> do
      let this =
            (compose s s1, map (apply s) (cond f1') ++ map (apply s) trs, apply s (right f1'))
      res <- narrowStep s1 trs env p     
      return $ this : res

--narrowing :: [([Term], Rule)] -> Subst -> [Term] -> Term -> Term -> m [(Subst, [Term], Term, Term)]
narrowing env sub rels l r =
  case match l r of
    Nothing -> do
      res <- narrowStep sub rels env r 
      helper env l res 
    Just _ -> return [(sub, rels, l, r)]      

helper env l [] = return []
helper env l ((s, rs, t):ls) = do
  a <- narrowing env s rs (apply s l) t
  b <- helper env l ls
  return $ a++b

p1 = Rule [] (App (App (Pred "P") (App (Fun "S") (Var "x"))) (Var "y")) (App (App (Pred "Q") (Var "y")) (Var "y"))

p2 = Rule [] ((App (App (Pred "Q") (Var "x")) (App (Fun "S") (Var "y")))) (App (App (Pred "P") (Var "x")) (Var "x"))

p11 = (App (App (Pred "P") (App (Fun "S") (Var "x"))) (Var "y"))
p12 = (App (App (Pred "Q") (Var "y")) (Var "y"))
q11 = ((App (App (Pred "Q") (Var "x")) (App (Fun "S") (Var "y"))))
q12 = (App (App (Pred "P") (Var "x")) (Var "x"))
--rs = quantify' [p1, p2]

p1' = Rule [] (App (App (App (Pred "f") (Var "x")) (Var "y")) (Var "z"))
      (App (App (App (Pred "g") (Var "x")) (Var "y")) (Var "z"))

p2' = Rule [] (App (App (App (Pred "g") (App (Fun "S") (Var "x"))) (Var "y")) (Var "z"))
      (App (App (App (Pred "f") (Var "z")) (App (Fun "S") (Var "y"))) (Var "z"))


runNarrowing rules rels l r = let rules' = quantify' rules in
  evalState (narrowing rules' [] rels l r) 1

test = runNarrowing [p1, p2] [] p11 p12
test' = let (s, _, l, r):[] = runNarrowing [p1, p2] [] q11 q12 in
  disp s $$ disp l <+> text "->" <+> disp r

test'' = let (s, _, l, r):[] = runNarrowing [p1', p2'] [] (left p1') (right p1') in
  disp s $$ disp l <+> text "->" <+> disp r
