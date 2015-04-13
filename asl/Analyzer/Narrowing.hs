module Analyzer.Narrowing where
import Data.List
import Analyzer.Stable
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

-- narrowStep ::
--  Subst -> [Term] -> [([Term], Rule)] -> Term -> State Int [(Subst, [Term], Term)]
-- instantiate rule's vars
-- return a set of reachable terms
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
-- narrowing incorporated the loop detection.
-- ironically, narrowing itself will diverge in the
-- event of terminating. so we have to impose the numbers of narrowing steps
-- it can take. Now it becomes an engineering problem, which is ok.

-- Note that an engineering problem means we try to maximize the chances of success
-- , while still allowing unknown failure.
      
-- The number of steps should be the number of rules times a factor, say 3 
narrowing env sub rels l r 0 = return []
narrowing env sub rels l r n | n > 0 =
  case match l r of
    Nothing -> do
      res <- narrowStep sub rels env r 
      helper env l res (n-1)
    Just m -> return [(m, sub, rels, l, r)]      

helper env l [] n = return []
helper env l ((s, rs, t):ls) n = do
  a <- narrowing env s rs (apply s l) t n 
  b <- helper env l ls n
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

p' = Rule [] (App (Pred "Eq") (App (Fun "S") (Var "x"))) -- (App (Pred "Eq") (Var "x"))
     (App (Pred "Eq") (Var "x")) -- (App (Pred "Eq") (App (Fun "S") (Var "x")))

p'' = Rule [] (App (Pred "Eq") (Var "x"))
      (App (Pred "Eq") (App (Fun "S") (Var "x")))

-- the first Subst is matcher, second Subst is the accumulated unifier
runNarrowing :: [Rule] -> [Term] -> Term -> Term -> [(Subst, Subst, [Term], Term, Term)]
runNarrowing rules rels l r =
  let rules' = quantify' rules
      number = (length rules) * 3 -- here is the engineering part
  in
   evalState (narrowing rules' [] rels l r number) 1

test = runNarrowing [p1, p2] [] p11 p12
test' = let (_, s, _, l, r):[] = runNarrowing [p1, p2] [] q11 q12 in
  disp s $$ disp l <+> text "->" <+> disp r

test'' = let (m, s, _, l, r):[] = runNarrowing [p1', p2'] [] (left p1') (right p1') in
  disp m $$ disp l <+> text "->" <+> disp r

test3 = runNarrowing [p'', p'] [] (left p') (right p')
test4 = runNarrowing [r1] [] (left r1) (right r2) 
        -- let (s, _, l, r):[] = runNarrowing [p'', p'] [] (left p') (right p') in
  -- disp s $$ disp l <+> text "->" <+> disp r
