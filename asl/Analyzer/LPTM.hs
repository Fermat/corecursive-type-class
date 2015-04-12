module Analyzer.LPTM where
import Prelude hiding(head)
import Analyzer.Syntax
import Analyzer.Stable
import Analyzer.PrettyPrint
import Text.PrettyPrint
import qualified Data.Set as S
import Control.Monad.State
import Control.Monad.Identity

step :: [Form] -> Term -> Maybe [Term]
step [] p = Nothing
step (f1:env) p = case match (head f1) p of
                    Nothing -> step env p
                    Just s -> Just $ map (apply s) (body f1)

-- reduce can be diverge.
reduce :: [Form] -> [Term] -> [Term]
reduce env [] = []
reduce env (p:ps) = case step env p of
                       Just ns -> reduce env (ps++ns)
                       Nothing -> let res = reduce env ps in p:res
a1 = App (Pred "eq") (App (App (Fun "cmp") (Var "x")) (Var "y"))
a2 = App (Pred "eq") (Var "y")
a3 = App (Pred "eq") (Var "x")
axiom = Form a1 [a2, a3]

type Unif a = StateT Int (StateT Subst Identity) a

reorder :: [Form] -> [Form] -> [Form] -> [Form]
reorder [] empty nonempty = empty ++ nonempty
reorder ((f@(Form h [])):fs) empty nonempty = reorder fs (f:empty) nonempty
reorder ((f@(Form h (b:bs))):fs) empty nonempty = reorder fs empty (f:nonempty)  


quantify :: [Form] -> [([Term], Form)]
quantify [] = []
quantify (f@(Form h b):fs) =
  let vars = fv h `S.union` (S.unions $ map fv b) in
  (S.toList vars, f) : quantify fs 

freshInst :: ([Term], Form) -> Unif Form
freshInst (xs, t@(Form h b)) =
  if null xs
  then return t
  else do
   newVars <- mapM (\ x -> makeName "x") xs
   let substs = zip xs (map (\ y -> Var y) newVars)
       h' = apply substs h
       b' = map (apply substs) b in
     return $ Form h' b'

-- side-effects: generating fresh vars, updating substitution
unifStep :: [([Term],Form)] -> Term -> Unif (Maybe ([Term], Subst))
unifStep [] p = return Nothing -- can't reduce a query any more
unifStep (f1:env) p = do
  f1' <- freshInst f1
  case unify (head f1') p of
    Nothing -> unifStep env p
    Just s -> do
      lift $ modify (compose s)
      return $ Just (map (apply s) (body f1'), s)


-- lpUnif can be diverging. 
-- Here I assume a lemma: if s is not unifiable with t, then
-- for any substitution sub, sub s is not unifiable with t.      

lpUnif :: [([Term],Form)] -> [Term] -> Unif Bool
lpUnif env [] = return True -- success
lpUnif env (p:ps) = do
  r <- unifStep env p
  case r of
    Nothing -> return False -- if one query is irreducible by lpUnif, then it is a failure
    Just (ns, s) ->
      lpUnif env ((map (apply s) ps)++ns)
                       

runLPUnif :: [Form] -> [Term] -> (Bool, Subst)
runLPUnif fs qs = 
  let
    fs1 = reorder fs [] []
    fs' = quantify fs1 in
  runIdentity $ runStateT (evalStateT (lpUnif fs' qs) 1) []

axioms = let
         as = axiomExtension $ ruleExtension [r1, r2, r3, r4, r5]
         in reverse as -- (reverse is)++ [l]
         
q1 = App (App (Pred "Xi") (App (App (Fun "Cmp") (Var "G")) (App (Fun "Gs") (Var "X")))) (App (Pred "Eq") (App Star (Var "A")))
testUnif =
  let (b, s) = runLPUnif axioms [q1] in
  if b then disp s else text "fail!"
