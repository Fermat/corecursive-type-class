module Analyzer.Syntax where
import Control.Monad
import Control.Monad.State
import qualified Data.Set as S
import Test.QuickCheck
import Data.List


data Term = Star
          | Var String
          | Fun String
          | Pred String
          | App Term Term deriving (Show, Eq, Ord)

instance Arbitrary Term where
  arbitrary = do
    n <- choose (1,5) :: Gen Int
    case n of
      1 -> return Star
      2 -> do s <- arbitrary
              return $ Var s
      3 -> do s <- arbitrary
              return $ Fun s
      4 -> do s <- arbitrary
              return $ Pred s
      5 -> do t1 <- arbitrary
              t2 <- arbitrary
              return $ App t1 t2

data Form = Form{head :: Term, body :: [Term]} deriving Show

data Rule = Rule{cond :: [Term], left :: Term, right :: Term} deriving Show

-- the domain of subsitution can be Star and Var
type Subst = [(Term, Term)]

apply :: Subst -> Term -> Term
apply s a@(Fun _) = a
apply s a@(Pred _) = a
apply s (App t1 t2) = App (apply s t1) (apply s t2)
apply s x = case lookup x s of
                  Just a -> a
                  Nothing -> x

-- coming from Mark Jones's Typing Haskell
compose :: Subst -> Subst -> Subst
compose s1 s2 = [(x, apply s1 t) | (x, t) <- s2] ++ s1

merge :: MonadPlus m => Subst -> Subst -> m Subst
merge s1 s2 = if agree then return $ s1 ++ s2 else mzero
  where agree = all (\ x -> apply s1 x == apply s2 x) (map fst s1 `intersect` map fst s2) 

match :: MonadPlus m => Term -> Term -> m Subst

match (Var s) t1 -- | (Var s) == t1 = return []
  = return [(Var s, t1)]
match Star Star = return []

match (Pred p1) (Pred p2) =
  if p1 == p2 then return [] else mzero

match (Fun p1) (Fun p2) =
  if p1 == p2 then return [] else mzero
                                  
match (App t1 t2) (App t1' t2') = do
  s1 <- match t1 t1'
  s2 <- match t2 t2'
  merge s1 s2

match _ _ = mzero

t1 = App (Pred "eq") (App (Var "y") (Var "x"))
t2 = App (Pred "eq") (App (Var "y") (Var "y"))

testMatch :: [Subst]
testMatch = match t1 t1


listMerge l = 
  let sub = map (\ x -> [x]) $ l in
  foldM merge [] sub
  
alphaEq f1 f2 =
  case match f1 f2 of
    [] -> False
    s:[] -> let s' = [(a, b) | (b, a) <- s] in
      if all prop s' then
        case listMerge s' of
             Nothing -> False
             Just sub -> f1 == apply sub f2
      else False
      where prop (Var _, b1) = True                 
            prop (_, b1) = False


fv :: Term -> S.Set Term
fv (Var x) = S.insert (Var x) S.empty
fv (Fun f) = S.empty
fv (Pred f) = S.empty
fv Star = S.empty
fv (App f1 f2) = fv f1 `S.union` fv f2

makeName name = do
  m <- get
  modify (+1)
  return $ name ++ show m

makeNames name ls = mapM (\ y -> makeName name) ls

unify :: MonadPlus m => Term -> Term -> m Subst
unify (App t1 t2) (App t1' t2') = do
  s1 <- unify t1 t1'
  s2 <- unify (apply s1 t2) (apply s1 t2')
  return $ compose s2 s1

unify (Var s) t1 = varBind (Var s) t1
unify t1 (Var s) = varBind (Var s) t1

unify Star Star = return []

unify (Pred p1) (Pred p2) =
  if p1 == p2 then return [] else mzero

unify (Fun p1) (Fun p2) =
  if p1 == p2 then return [] else mzero
                                  
unify _ _ = mzero

varBind u t | t == u = return []
            | u `S.member` fv t = mzero
            | otherwise = return [(u, t)]


testUnify :: [Subst]
testUnify = unify t2 t1

dpGen :: [Form] -> [Rule]
dpGen fs = [(Rule [] h b) | (Form h bs) <- fs, b <- bs]
