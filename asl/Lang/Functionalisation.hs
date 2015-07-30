module Lang.Functionalisation where
import Lang.Syntax
import Lang.PrettyPrint

import Data.List
import qualified Data.Set as S
import Control.Monad.Reader
import Control.Monad.State

type Axioms = [(VName, Exp)]

runRewrite d axioms = runReader (evalStateT (rewrite d) 0) axioms

rewrite :: Exp -> StateT Int (Reader Axioms) (Maybe Exp)
rewrite (Imply [] h) = do
  axioms <- ask
  case firstMatch h axioms of
    Nothing -> return Nothing
    Just (k, ls) -> do res <- mapM rewrite ls
                       if success res then do
                         let res' = map (\ (Just x) -> x) res
                         return $ Just $ foldl' (\ z x -> App z x) (EVar k) res' 
                         else return Nothing
 where firstMatch  x [] = Nothing
       firstMatch  x ((k, Imply bds h'):ys) = 
         case match h' x of
           Nothing -> firstMatch  x ys
           Just s -> Just $ (k, map (applyE s) bds)
       firstMatch  x ((k, h'):ys) = firstMatch x ((k, Imply [] h'):ys)
       success [] = True
       success (Nothing:rs) = False
       success (Just _ :rs) = success rs
         
rewrite (Imply bds@(y:ys) h) = do
  as <- mapM (\ x -> makeName "a") bds
  let new = zip as bds
  res <- local (\ y -> new ++ y) $ rewrite h
  case res of
    Nothing -> return Nothing
    Just res' -> 
      return $ Just $ foldr (\ a b -> Lambda a b) res' as

rewrite a = rewrite (Imply [] a)
--- helper function

merge :: MonadPlus m => Subst -> Subst -> m Subst
merge s1 s2 = if agree then return $ s1 ++ s2 else mzero
  where agree = all (\ x -> applyE s1 (EVar x) == applyE s2 (EVar x)) (map fst s1 `intersect` map fst s2) 

-- match :: MonadPlus m => Exp -> Exp -> m Subst

match (EVar s) t1 = return [(s, t1)]
match (FApp t1 t2) (FApp t1' t2') = do
  s1 <- match t1 t1'
  s2 <- match t2 t2'
  merge s1 s2
match (Con s) (Con t) | s == t = return []
match _ _ = mzero


myPi a f = do
  f' <- inst f
  let as = freeVar a
      fs = freeVar f'
      dom = S.toList (S.difference fs as)
  names <- mapM (\ y -> makeName "d") dom
  let cons = map Con names
      sub = zip dom cons
  return $ applyE sub f'

myVarPi a f = do
  f' <- inst f
  let dom = S.toList $ freeVar a
  names <- mapM (\ y -> makeName "d") dom
  let cons = map Con names
      sub = zip dom cons
  return $ applyE sub f'

positive :: Exp -> State Int Exp
positive (Imply bds h) = do
  bds' <- mapM (myPi h) bds
  res <- mapM negative bds'
  return $ Imply res h
positive h = return h

negative :: Exp -> State Int Exp
negative (Imply bds h) = do
  bds' <- mapM (myVarPi h) bds
  res <- mapM positive bds'
  return $ Imply res h
negative a = return a

runPositive exp  = evalState (positive exp) 0
runNegative exp  = evalState (negative exp) 0
t1' = FApp (EVar "Eq") (FApp (EVar "y") (EVar "y"))
t2' = FApp (EVar "Eq") (FApp (EVar "char") (EVar "char"))

dl = FApp (EVar "Eq") (FApp (EVar "DList") (EVar "Char"))
c1 = Imply [(FApp (EVar "Eq") (EVar "y"))] (FApp (EVar "Eq") (FApp (EVar "DList") (EVar "y")))
c2 = Imply [] (FApp (EVar "Eq") (EVar "Char"))
axiom1 = [("k1", c1), ("k2", c2)]

t1 = Imply [] (FApp (Con "Eq") (Con "Unit"))
t2 = Imply [(FApp (Con "Eq") (FApp (EVar "F") (FApp (EVar "G") (EVar "A"))))]
     (FApp (Con "Eq") (FApp (FApp (FApp (Con "Comp") (EVar "F")) (EVar "G")) (EVar "A")))
     
t3 = Imply [(FApp (Con "Eq") (EVar "y"))] (FApp (Con "Eq") (FApp (Con "Pair") (EVar "y")))

t4 = Imply [(FApp (Con "Eq") (EVar "A")), (FApp (Con "Eq") (EVar "R"))]
     (FApp (Con "Eq") (FApp (FApp (Con "GS") (EVar "A")) (EVar "R")))
t5' = runPositive t5
t5 = Imply [Forall "X" $ Imply [(FApp (Con "Eq") (EVar "X"))] (FApp (Con "Eq") (FApp (EVar "F") (EVar "X")))]
     (FApp (Con "Eq") (FApp (FApp (Con "Fix") (EVar "F")) (Con "Pair")))
t6 = (FApp (Con "Eq") (FApp (FApp (Con "Fix") (FApp (Con "GS") (Con "Unit"))) (Con "Pair")))     

axioms2 = [("k1", t1), ("k2", t2), ("k3", t3), ("k4", t4), ("k5", t5')]
testMatch :: [Subst]
testMatch = match t1' t2' 

-- testRewrite = runReader (evalStateT (rewrite dl) 0) axiom1
test2 = runRewrite t6 axioms2 
-- test3 = disp $ 
