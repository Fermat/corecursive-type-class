module Lang.Functionalisation where
import Lang.Syntax

import Data.List
import Control.Monad.Reader
import Control.Monad.State

type Axioms = [(VName, Exp)]

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
 where firstMatch x [] = Nothing
       firstMatch x ((k, Imply bds h'):ys) = 
         case match h' x of
           Nothing -> firstMatch x ys
           Just s -> Just $ (k, map (applyE s) bds)
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

--- helper function

merge :: MonadPlus m => Subst -> Subst -> m Subst
merge s1 s2 = if agree then return $ s1 ++ s2 else mzero
  where agree = all (\ x -> applyE s1 (EVar x) == applyE s2 (EVar x)) (map fst s1 `intersect` map fst s2) 

match :: MonadPlus m => Exp -> Exp -> m Subst

match (EVar s) t1 
  = return [(s, t1)]

match (FApp t1 t2) (FApp t1' t2') = do
  s1 <- match t1 t1'
  s2 <- match t2 t2'
  merge s1 s2

match _ _ = mzero

t1 = FApp (EVar "eq") (FApp (EVar "y") (EVar "y"))
t2 = FApp (EVar "eq") (FApp (EVar "y") (EVar "y"))

testMatch :: [Subst]
testMatch = match t1 Star
