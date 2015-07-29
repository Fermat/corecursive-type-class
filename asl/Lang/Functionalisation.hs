module Lang.Functionalisation where
import Lang.Syntax
import Lang.PrettyPrint

import Data.List
import Control.Monad.Reader
import Control.Monad.State

type Axioms = [(VName, Exp)]

runRewrite d axioms fs = runReader (evalStateT (evalStateT (rewrite d) 0) fs) axioms

rewrite :: Exp -> StateT Int (StateT [VName] (Reader Axioms)) (Maybe Exp)
rewrite (Imply [] h) = do
  axioms <- ask
  funcs <- lift get
  case firstMatch funcs h axioms of
    Nothing -> return Nothing
    Just (k, ls) -> do res <- mapM rewrite ls
                       if success res then do
                         let res' = map (\ (Just x) -> x) res
                         return $ Just $ foldl' (\ z x -> App z x) (EVar k) res' 
                         else return Nothing
 where firstMatch funcs x [] = Nothing
       firstMatch funcs x ((k, Imply bds h'):ys) = 
         case match funcs h' x of
           Nothing -> firstMatch funcs x ys
           Just s -> Just $ (k, map (applyE s) bds)
       firstMatch funcs x ((k, h'):ys) = firstMatch funcs x ((k, Imply [] h'):ys)
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

match fs (EVar s) t1 =
  if s `elem` fs then
    if (EVar s) == t1 then return [] else mzero
  else return [(s, t1)]
       

match fs (FApp t1 t2) (FApp t1' t2') = do
  s1 <- match fs t1 t1'
  s2 <- match fs t2 t2'
  merge s1 s2

match _ _ _ = mzero

t1' = FApp (EVar "Eq") (FApp (EVar "y") (EVar "y"))
t2' = FApp (EVar "Eq") (FApp (EVar "char") (EVar "char"))

dl = FApp (EVar "Eq") (FApp (EVar "DList") (EVar "Char"))
c1 = Imply [(FApp (EVar "Eq") (EVar "y"))] (FApp (EVar "Eq") (FApp (EVar "DList") (EVar "y")))
c2 = Imply [] (FApp (EVar "Eq") (EVar "Char"))
axiom1 = [("k1", c1), ("k2", c2)]

t1 = Imply [] (FApp (EVar "Eq") (EVar "Unit"))
t2 = Imply [(FApp (EVar "Eq") (FApp (EVar "F") (FApp (EVar "G") (EVar "A"))))]
     (FApp (EVar "Eq") (FApp (FApp (FApp (EVar "Comp") (EVar "F")) (EVar "G")) (EVar "A")))
     
t3 = Imply [(FApp (EVar "Eq") (EVar "y"))] (FApp (EVar "Eq") (FApp (EVar "Pair") (EVar "y")))

t4 = Imply [(FApp (EVar "Eq") (EVar "A")), (FApp (EVar "Eq") (EVar "R"))]
     (FApp (EVar "Eq") (FApp (FApp (EVar "GS") (EVar "A")) (EVar "R")))

t5 = Imply [Imply [(FApp (EVar "Eq") (EVar "X"))] (FApp (EVar "Eq") (FApp (EVar "F") (EVar "X")))]
     (FApp (EVar "Eq") (FApp (FApp (EVar "Fix") (EVar "F")) (EVar "Pair")))
t6 = (FApp (EVar "Eq") (FApp (FApp (EVar "Fix") (FApp (EVar "GS") (EVar "Unit"))) (EVar "Pair")))     

axioms2 = [("k1", t1), ("k2", t2), ("k3", t3), ("k4", t4), ("k5", t5)]
fs = ["Eq", "Comp", "Fix", "GS", "Pair", "Unit", "Char", "DList", "X"]  
testMatch :: [Subst]
testMatch = match fs t1' t2' 

-- testRewrite = runReader (evalStateT (rewrite dl) 0) axiom1
test2 = runRewrite t6 axioms2 fs
