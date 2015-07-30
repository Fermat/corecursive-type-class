module Lang.Functionalisation where
import Lang.Syntax
import Lang.PrettyPrint

import Data.List
import qualified Data.Set as S
import Control.Monad.Reader
import Control.Monad.State

type Axioms = [(VName, Exp)]
type Lemmas = [(VName, Exp)]


runRewrite d axioms =
  runReader (evalStateT (rewrite d) 0) axioms

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

rewrite (App t1 t2) = do
  t1' <- rewrite t1
  t2' <- rewrite t2
  case (t1', t2') of
    (Just t1'', Just t2'') -> 
      return $ Just $ App t1'' t2''
    _ -> return Nothing
rewrite (EVar x) = return $ Just $ EVar x
rewrite (Lambda x t) = do
  t' <- rewrite t
  case t' of
    Just t' -> return $ Just $ Lambda x t'
    Nothing -> return Nothing

rewrite a = rewrite (Imply [] a)

runStep d axioms =
  runState (evalStateT (oneStep d) 0) axioms


oneStep :: Exp -> StateT Int (State Axioms) (Maybe Exp)
oneStep (Imply [] h) = do
  axioms <- lift get
  case firstMatch h axioms of
    Nothing -> return Nothing
    Just (k, ls) -> return $ Just $ foldl' (\ z x -> App z x) (EVar k) ls
 where firstMatch  x [] = Nothing
       firstMatch  x ((k, Imply bds h'):ys) = 
         case match h' x of
           Nothing -> firstMatch  x ys
           Just s -> Just $ (k, map (applyE s) bds)
       firstMatch  x ((k, h'):ys) = firstMatch x ((k, Imply [] h'):ys)
       success [] = True
       success (Nothing:rs) = False
       success (Just _ :rs) = success rs
         
oneStep (Imply bds@(y:ys) h) = do
  as <- mapM (\ x -> makeName "b") bds
  let new = zip as bds
  lift $ modify (\ y -> new ++ y)
  res <- oneStep h
  case res of
    Nothing -> return Nothing
    Just res' -> 
      return $ Just $ foldr (\ a b -> Lambda a b) res' as

oneStep a = oneStep (Imply [] a)


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

corecursive :: Exp -> Axioms -> Lemmas -> Maybe Exp
corecursive t axioms lemmas = 
  let (t', as) = runStep t axioms in
  case t' of
    Nothing -> Nothing
    Just t'' -> 
      runRewrite t'' (lemmas++as)

t1' = FApp (EVar "Eq") (FApp (EVar "y") (EVar "y"))
t2' = FApp (EVar "Eq") (FApp (EVar "char") (EVar "char"))

dl = FApp (Con "Eq") (FApp (Con "DList") (Con "Char"))
c1 = Imply [(FApp (Con "Eq") (EVar "y")),
            (FApp (Con "Eq") (FApp (Con "DList") (FApp (Con "DList") (EVar "y"))))] (FApp (Con "Eq") (FApp (Con "DList") (EVar "y")))
     
c2 = Imply [] (FApp (Con "Eq") (Con "Char"))

lm1 = Imply [(FApp (Con "Eq") (EVar "y"))] (FApp (Con "Eq") (FApp (Con "DList") (EVar "y")))
lm1' = case runNegative (Imply [(Imply [lm1] (Con "what"))] (Con "what") ) of
  (Imply [(Imply [l] (Con "what"))] (Con "what") ) -> l
axiom1 = [("k1", c1), ("k2", c2)]

test4 = runRewrite dl axiom1
test5 = corecursive lm1' axiom1 [("alpha", lm1)]
t1 = Imply [] (FApp (Con "Eq") (Con "Unit"))
t2 = Imply [(FApp (Con "Eq") (FApp (EVar "F") (FApp (EVar "G") (EVar "A"))))]
     (FApp (Con "Eq") (FApp (FApp (FApp (Con "Comp") (EVar "F")) (EVar "G")) (EVar "A")))
     
t3 = Imply [(FApp (Con "Eq") (EVar "y"))] (FApp (Con "Eq") (FApp (Con "Pair") (EVar "y")))

t4 = Imply [(FApp (Con "Eq") (EVar "A")), (FApp (Con "Eq") (EVar "R"))]
     (FApp (Con "Eq") (FApp (FApp (Con "GS") (EVar "A")) (EVar "R")))
t5' = runPositive t5
t5'' = runNegative (Imply [(Imply [Forall "F" t5] (Con "what"))] (Con "what") )
t5 = Imply [Forall "X" $ Imply [(FApp (Con "Eq") (EVar "X"))] (FApp (Con "Eq") (FApp (EVar "F") (EVar "X")))]
     (FApp (Con "Eq") (FApp (FApp (Con "Fix") (EVar "F")) (Con "Pair")))
t6 = Imply [Con "B"] (FApp (Con "Eq") (FApp (FApp (Con "Fix") (FApp (Con "GS") (Con "Unit"))) (Con "Pair")))     

axioms2 = [("k1", t1), ("k2", t2), ("k3", t3), ("k4", t4), ("k5", t5)]
testMatch :: [Subst]
testMatch = match t1' t2' 

-- testRewrite = runReader (evalStateT (rewrite dl) 0) axiom1
test2 = runRewrite t6 axioms2
test3 = (runStep t6 axioms2)
-- test3 = disp $ 
