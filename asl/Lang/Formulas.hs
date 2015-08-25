module Lang.Formulas
       where
import Lang.Monad
import Lang.Syntax hiding(match)
import Control.Monad.State.Lazy
import Control.Monad
import Control.Monad.Identity
import Control.Parallel

import qualified Data.Set as S

-- import The match function here is
-- doing precise matching, meaning, variable can only
-- be matched to variable, not other stuff.
match :: MonadPlus m => [(VName, VName)] -> Exp -> Exp -> m [(VName, VName)]
match env (Con x) (Con y) =
  if x == y then return env
  else mzero

match env (EVar x) (EVar y) = 
  case lookup x env of
    Just z -> if z == y then return env
              else mzero
    mzero -> if x == y then return env else return $ (x, y):env

match env (Arrow f1 f2) (Arrow a1 a2) = do
  r1 <- match env f1 a1
  r2 <- match r1 f2 a2
  return r2

match env (FApp f1 f2) (FApp a1 a2) = do
  r1 <- match env f1 a1
  r2 <- match r1 f2 a2
  return r2

match _ _ _ = mzero

-- cmp :: [VName] -> FType -> [FType] -> [(FType, [(VName, VName)])]
-- cmp datas p l =
--   [(r, sub) | r <- l, let (b, sub) = alphaEq datas p r , b == True]

insert :: a -> [a] -> [[a]]
insert a [] = [[a]]
insert a l@(x:xs) =
  let c = [ x:b | b <- insert a xs] in
  (a:l) : c

perm :: [a] -> [[a]]
perm [] = [[]]
perm (x:xs) =  [ b | l <- perm xs, b <- insert x l]

-- getPred :: [FType] -> S.Set VName
-- getPred [] = S.empty
-- getPred ((FCons x args):xs) = S.insert x $ getPred xs

getPred :: Exp -> VName
getPred (Con x) =  x
getPred (FApp x1 x2) = getPred x1
getPred _ = error "not a predicate"

divide :: [Exp] -> [[Exp]]
divide [] = []
divide (p:xs)  =
  tack p $ divide xs

tack p [] = [[p]]
tack p ((p':l):ys) =
  if getPred p == getPred p' then (p:p':l):ys
  else (p':l) : tack p ys

-- same as divide, but group the identical predicates togehter
separate :: [Exp] -> [[Exp]]
separate [] = []
separate (p:xs) =
  tack' p $ separate xs

tack' p [] = [[p]]
tack' p1 ((p2:l):ys) =
  if p1 == p2 then (p1:p2:l):ys
  else (p2:l) : tack' p1 ys

-- reorder assumes check a b && check b a == True.
-- reorder first argument according to the second
reorder :: [[Exp]] -> [[Exp]]-> [[Exp]]
reorder [] [] = []
reorder (y:ys) (z:zs) =
  if same y z then y : reorder ys zs
  else reorder (ys++[y]) (z:zs)
     where same ( q:_) ( p:_) = getPred q == getPred p
reorder a b = error $ "debug:" ++ show a ++ show b

-- check a b : check if every predicate in a is also in b
check :: [[Exp]] -> [[Exp]] -> Bool
check (a:as) bs = if get a bs then check as bs else False
  where get (p:_) [] = False
        get (x:qs) (( y:_):ys) =
          if getPred x == getPred y then True else get (x:qs) ys
check [] bs = True

combine :: MonadPlus m => [(VName, VName)] -> [(VName, VName)] -> m [(VName, VName)]
combine as [] = return as
combine as ((x,v):bs) = 
  case lookup x as of
    Just b -> if v == b then combine as bs
              else mzero
    Nothing -> do
      sub <- combine as bs
      return $ (x,v):sub

inverse :: [(VName, VName)] -> [(VName, VName)]
inverse ls = map (\(x, y) -> (y, x)) ls

reverseCombine :: MonadPlus m => [(VName, VName)] -> m [(VName, VName)]
reverseCombine l = do
  let sub = map (\ x -> [x]) $ inverse l
  foldM combine [] sub

alphaEq :: MonadPlus m => Exp -> Exp -> m [(VName, VName)]
alphaEq f1 f2 = do
  s <- match [] f1 f2
  reverseCombine s
      
listAlpha :: MonadPlus m => [Exp] -> [Exp] -> m [(VName, VName)]
listAlpha fs ts = do
  ls <- zipWithM alphaEq fs ts
  s <- foldM combine [] ls
  reverseCombine s

alphaFormulas :: MonadPlus m => [[Exp]] -> [[Exp]] -> m [(VName, VName)]
alphaFormulas fss tss = do
  lss <- zipWithM (listAlpha) fss tss
  s <- foldM combine [] lss
  reverseCombine s

-- generate all possible formulas per position
genFormulas (fs:fss) = [ a' | f <- fs, let a = map (\ y -> f:y) $ genFormulas fss, a' <- a ]
genFormulas [] = [[]]  

formulasEq :: [[Exp]] -> [[Exp]] -> [[(VName, VName)]]
formulasEq fss tss =
   let n = map perm tss
       all = genFormulas n in
   map helper all
  where helper y = case alphaFormulas y fss of
                       Nothing -> [("Fail", "Fail")]
                       Just o -> o

firstNon [] = Nothing
firstNon (a:as) = if a == [("Fail", "Fail")] then firstNon as else Just a

-- firstSub datas fss tss, it assumes all the variables in fss is separated from
-- all the variables in tss.
firstSub :: [[Exp]] -> [[Exp]] -> Maybe [(VName, VName)]
firstSub  fss tss = firstNon $ formulasEq fss tss 


-- testing

{-
ftype1 = FCons "Eq1" [FVar "Q", FVar "E"]
ftype2 = FCons "Eq1" [FVar "B", FVar "P"] -- [FCons "E" [FVar "C"], FVar "B"]

test1 :: Maybe [(VName, VName)]
test1 = alphaEq [] ftype1 ftype2

ftype3 = FCons "Eq2" [FVar "Q", FVar "E"]
ftype4 = FCons "Eq2" [FVar "E", FVar "P"]
ftype5 = FCons "Eq2" [FVar "Y", FVar "Z"]
ftype6 = FCons "Eq2" [FVar "X", FVar "Y"]

f7 = FCons "Eq1" [FVar "P1", FVar "U1"]
f8 = FCons "Eq1" [FVar "P11", FVar "P11"]
--test5 = firstSub [] [[ftype3, ftype4], [f7]] [[ftype5, ftype6],[f8]]
test55 = firstSub []  [[f8]] [[f7]]
--test2 = runState (alphaFormulas [] [ftype3, ftype4] [ftype5, ftype6]) []

test3 = reorder [[FCons "Eq4" [FVar "Y1",FVar "Z1"]], [FCons "Eq2" [FVar "Q1",FVar "E1"],FCons "Eq2" [FVar "E1",FVar "P1"]],[FCons "Eq1" [FVar "Q1",FVar "E1"],FCons "Eq1" [FCons "E1" [FVar "C1"],FVar "B1"]], [FCons "Eq" [FVar "X1",FVar "Y1"]]]  [[FCons "Eq" [FVar "X",FVar "Y"]],[FCons "Eq4" [FVar "Y",FVar "Z"]],[FCons "Eq2" [FVar "Q",FVar "E"],FCons "Eq2" [FVar "E",FVar "P"]],[FCons "Eq1" [FVar "Q",FVar "E"],FCons "Eq1" [FCons "E" [FVar "C"],FVar "B"]]]    
--[FCons "Eq4" [FVar "Y1",FVar "Z1"]],
test4 = check  [[FCons "Eq" [FVar "X",FVar "Y"]],[FCons "Eq4" [FVar "Y",FVar "Z"]],[FCons "Eq2" [FVar "Q",FVar "E"],FCons "Eq2" [FVar "E",FVar "P"]],[FCons "Eq1" [FVar "Q",FVar "E"],FCons "Eq1" [FCons "E" [FVar "C"],FVar "B"]]]   [ [FCons "Eq2" [FVar "Q1",FVar "E1"],FCons "Eq2" [FVar "E1",FVar "P1"]],[FCons "Eq1" [FVar "Q1",FVar "E1"],FCons "Eq1" [FCons "E1" [FVar "C1"],FVar "B1"]], [FCons "Eq" [FVar "X1",FVar "Y1"]]] 
-}


