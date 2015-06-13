module Lang.Pattern (match, arity, makeVar) where

import Lang.PrettyPrint
import Lang.Syntax
import Lang.Monad


import Text.Parsec.Pos
import Text.PrettyPrint

import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Reader

import Data.List hiding(partition)
import qualified Data.Map as M
import qualified Data.Set as S

isVar :: Equation -> Bool
isVar (Var x:ps,e) = True
isVar (Cons x xs : ps,e) = False
--isVar a = error $ "efrom isVar" ++ show a

isCon :: Equation -> Bool
isCon e = not $ isVar e

getCon (Cons c ps1:ps, e) = c

constructors :: Env -> [VName]
constructors env = [ n | (n, (_, True)) <- dataType env ]

arity :: VName -> Env -> Int
arity v env = case lookup v (dataType env) of
                       Nothing -> error "inpropable error just occur"
                       Just (k, _) -> kindArity k
                         where kindArity (KArrow k1 k2) = 1 + kindArity k2
                               kindArity _ = 0

  
match :: VName -> Env -> Int -> [VName] -> [Equation] -> Exp -> Exp
match name env k [] qs def =
  let p = [e | ([], e) <- qs] in -- trace ("spit p "++ show p ++ show qs ++ show def) (head p)
  if null p then def else head p -- trace ("nonempty head") (head p)
  --foldr Applica def [e | ([], e) <- qs]
--  if null qs then (Name "Error") else let ([], p) = head qs in p
match name env k (u:us) qs def = foldr (matchVarCon name env k (u:us)) def (partition isVar qs)

matchVarCon name env k us qs def | isVar $ head qs = matchVar name env k us qs def
matchVarCon name env k us qs def | otherwise = matchCon name env k us qs def

matchVar name env k (u:us) qs def = match name env k us [(ps, applyE [(v, EVar u)] e) | (Var v : ps, e) <- qs] def

matchCon name env k (u:us) qs def =
  Match (EVar u) [matchClause name env c k (u:us) (choose c qs) def | c <- cs]
  where cs = constructors env
        
matchClause name env c k (u:us) qs def =
  let k' = arity c env in
  (c, (us' k'), match name env (k'+ k) ((us' k') ++ us) [(ps' ++ ps, e) | (Cons c ps' : ps, e) <- qs] def )
  where
    us' q = [makeVar name (i + k) | i <- [1..q]]

makeVar n l = n ++ show l

choose c qs = [q | q <- qs, getCon q == c]

partition f [] = []
partition f (x:[]) = [[x]]
partition f (x:x1:xs) | f x == f x1 = tack x (partition f (x1:xs))
                      | otherwise = [x]: partition f (x1:xs)
  where tack x xss = (x : head xss) : tail xss
        

p1 = ( [Cons "List" [(Var "A")]], App (EVar "f") (EVar "A"))
p2 = ( [Cons "Nat" []], EVar "g")
eqs1 = [p2, p1]


env1 = extendData "List" (KArrow Star Star) True emptyEnv
env2 = extendData "Nat" Star True env1
env3 = extendData "Unit" Star True env2
env4 = extendData "Eq" (KArrow Star Star) False env3
-- calling convention, 1 is the number of the argument
test13 = disp $ match "_u" env4  1 ["_u1"] eqs1 (EVar "Error")
