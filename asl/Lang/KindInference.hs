module Lang.KindInference where
import Lang.Syntax
import Lang.PrettyPrint
import Lang.Monad

import Text.Parsec.Pos
import Text.PrettyPrint hiding(sep)

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import qualified Data.Map as M
import qualified Data.Set as S
import Data.List hiding(partition)

type KCMonad a = StateT Int (StateT KSubst Global) a  

type KSubst = [(VName, Exp)]
type LocalEnv = [(VName, Exp)]

runKinding :: [Exp] -> Global KSubst
runKinding ls = execStateT (evalStateT (mapM inferKind ls) 0) []

ground :: Exp -> Exp
ground (KVar x) = Star
ground (KArrow k1 k2) = KArrow (ground k1) (ground k2)
ground Star = Star

inferKind :: Exp -> KCMonad Exp
inferKind (Con x) = do
  gEnv <- lift $ lift get
  case M.lookup x (dataType gEnv) of
    Just (k, _) -> return k
    Nothing -> tcError "Kinding error "
           [(disp "undefine type constructor", disp x)]
  
inferKind (EVar x) = do
  env <- lift get
  case lookup x env of
    Nothing -> do
      ki <- makeName "k"
      let kind = KVar ki
      lift $ modify (\ e -> (x, kind): e)
      return kind
    Just k -> return k  
  
inferKind (FApp f1 f2) = do
  k1 <- inferKind f1
  k2 <- inferKind f2
  k <- makeName "k"
  unificationK k1 $ KArrow k2 (KVar k) 
  return (KVar k) 

inferKind (Arrow f1 f2) = do
  k1 <- inferKind f1
  k2 <- inferKind f2
  unificationK k1 $ Star
  unificationK k2 $ Star
  return Star

inferKind (Forall x f) = do
  k <- inferKind f
  return Star

combineK :: KSubst -> KSubst -> KSubst
combineK s2 s1 =
   s2 ++ [(v, applyK s2 t) | (v, t) <- s1] 

unifyK :: Exp -> Exp -> KCMonad KSubst
unifyK (KArrow t1 t2) (KArrow a1 a2) = do
  s1 <- unifyK t1 a1
  s2 <- unifyK (applyK s1 t2) (applyK s1 a2) 
  return $ combineK s2 s1

unifyK (KVar tn) t =
  varBindK tn t
unifyK t (KVar tn) = varBindK tn t

unifyK Star Star = return []

unifyK t t' = tcError "Unification failure during Kinding: "
           [(disp "trying to unify ", disp t),(disp "with ", disp t')]

varBindK x t | t == KVar x = return []
             | x `S.member` freeKVar t =
                tcError "Occur-Check failure during Kinding: "
                [(disp "trying to unify ", disp x),(disp "with ", disp t)]
             | otherwise = return [(x, t)]

-- unificationK :: FType -> FType -> TCMonad ()
unificationK t1 t2 = do
  subs <- lift get
  new <- unifyK (applyK subs t1) (applyK subs t2)
  lift $ put $ combineK new subs

