-- | Anti-Unification of Exps
module Lang.AntiUnify where

import           Lang.Syntax
import           Data.Tuple                    (swap)

type AUExp = [(Exp, Exp, Exp)] --
type SubstAU = [(Int, (Exp,Exp))]

-- \ Given two expressions return their anti-unifier
antiUnify :: Exp -> Exp -> Exp
antiUnify e1 e2 = fst $ antiUnifyExp e1 e2 []

-- | Given two expresions and a list of substitutions return the antiunifier
-- and the substitutions for it.
antiUnifyExp :: Exp -> Exp -> SubstAU -> (Exp, SubstAU)
antiUnifyExp e1@(FApp l1@(FApp _ _) r1) e2@(FApp l2@(FApp _ _) r2) s
  | outerExp e1 == outerExp e2 = let (le, ls) = antiUnifyExp l1 l2 s
                                     (re, rs) = antiUnifyExp r1 r2 ls
                                 in  (FApp le re, rs)
  | otherwise = checkSubs e1 e2 s
antiUnifyExp e1@(FApp (FApp _ _) _) e2@(FApp (Con _) _) s =
  checkSubs e1 e2 s
antiUnifyExp e1@(FApp (Con _) _) e2@(FApp (FApp _ _) _) s =
  checkSubs e1 e2 s
antiUnifyExp (FApp l1 r1) (FApp l2 r2) s = (FApp le re, rs)
  where (le, ls) = antiUnifyExp l1 l2 s
        (re, rs) = antiUnifyExp r1 r2 ls
antiUnifyExp e1 e2 s
  | e1 == e2 = (e1, s)
  | otherwise = checkSubs e1 e2 s

-- \ If a substitution exists return it and the list of subs, otherwise return
-- a fresh variable representing the substitution and the modified list of subs
checkSubs :: Exp -> Exp -> SubstAU -> (Exp, SubstAU)
checkSubs e1 e2 s =
  case subExists (e1,e2) s of
    Just x  -> (EVar $ "var_" ++ show x, s)
    Nothing -> (EVar $ "var_" ++ show v, s ++ [(v, (e1,e2))])
      where v = nextVar s

-- | Check if a substitution exists for the the two expressions and return it
-- if it does
subExists :: (Exp,Exp) -> SubstAU -> Maybe Int
subExists e subs = lookup e subAU
  where subAU = map swap subs

-- Calculate the nex variable to use
nextVar :: SubstAU -> Int
nextVar [] = 1
nextVar subs = maximum (map fst subs) + 1

-- Find the outermost function symbol
outerExp :: Exp -> Exp
outerExp (FApp e1@(Con _ee1) _e2) = e1
outerExp (FApp e1 _e2) = outerExp e1
outerExp e1 = e1
