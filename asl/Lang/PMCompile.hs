module Lang.PMCompile where
import Lang.Syntax
import Lang.Pattern
import Lang.Monad
import Data.List

convert :: Env -> Env
convert env =
  let eqs = equations env
      eqs' = divide eqs
      eqss = map helper eqs' -- [(eq1, []), (eq2, [])]
      eqss' = map (helper1 env) eqss in 
  foldl' (\ e (n, d) -> extendProgDef n (Scheme [] (DArrow [] (EVar "Internal"))) d e) env eqss'
  where helper ls = (getFst ls , (map snd ls))
        getFst ((a,_):xs) = a
        helper1 e (n, qs) = let ar = arity n e
                                Just (kind, _) = lookup n (dataType e)
                                vars = [makeVar "u" i | i <- [1..ar]]
                                vars' = zip vars (flatten kind)
                                body = match "u" e ar vars' qs (EVar "Error")
                                close = foldr (\ x y -> Lambda x y) body vars 
                            in (n, close)

divide [] = []
divide (p:xs)  =
  tack p $ divide xs

tack p [] = [[p]]
tack p@(a1, eqs1) ((p'@(a2, eqs2):l):ys) =
  if a1 == a2 then (p:p':l):ys
  else (p':l) : tack p ys

