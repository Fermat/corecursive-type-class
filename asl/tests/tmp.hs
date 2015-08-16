{-# LANGUAGE RankNTypes#-}
-- suc = \ n s z -> s n
-- zero = \ s z -> z
-- one = suc zero
-- two = suc (suc zero)
-- add = \ n m -> let f = (\ y -> add y m) in n f m 

data Nat = Z | S Nat deriving Show

add n m = case n of
           Z -> m
           S n' -> S (add n' m)
  
data Nested a = a :<: (Nested [a]) | Epsilon
infixr 5 :<:

-- len Epsilon    = 0
-- len (_ :<: xs) = 1 + len xs
data Term v = Var v | App (Term v) (Term v) | Lam (Term (Incr v))
data Incr v = Zero | Succ v
-- fixMT ::  ((forall x3 . x3) -> x3) -> (forall x2 . x2)


type MapT = forall a b. (a->b) -> Term a -> Term b

fixMT :: (MapT -> MapT) -> MapT
fixMT f = f (fixMT f)

mapI f Zero = Zero
mapI f (Succ x) = Succ  (f x)
                       
mapT :: MapT
mapT = fixMT (\ mt -> \ f t ->
               case t of
                 Var x ->Var (f x)
                 App t1 t2 -> App (mt f t1) (mt f t2)
                 Lam t -> Lam (mt (mapI f) t))
-- mt : (a->b) -> Term a -> Term b
-- f : a -> b
--  mapI f : Incr a -> Incr b
-- Term Incr v
