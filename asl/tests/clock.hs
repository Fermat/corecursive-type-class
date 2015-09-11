{-# LANGUAGE RankNTypes, TypeFamilies, UndecidableInstances, AllowAmbiguousTypes #-}

data Z
data S n

data D a b

k1 :: D n (S m) -> D (S n) m
k1 = undefined

k2 :: D (S m) Z -> D Z m
k2 = undefined

f :: (forall n. D n (S m) -> D (S (Add m n)) Z) -> D Z m
f g = k2 (g (f (\ x -> g (k1 x))))

p :: (n ~ Add Z n) => D Z Z
p =  f k1

type family Add m n where
  -- Add Z n  =  n
  -- Add (S m) n = Add m (S n)
  Add n Z  =  n
  Add m (S n) = Add (S m) n
 
