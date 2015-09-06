{-# LANGUAGE RankNTypes, TypeFamilies, UndecidableInstances #-}

data Z
data S n

data D a b

k1 :: D n (S m) -> D (S n) m
k1 = undefined

k2 :: D (S m) Z -> D Z m
k2 = undefined

f :: (forall n. D n (S m) -> D (S (Add m n)) Z) -> D Z m
f g = k2 (g (f (\ x -> g (k1 x))))

p :: D Z Z
p =  f (\ x -> k1 x)
type family Add m n
type instance Add n Z  =  n
type instance Add m (S n) = Add (S m) n

