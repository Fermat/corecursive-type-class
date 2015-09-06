{-# LANGUAGE RankNTypes, TypeFamilies, UndecidableInstances #-}

data Z
data S n

data D a b

k1 :: D n (S m) -> D (S n) m
k1 = undefined

k2 :: D (S m) Z -> D Z m
k2 = undefined

f :: (forall n. D n (S m) -> D (S (Add m n)) Z) -> D Z m
f = \ g -> k2 (g (f (\ x -> g (k1 x))))

type family Add m n
type instance Add Z n  =  n
type instance Add (S n) m = Add (S m) n
