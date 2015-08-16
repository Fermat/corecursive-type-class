{-#LANGUAGE GADTs, FlexibleContexts, UndecidableInstances, RankNTypes #-}
type Nat g h = forall a. g a -> h a

type Alg f g = Nat (f g) g

class HFunctor f where
  ffmap :: Functor g => (a -> b) -> f g a -> f g b
  hfmap :: Nat g h -> Nat (f g) (f h)

data Mu f a = In { unIn :: f (Mu f) a }

hfold :: HFunctor f => Alg f g -> Nat (Mu f) g
hfold m (In u) = m (hfmap (hfold m) u)

instance Eq a => Eq (Mu f a) where
  (==) = hfold (==)
