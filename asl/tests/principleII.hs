{-#LANGUAGE GADTs, FlexibleContexts, UndecidableInstances #-}
data Unit where
  Unit :: Unit

data Pair a b where
 Pair :: a -> b -> Pair a b

data HBush f a where
  HBLeaf :: HBush f a
  HBNode :: Pair a (f (f a)) -> HBush f a

data HPTree f a where
  HPLeaf :: a -> HPTree f a
  HPNode :: f (Pair a a) -> HPTree f a  

data Mu f a where
  In :: f (Mu f) a -> Mu f a

instance Eq Unit where
  (==) a b = True

instance (Eq a, Eq b) => Eq (Pair a b) where
  (==) = \ x y -> case x of
                 Pair x1 y1 -> case y of
                                Pair x2 y2 ->  (x1 == x2) && (y1 == y2)

instance Eq (f (Mu f) a) => Eq (Mu f a) where
   (==) = \ x y -> case x of
                  In s -> case y of
 		            In t -> s == t

instance (Eq a, Eq (Pair a (f (f a)))) => Eq (HBush f a) where
  (==) = \ x y -> case x of
                 HBLeaf -> case y of
                            HBLeaf -> True
                            HBNode a -> False
                 HBNode a -> case y of
                              HBLeaf -> False
                              HBNode b -> a == b


instance (Eq a, Eq (f (Pair a a))) => Eq (HPTree f a) where
   (==) = \ x y -> case x of
                  HPLeaf s -> case y of
 		                HPLeaf t -> s == t
                                HPNode p -> False
                  HPNode p -> case y of
                                HPLeaf t -> False
                                HPNode q -> p == q

-- a1 :: Mu HBush Unit
-- a1 = In HBLeaf

-- a2 = In (HBNode (Pair Unit a3))
-- a3 :: Mu HBush (Mu HBush Unit)
-- a3 = In HBLeaf

a1 :: Mu HPTree Unit
a1 = In (HPLeaf Unit)

--a2 = In (HPNode (Pair Unit Unit))
-- a3 :: Mu HBush (Mu HBush Unit)
test = a1 == a1

-- test = a2 == a1
