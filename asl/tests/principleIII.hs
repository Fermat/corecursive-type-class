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

data HLam f a where
  HVar :: a -> HLam f a
  HApp :: (f a) -> (f a) -> HLam f a
  HAbs :: (f (Maybe a)) -> HLam f a
  
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

instance (Eq a, Eq (f (Maybe a)), Eq (f a)) => Eq (HLam f a) where
   (==) = \ x y -> case x of
                     HVar s -> case y of
 		                  HVar t -> s == t
                                  HApp u1 u2 -> False
                                  HAbs u -> False
                     HApp p1 p2 -> case y of
                                    HVar t -> False
                                    HApp u1 u2 -> p1 == u1 && p2 == u2
                                    HAbs u -> False
                     HAbs s1 -> case y of
                                    HVar t -> False
                                    HApp u1 u2 -> False
                                    HAbs u -> u == s1


a1 = In (HVar Unit)

--a2 = In (HPNode (Pair Unit Unit))
-- a3 :: Mu HBush (Mu HBush Unit)
test = a1 == a1

-- test = a2 == a1
