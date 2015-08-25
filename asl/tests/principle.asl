module principle where

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
  
data Bool where
     True :: Bool
     False :: Bool

class Eq a where
   eq :: Eq a => a -> a -> Bool

and = \ x y . case x of
                True -> y
		False -> False

instance  => Eq Unit where
   eq = \ x y . case x of
                   Unit -> case y of 
                              Unit -> True

instance Eq a, Eq b => Eq (Pair a b) where
  eq = \ x y . case x of
                 Pair x1 y1 -> case y of
                                Pair x2 y2 -> and (eq x1 x2) (eq y1 y2)

instance Eq a, Eq (Pair a (f (f a))) => Eq (HBush f a) where
  eq = \ x y . case x of
                 HBLeaf -> case y of
                            HBLeaf -> True
                            HBNode a -> False
                 HBNode a -> case y of
                              HBLeaf -> False
                              HBNode b -> eq a b

instance Eq (f (Mu f) a) => Eq (Mu f a) where
   eq = \ x y . case x of
                  In s -> case y of
 		            In t -> eq s t

-- lemma Eq x => Eq (HBush (Mu HBush) x)
-- lemma Eq x => Eq (Mu HBush x)

term1 = In HBLeaf

term2 = In (HBNode (Pair Unit term1))

-- test = eq term2 term1
test1 = eq term2 term2

-- test2 = eq a1 a1
reduce test1
-- reduce test1
-- reduce test2