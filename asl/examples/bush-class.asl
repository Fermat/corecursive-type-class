module bush where
data Unit where
  Unit :: Unit

data Maybe a where
  Nothing :: Maybe a
  Just :: a -> Maybe a

data Pair a b where
 Pair :: a -> b -> Pair a b

data HBush f a where
  HBLeaf :: HBush f a
  HBNode ::  a -> (f (f a)) -> HBush f a

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

instance Eq a, Eq (f (f a)) => Eq (HBush f a) where
  eq = \ x y . case x of
                 HBLeaf -> case y of
                            HBLeaf -> True
                            HBNode a c -> False
                 HBNode a c1 -> case y of
                              HBLeaf -> False
                              HBNode b c2  -> and (eq a b) (eq c1 c2)

instance Eq (f (Mu f) a) => Eq (Mu f a) where
   eq = \ x y . case x of
                  In s -> case y of
 		            In t -> eq s t


term1 = In HBLeaf

term2 = In (HBNode Unit term1)

test = eq term2 term1
test1 = eq term2 term2
reduce test
reduce test1
