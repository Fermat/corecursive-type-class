module principle where

data Unit where
  Unit :: Unit

data Maybe a where
  Nothing :: Maybe a
  Just :: a -> Maybe a

data HLam f a where
  HVar :: a -> HLam f a
  HApp :: (f a) -> (f a) -> HLam f a
  HAbs :: (f (Maybe a)) -> HLam f a

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

instance Eq a, Eq (f (Pair a a)) => Eq (HPTree f a) where
   eq = \ x y . case x of
                  HPLeaf s -> case y of
 		                HPLeaf t -> eq s t
                                HPNode p -> False
                  HPNode p -> case y of
                                HPLeaf t -> False
                                HPNode q -> eq p q


instance Eq (f (Mu f) a) => Eq (Mu f a) where
   eq = \ x y . case x of
                  In s -> case y of
 		            In t -> eq s t

instance Eq a => Eq (Maybe a) where
   eq = \ x y . case x of
                  Nothing -> case y of
 		               Nothing -> True
                               Just z1 -> False
                  Just z2 -> case y of
 		               Nothing -> False
                               Just z1 -> eq z2 z1
                               


instance Eq a, Eq (f a), Eq (f a), Eq (f (Maybe a)) => Eq (HLam f a) where
   eq = \ x y . case x of
                     HVar s -> case y of
 		                  HVar t -> eq s t
                                  HApp u1 u2 -> False
                                  HAbs u -> False
                     HApp p1 p2 -> case y of
                                    HVar t -> False
                                    HApp u1 u2 -> and (eq p1 u1) (eq p2 u2)
                                    HAbs u -> False
                     HAbs s1 -> case y of
                                    HVar t -> False
                                    HApp u1 u2 -> False
                                    HAbs u -> eq u s1

-- lemma Eq x => Eq (Mu HBush x)
-- lemma Eq x => Eq (Mu HPTree x)
-- lemma Eq x => Eq (Mu HLam x)

term1 = In HBLeaf

term2 = In (HBNode (Pair Unit term1))

test = eq term2 term1
test1 = eq term2 term2
-- test2 = eq a1 a1
reduce test
reduce test1
-- reduce test2

q1 = In (HPLeaf Unit)
test2 = eq q1 q1

reduce test2

q2 = In (HVar Unit)
test3 = eq q2 q2

reduce test3