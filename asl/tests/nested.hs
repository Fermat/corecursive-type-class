{-#LANGUAGE GADTs, FlexibleContexts, UndecidableInstances #-}
data Unit where
  Unit :: Unit

data Pair a b where
 Pair :: a -> b -> Pair a b

data H1 f1 f2 a = H1 a (Pair (f1 a) (f2 a)) | Nil
data H2 f1 f2 a = H2 (f1 (f2 a))

data Mu h1 h2 a where
  In :: (h1 (Mu h1 h2) (Mu h2 h1) a) -> Mu h1 h2 a


instance (Eq a, Eq b) => Eq (Pair a b) where
  (==) = \ x y -> case x of
                 Pair x1 y1 -> case y of
                                Pair x2 y2 ->  (x1 == x2) && (y1 == y2)

instance Eq (h1 (Mu h1 h2) (Mu h2 h1) a) => Eq (Mu h1 h2 a) where
   (==) = \ x y -> case x of
                  In s -> case y of
 		            In t -> s == t

instance Eq (f1 (f2 a)) => Eq (H2 f1 f2 a) where
   (==) = \ x y -> case x of
                  H2 s -> case y of
 		            H2 t -> s == t

instance (Eq a, Eq (f1 a), Eq (f2 a)) => Eq (H1 f1 f2 a) where
   (==) = \ x y -> case x of
                     Nil -> case y of
                             Nil -> True
 		             H1 s' t -> False
                     H1 s p -> case y of
                                 Nil -> False
 		                 H1 s1 p1 -> s1 == s && p == p1

a1 :: Mu H1 H2 Unit
a1 = undefined

test = a1 == a1
