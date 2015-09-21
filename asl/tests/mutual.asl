module mutual where

data Unit where
  Unit :: Unit

data Maybe a where
  Nothing :: Maybe a
  Just :: a -> Maybe a

data Pair a b where
 Pair :: a -> b -> Pair a b

data Bool where
     True :: Bool
     False :: Bool

data H1 f1 f2 a where
  H1 ::  a -> (Pair (f1 a) (f2 a)) -> H1 f1 f2 a
  Nil :: H1 f1 f2 a

data H2 f g a where
  H2 :: Pair (g a) (f (g a)) -> H2 f g a

data Mu h1 h2 a where
  In :: (h1 (Mu h1 h2) (Mu h2 h1) a) -> Mu h1 h2 a

class Eq a where
   eq :: Eq a => a -> a -> Bool

and = \ x y . case x of
                True -> y
		False -> False

instance  => Eq Unit where
   eq = \ x y . True

instance Eq a, Eq b => Eq (Pair a b) where
  eq = \ x y . case x of
                 Pair x1 y1 -> case y of
                                Pair x2 y2 -> and (eq x1 x2) (eq y1 y2)


instance Eq (h1 (Mu h1 h2) (Mu h2 h1) a) => Eq (Mu h1 h2 a) where
   eq = \ x y . case x of
                  In s -> case y of
 		            In t -> eq s t

instance Eq (Pair (g a) (f (g a))) => Eq (H2 f g a) where
   eq = \ x y . case x of
                  H2 s -> case y of
 		            H2 t -> eq s t

instance Eq a, Eq (Pair (f1 a) (f2 a)) => Eq (H1 f1 f2 a) where
   eq  = \ x y . case x of
                     Nil -> case y of
                             Nil -> True
 		             H1 s' t -> False
                     H1 s p -> case y of
                                 Nil -> False
 		                 H1 s1 p1 -> and (eq s1 s) (eq p p1)


-- lemma (Eq x, Eq (Mu H2 H1 x)) => Eq (Mu H1 H2 x)
-- lemma Eq x => Eq (Mu H2 H1 x)
-- lemma Eq (Mu H1 H2 Unit)

lemma (Eq x, Eq (Mu h2 H1 x)) => Eq (Mu h1 H2 x)
lemma Eq x => Eq (Mu H2 H1 x)

