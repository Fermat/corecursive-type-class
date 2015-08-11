module hfix where
data H f a where
   H ::  (f a) -> (f a) -> H f a

data Unit where
  Unit :: Unit

data Pair a where
 Pair :: a -> a -> Pair a

data GSeqF a r where
   Nil :: GSeqF a r
   Cons :: a -> r -> GSeqF a r

data HFix h f where
 In :: (f (HFix h (h f))) -> HFix h f

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

instance Eq a, Eq a => Eq (Pair a) where
  eq = \ x y . case x of
                 Pair x1 y1 -> case y of
                                Pair x2 y2 -> and (eq x1 x2) (eq y1 y2)

instance Eq a, Eq r => Eq (GSeqF a r) where
    eq = \ x y . case x of
                    Nil -> case y of
                             Nil -> True
                             Cons z zs -> False
                    Cons q qs -> case y of
                                   Nil  -> False
    				   Cons z zs -> and (eq q z) (eq qs zs)

instance Eq (f (HFix h (h f))) => Eq (HFix h f) where
   eq = \ x y . case x of
                  In s -> case y of
 		            In t -> eq s t

-- lemma (forall x . Eq x => Eq (f x)) => Eq (Fix f Pair)
lemma (forall x . Eq x => Eq (f x), forall x . Eq x => Eq (f x)) => Eq (HFix h f)

-- test = eq (Fix (Cons Unit (Fix (Comp (Pair Nil Nil))))) (Fix Nil)
-- test1 = eq (Fix (Cons Unit (Fix (Comp (Pair Nil Nil))))) (Fix (Cons Unit (Fix (Comp (Pair Nil Nil)))))
-- reduce eq (Fix (Cons Unit (Fix (Comp (Pair Nil Nil))))) (Fix (Cons Unit (Fix (Comp (Pair nil nil)))))
--  (fix nil)
-- reduce test
-- reduce test1
-- (fix nil)

