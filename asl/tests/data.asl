module eq where

data Bool where
  True :: Bool
  False :: Bool

and = \ x y . case x of
                True -> y
		False -> False

data Nat where
  Z :: Nat
  S :: Nat -> Nat

myeq = \ x y . case x of
                  Z -> case y of
 		         Z -> True
 			 S n -> False
 	          S m -> case y of
                          Z -> False
     			  S n -> myeq m n

data List a where
  Nil :: List a
  Cons :: a -> List a -> List a

class Eq a where
   eq :: Eq a => a -> a -> Bool

instance Eq Nat => Eq Nat where
--   eq = myeq
  eq = \ x y . case x of
                 Z -> case y of
        	         Z -> True
        		 S n -> False
                 S m -> case y of
                          Z -> False
        		  S n -> eq m n

instance Eq a, Eq (List a) => Eq (List a) where
   eq = \ l1 l2 . case l1 of
                    Nil -> case l2 of
                             Nil -> True
			     Cons y ys -> False
                    Cons x xs -> case l2 of
		                   Nil -> False
				   Cons y ys -> and (eq x y) (eq xs ys)
-- lemma Eq Nat 
-- lemma Eq a => Eq (List a)

-- lemma Eq (List Nat)
test = eq (Cons Z Nil) (Cons Z (Cons Z Nil))
test1 = eq (Cons Z (Cons Z Nil)) (Cons Z (Cons Z Nil))
reduce test
-- reduce test1

-- test = eq Z (S Z)
-- reduce test