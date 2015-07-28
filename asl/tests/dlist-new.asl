module dlist where

data DList A where
 ni :: DList A
 con :: A -> (DList (DList A)) -> DList A
 
data Bool where
     true :: Bool
     false :: Bool

and = \ x y . case x of
                true -> y
		false -> false

data Nat where
  z :: Nat
  s :: Nat -> Nat

  
class Eq A where
   eq :: Eq A => A -> A -> Bool

instance Eq Nat => Eq Nat where
  eq = \ x y . case x of
                 z -> case y of
		         z -> true
			 s n -> false
	         s m -> case y of
                          z -> false
			  s n -> eq m n
   

                  
instance Eq A, Eq (DList (DList A)) => Eq (DList A) where
   eq = \ x y . case x of
                  con a as -> case y of
                                con b bs -> and (eq a b) (eq as bs)
                                ni -> false
                  ni -> case y of
                          con c cs -> false
                          ni -> true

-- lemma (forall B . Eq B => Eq (D B), forall X  . Eq X => Eq (F X)) => Eq (DList A)
-- lemma forall A . Eq A => Eq (DList A)

test = eq (con z (con (con z (con (con z ni) ni)) ni))  (con z (con (con z ni) ni))
reduce test
reduce eq (con z (con (con z (con (con z ni) ni)) ni)) (con z (con (con z (con (con z ni) ni)) ni))

-- (con z (con (con z (con (con z ni) ni)) ni))