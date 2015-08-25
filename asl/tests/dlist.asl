module dlist where

data DList a where
 Ni :: DList a
 Con :: a -> (DList (DList a)) -> DList a
 
data Bool where
     True :: Bool
     False :: Bool

and = \ x y . case x of
                True -> y
		False -> False

data Nat where
  Z :: Nat
  S :: Nat -> Nat

  
class Eq a where
   eq :: Eq a => a -> a -> Bool

myeq = \ x y . case x of
                  Z -> case y of
 		         Z -> True
 			 S n -> False
 	          S m -> case y of
                          Z -> False
     			  S n -> myeq m n
   
instance Eq Nat => Eq Nat where
  eq = \ x y . case x of
                 Z -> case y of
		         Z -> True
			 S n -> False
	         S m -> case y of
                          Z -> False
			  S n -> eq m n
   
                
instance Eq a, Eq (DList (DList a)) => Eq (DList a) where
   eq = \ x y . case x of
                  Con a as -> case y of
                                Con b bs -> and (eq a b) (eq as bs)
                                Ni -> False
                  Ni -> case y of
                          Con c cs -> False
                          Ni -> True

test = eq (Con Z (Con (Con Z (Con (Con Z Ni) Ni)) Ni))  (Con Z (Con (Con Z Ni) Ni))
reduce test
reduce eq (Con Z (Con (Con Z (Con (Con Z Ni) Ni)) Ni)) (Con Z (Con (Con Z (Con (Con Z Ni) Ni)) Ni))

-- (con z (con (con z (con (con z ni) ni)) ni))
