module eq where

data List A where
  nil :: List A
  cons :: A -> List A -> List A

data Bool where
     true :: Bool
     false :: Bool

and = \ x y . case x of
                true -> y
		false -> false

map = \ f l . case l of
                  nil -> nil
                  cons x xs -> cons (f x) (map f xs)

zipWith = \ f l1 l2 . case l1 of
                         nil -> case l2 of
                                   nil -> nil
                                   cons z zs -> cons false nil 
                         cons x xs -> case l2 of
                                        nil -> cons false nil
                                        cons y ys -> cons (f x y) (zipWith f xs ys)

foldr = \ f a l . case l of
                    nil -> a
                    cons x xs -> f x (foldr f a xs)

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

instance Eq A => Eq (List A) where
       eq = \ l1 l2 . foldr (\ x y . and x y) true (zipWith eq l1 l2)

-- found a bug in the evaluator and type checker.. 
test1 =  eq (cons (s z) (cons z nil)) (cons z (cons z (cons z nil)))
-- 
-- 

--reduce test1