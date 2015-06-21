module gmap where

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
                  cons x xs -> cons (f x) xs

g = g
-- turns out it is a bug in the type checker.
zipWith :: (A -> B -> C) -> List A -> List B -> List C
zipWith = \ f l1 l2 . case l1 of
                         nil -> nil
                         cons x xs -> case l2 of
                                        nil -> nil
                                        cons y ys -> cons (f x y) (zipWith f xs ys) -- forget f

foldr = \ f a l . case l of
                    nil -> a
                    cons x xs -> f x (foldr f a xs)

data Nat where
  z :: Nat
  s :: Nat -> Nat

data Nested A where
  ep :: Nested A
  con :: A -> Nested (List A) -> Nested A

len :: Nested A -> Nat
len = \ x . case x of 
             ep -> z
             con a b -> s (len b)

-- reduce test1
-- class Data C A where
--   gmapQ :: Data C A, Eq E B => (forall B . Data C B => B -> R) -> A -> List R

-- f :: forall A . (A -> A) -> List A -> List A

