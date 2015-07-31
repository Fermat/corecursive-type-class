# functionalised-type-class
A functionalised implementation of type class

To install: cabal install

To run the interpreter and type checker for a file: asl filename

A simple language(called ASL) that support recursive definition and case expression,
algebraic data type, class declaration(without subtyping and superclass),
instance declaration. 

The implementation includes polymorphic type inference, type class resolution and
a naive version of interpreter.

ASL support guided corecursive evidence construction through the ''lemma'' mechanism, 
and sometimes this mechanism can be fully automized.

```haskell
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

lemma Eq Nat

lemma forall a . Eq a => Eq (DList a)

test = eq (Con Z (Con (Con Z (Con (Con Z Ni) Ni)) Ni))  (Con Z (Con (Con Z Ni) Ni))
test1 = eq (Con Z (Con (Con Z (Con (Con Z Ni) Ni)) Ni)) (Con Z (Con (Con Z (Con (Con Z Ni) Ni)) Ni))  

reduce test
reduce test1
```

The reduction for test above will return False and test1 return True. 