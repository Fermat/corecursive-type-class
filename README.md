# functionalised-type-class
A functionalised implementation of type class

To install: cabal install

To run the interpreter and type checker for a file: asl <filename>

A simple language(called ASL) that support recursive definition and case expression,
algebraic data type, class declaration(without subtyping and superclass),
instance declaration. 

The implementation includes polymorphic type inference, type class resolution and
a naive version of interpreter.

Type class resolution is lazy, namely, evidence of a type class will not be 
constructed until it is needed. Through laziness, ASL can support corecursive
evidence, i.e., the evidence construction involves infinite steps.

```haskell
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

test = eq (con z (con (con z (con (con z ni) ni)) ni))  (con z (con (con z ni) ni))

reduce test 
```

The reduction for test above will return false. 