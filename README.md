# corecursive-type-class
A implementation of type class mechanism based on corecursive resolution

To install: cabal install

To run the interpreter and type checker for a file: asl `filename`

A simple language(called ASL) that support recursive definition and simple case expression,
algebraic data type, simple class declaration and instance declaration. 

The current implementation includes polymorphic type inference, type class resolution and
a naive version of interpreter(through the *reduce* keyword).

ASL support guided corecursive evidence construction through the ''lemma'' mechanism, 
and sometimes this mechanism can be fully automized.

Some remarks: lambda abstraction is slash-dot instead of slash-arrow, e.g.
`(\ x . x x) (\ x . x x)`. Data declaration is only available using GADTs(which we does not support yet) convention. Currently no type annotation is allowed for function. To achieve direct experimentation on resolution, we recommend using the keyword *axiom* to introduce an axiom and *lemma* to use the existing axioms to prove the lemma, once it is proven, it will be stored and can be used later. Examples are in the `examples` directory.

The following is a direct experiment on resolution.
```haskell
module experiment where

axiom (Eq x, Eq (D (D x))) => Eq (D x)

axiom Eq Char

lemma Eq x => Eq (D x)

lemma Eq (D Char)
```


The following is an more concrete example.
```haskell
module principle where

data Unit where
  Unit :: Unit

data Pair a b where
 Pair :: a -> b -> Pair a b

data HBush f a where
  HBLeaf :: HBush f a
  HBNode :: Pair a (f (f a)) -> HBush f a

data HPTree f a where
  HPLeaf :: a -> HPTree f a
  HPNode :: f (Pair a a) -> HPTree f a  

data Mu f a where
  In :: f (Mu f) a -> Mu f a
  
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

instance Eq a, Eq b => Eq (Pair a b) where
  eq = \ x y . case x of
                 Pair x1 y1 -> case y of
                                 Pair x2 y2 -> and (eq x1 x2) (eq y1 y2)

instance Eq (Pair a (f (f a))) => Eq (HBush f a) where
  eq = \ x y . case x of
                 HBLeaf -> case y of
                            HBLeaf -> True
                            HBNode a -> False
                 HBNode a -> case y of
                              HBLeaf -> False
                              HBNode b -> eq a b

instance Eq (f (Mu f) a) => Eq (Mu f a) where
   eq = \ x y . case x of
                  In s -> case y of
 		            In t -> eq s t

term1 = In HBLeaf
term2 = In (HBNode (Pair Unit term1))
test1 = eq term2 term2
reduce test1

```


