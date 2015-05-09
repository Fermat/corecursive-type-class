module hughes where

data Bool where
  true :: Bool
  false :: Bool

-- a bug when I drop Cxt in the type of a method declaration

class Eq A where
   eq :: Eq A => A -> A -> Bool

class Ord A where
   le :: Ord A => A -> A -> Bool

class Self Cxt where
   what :: Self Cxt, Cxt A => A -> A -> Bool

instance => Self Self where
   what = \ x y . true
class Monad M Cxt where
   return :: Monad M Cxt, Cxt A => A -> M A
   bind :: Monad M Cxt, Cxt A, Cxt B => M A -> (A -> M B) -> M B 

f = return

class Collection C Cxt where
  empty :: Collection C Cxt, Cxt A => C A
  singleton :: Collection C Cxt, Cxt A => A -> C A
  union :: Collection C Cxt, Cxt A => C A -> C A -> C A
  member :: Collection C Cxt, Cxt A => A -> C A -> Bool