module monad where

class Monad M where
    bind :: Monad M => M A -> (A -> M B) -> M B
    return :: Monad M => A -> M A  

data Maybe A where
  nothing :: Maybe A
  just :: A -> Maybe A

instance => Monad Maybe where
   bind = \ x f . case x of
                     just a -> f a
                     nothing -> nothing
   return = just