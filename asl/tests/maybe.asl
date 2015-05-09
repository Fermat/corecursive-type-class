module maybe where

data Bool where
  true :: Bool
  false :: Bool

class Monad M where
   return :: Monad M => A -> M A
   bind :: Monad M => M A -> (A -> M B) -> M B

data Maybe A where
  nothing :: Maybe A
  just :: A -> Maybe A

instance => Monad Maybe where
  return = just
  bind = \ x f . case x of
                    just a -> f a
                    nothing -> nothing
