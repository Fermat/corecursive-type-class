module maybe where

data Bool where
  true :: Bool
  false :: Bool

data Monad M where
  mc :: (forall A . A -> M A) -> (forall A B . M A -> (A -> M B) -> M B) -> Monad M
  
-- class Monad M where
--    return :: Monad M => A -> M A
--    bind :: Monad M => M A -> (A -> M B) -> M B

-- data Maybe A where
--   nothing :: Maybe A
--   just :: A -> Maybe A

-- instance => Monad Maybe where
--   return = just
--   bind = \ x f . case x of
--                     just a -> f a
--                     nothing -> nothing
