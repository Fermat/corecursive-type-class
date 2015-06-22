module monad1 where


data Monad M where
  mc :: (forall A . A -> M A) -> (forall A B . M A -> (A -> M B) -> M B) -> Monad M

unit = \ x . case x of
              mc a b -> a

bind = \ x . case x of
               mc a b -> b

data List A where
  nil :: List A
  cons :: A -> List A -> List A

-- mapM :: Monad M -> (A -> M B) -> List A -> M (List B)
mapM = \ m f xs .
            case xs of
              nil -> unit m nil
              cons x xs -> 
                bind m (f x) (\ y . bind m (mapM m f xs) (\ ys . unit m (cons y ys)))