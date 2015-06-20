module gmap where

data List A where
  nil :: List A
  cons :: A -> List A -> List A

class Data C A where
  gmapQ :: Data C A, Eq E B => (forall B . Data C B => B -> R) -> A -> List R

f :: forall A . (A -> A) -> List A -> List A