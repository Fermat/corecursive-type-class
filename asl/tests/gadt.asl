module gadts where

class TEq A B where
 iso :: TEq A B => A -> B
 soi :: TEq A B => B -> A

class Functor C where
  fmap :: Functor C => (A -> B) -> C A -> C B
  
compose  = \ f g x . f (g x) 

instance TEq A B, TEq B C => TEq A C where
  iso = compose iso iso

test = compose iso iso
-- test2 = \ a b . let ddict = cTEq (compose iso iso) in
--                     ddict

-- test3 = (\ x . x x) (\ x . x x) 