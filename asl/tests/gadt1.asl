module gadts where
class TEq A B where
 iso :: TEq A B => C A -> C B
 soi :: TEq A B => C B -> C A

compose  = \ f g x . f (g x) 

instance TEq A B, TEq B C => TEq A C where
  iso = compose iso iso
  soi = compose soi soi

