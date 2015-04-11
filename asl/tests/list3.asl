module eq where

data List A where
  nil :: List A
  cons :: A -> List A -> List A

-- foldr = \ f a l . case l of
--                     nil -> a
--                     cons x xs -> f x (foldr f a xs)

foldr = let g = \ f a l . case l of
                    nil -> a
                    cons x xs -> f x (g f a xs)
            in g

-- zipWith = \ f l1 l2 . case l1 of
--                          nil -> nil
--                          cons x xs -> case l2 of
--                                         nil -> nil
--                                         cons y ys -> cons (f x y) (zipWith f xs ys) -- forget f
