module collect where
class Collect A C where
 empty :: Collect A C => C
 insert :: Collect A C => A -> C -> C


f = \ x y c . insert x (insert y c)

init = \ x . insert x empty