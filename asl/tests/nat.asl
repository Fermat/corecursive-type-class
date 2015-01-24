module nat where
zero = \ z s . z
succ = \ n z s . s n
one = succ zero
two = succ (succ zero)
add = \ x y . x y (\ n . add n (succ y))
test = two two
reduce test