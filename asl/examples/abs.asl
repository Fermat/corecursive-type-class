module abs where
axiom D n (S m) => D (S n) m
axiom D (S m) Z => D Z m
-- challenge: can you prove D Z Z corecursively from the above axiom? 
