module sing where
axiom D x (S y) => D (S x) y
axiom D (S m) Z => D Z m
lemma (forall n . D n (S m) => D m (S n)) => D Z m
-- lemma (forall n . D n (S m) => D (S m) n) => D Z m

-- b0 : (forall n . D n (S m') => D (S m') n)
-- D Z m' -a2-> D (S m') Z -b0-> D Z (S m') -rec-> (forall n . D n (S (S m')) => D (S (S m')) n)
-- b: D n' (S (S m'))-> D (S (S m')) n' -a1->  D (S m') (S n') -b0-> D (S n') (S m') -a1->
-- D n' (S (S m')) -b> 0

-- D Z Z -lemm-> (forall n . D n (S Z) => D (S Z) n) -- b :  D n' (S Z) -> D (S Z) n'
-- -a1-> D Z (S n') -lemm-> (forall n . D n (S (S n')) => D (S (S n')) n) -- b0 : D n'' (S (S n'))
-- -> D (S (S n')) n'' -a1 a1-> D n' (S (S n'')) -> 
-- There is a bug when I use the complicated lemma multiple times, I may wrongfully use 
-- not instantiate it to unique variable
-- 
lemma D Z Z
-- lemma D x
-- lemma D x => D (S x) 
-- lemma D (S )

-- axiom Eq (h1 (Mu h1 h2) (Mu h2 h1) a) => Eq (Mu h1 h2 a) 
-- axiom (Eq a, Eq (Pair (f1 a) (f2 a))) => Eq (H1 f1 f2 a)
-- axiom Eq (Pair (g a) (f (g a))) => Eq (H2 f g a) 
-- axiom (Eq a, Eq b) => Eq (Pair a b)
-- axiom Eq Unit

-- lemma (Eq x, Eq (Mu H2 H1 x)) => Eq (Mu H1 H2 x)
-- lemma (Eq x) => Eq (Mu H2 H1 x)
-- lemma (Eq x, Eq (Mu H2 H1 (Mu H1 H2 x))) => Eq (Mu H2 H1 x)
-- , Eq (Mu H2 H1 (Mu H1 H2 x))
-- lemma Eq (Mu H2 H1 Unit)