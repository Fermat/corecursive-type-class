module seq where

axiom D n (S m) => D (S n) m
axiom D (S m) Z => D Z m

-- lemma (forall n . D n (S m) => D m (S n)) => D Z m
-- lemma (forall n . D n (S m) => D (S n) m) => D Z m
-- lemma D (S n) m => D m (S n)

lemma D (S n) Z => D Z (S n)


-- lemma D Z Z
-- axiom Pair b m => Add Z m b
-- axiom Add n (S m) b => Add (S n) m b
-- axiom (Nat a, Add a b b) => Pair a b
-- axiom Nat Z
-- axiom Nat n => Nat (S n)

-- lemma Pair Z (S Z)





-- axiom  D Z m => D (S m) Z
-- axiom (forall y . D y m => D m (S y)) => D Z m

-- axiom (forall y . D y n => D (S n) y ) => D (S n) Z

-- lemma D Z Z

-- lemma (forall y . D y x => D x (S y)) => D Z x
-- d(z(),x) -> d(s(x),z())
--  d(s(x),y) -> d(x,s(y))



-- axiom Eq Unit
-- axiom Eq (f (g a)) => Eq (Comp f g a)
-- axiom (Eq a, Eq a) => Eq (Pair a)
-- axiom (Eq a, Eq r) => Eq (GSeqF a r)
-- axiom Eq (f (Fix (Comp g f) g)) => Eq (Fix f g)
-- lemma (forall x . Eq x => Eq (f x)) => Eq (Fix f Pair)
-- lemma Eq (Fix Pair Pair)
-- lemma D Z Z
-- axiom D (S x) => D x

-- lemma D x => D (S x)
-- lemma D x (S Z) => D Z x
-- lemma (D Z x => D x (S Z)) => D Z x
-- lemma D Z Z
-- axiom (Eq x , Eq (List x)) => Eq (List x)

-- lemma Eq x => Eq (List x)
