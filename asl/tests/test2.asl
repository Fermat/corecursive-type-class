module test2 where

-- axiom (Eq x, Eq (D x), Eq (D (D (D x))), Eq (D (D (D (D x)))) ) => Eq (D (D x))

-- lemma (Eq (D x), Eq x) => Eq (D (D x)) 

axiom (Eq x, Eq (D x), Eq (D (D (D x))), Eq (D (D (P x)))) => Eq (D (D x))
axiom Eq x => Eq (D (P x))
axiom Eq x => Eq (P x)

lemma (Eq x, Eq (D x)) => Eq (D (D x))


-- \ b0 . \ b1 . Ax0 b1 b0 (lem1 (lem1 b0 b1) b0) (lem1 (lem1 (lem1 b0 b1) b0) (lem1 b0 b1)) 

-- \ b0 . \ b1 . Ax0 b0 b1 (lem1 b1 (lem1 b0 b1)) (lem1 (lem1 b0 b1) (lem1 b1 (lem1 b0 b1))) 