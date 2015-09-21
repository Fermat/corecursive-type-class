module lam where
axiom Eq (f (Mu f) a) => Eq (Mu f a)
axiom (Eq a, Eq (f a), Eq (f a), Eq (f (Maybe a))) => Eq (HLam f a)
axiom Eq Unit
axiom Eq a => Eq (Maybe a)
lemma (Eq x) => Eq (Mu HLam x)
lemma Eq (Mu HLam Unit)
-- one can replace the above two lemmas with 
-- the following auto
-- auto Eq (Mu HLam Unit)