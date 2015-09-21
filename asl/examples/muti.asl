module muti where

axiom (Eq a, Eq (Pair (f1 a) (f2 a))) => Eq (H1 f1 f2 a)
axiom Eq (Pair (g a) (f (g a))) => Eq (H2 f g a)
axiom Eq (h1 (Mu h1 h2) (Mu h2 h1) a) => Eq (Mu h1 h2 a)
axiom (Eq a, Eq b) => Eq (Pair a b)
axiom Eq Unit
lemma (Eq x, Eq (Mu H2 H1 x)) => Eq (Mu H1 H2 x)
lemma Eq x => Eq (Mu H2 H1 x)
lemma Eq (Mu H1 H2 Unit)
-- auto Eq (Mu H1 H2 Unit)