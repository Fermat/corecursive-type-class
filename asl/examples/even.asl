module even where

axiom (Eq a, Eq (EvenList a)) => Eq (OddList a)
axiom (Eq a, Eq (OddList a)) => Eq (EvenList a)
axiom Eq Int
-- lemma Eq (OddList Int) 
auto Eq (OddList Int)
