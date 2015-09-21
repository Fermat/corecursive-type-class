module d where

axiom (Eq x, Eq (D (D x))) => Eq (D x)
axiom Eq C 
lemma (Eq y) => Eq (D y)
