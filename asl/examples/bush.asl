module bush where

axiom Eq (f (Mu f) a) => Eq (Mu f a)
axiom (Eq a, Eq (f (f a))) => Eq (HBush f a)
axiom Eq Unit
auto Eq (Mu HBush Unit)