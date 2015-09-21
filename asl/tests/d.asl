module d where

axiom  Eq Nat
axiom ( Eq a, Eq (DList (DList a)) ) => Eq (DList a)

auto Eq (DList Nat)

-- axiom (Eq x, Eq (D (D x))) => Eq (D x)
-- axiom Eq C 
-- lemma (Eq y) => Eq (D y)
-- auto Eq (D C)

-- [("Ax1",FApp (Con "Eq") (Con "Nat")),("Ax0",Imply [FApp (Con "Eq") (EVar "a"),FApp (Con "Eq") (FApp (Con "DList") (FApp (Con "DList") (EVar "a")))] (FApp (Con "Eq") (FApp (Con "DList") (EVar "a"))))]

-- [("e35",Imply [FApp (Con "Eq") (EVar "a"),FApp (Con "Eq") (FApp (Con "DList") (FApp (Con "DList") (EVar "a")))] (FApp (Con "Eq") (FApp (Con "DList") (EVar "a")))),("e14",Imply [] (FApp (Con "Eq") (Con "Nat")))]