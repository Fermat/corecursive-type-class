module tom where
data Comp F G A where
   comp :: (F (G A)) -> Comp F G A

data Unit where
  unit :: Unit

data Pair A where
 pair :: A -> A -> Pair A

data GSeqF A R where
   nil :: GSeqF A R
   cons :: A -> R -> GSeqF A R

data Fix F G where
 fix ::  (F (Fix (Comp G F) G)) -> Fix F G

data Bool where
     true :: Bool
     false :: Bool

class Eq A where
   eq :: Eq A => A -> A -> Bool

and = \ x y . case x of
                true -> y
		false -> false

instance  => Eq Unit where
   eq = \ x y . case x of
                  unit -> case y of 
                             unit -> true


instance Eq (F (G A)) => Eq (Comp F G A) where
   eq = \ x y . case x of
                   comp s -> case y of 
                                comp t  ->  eq s t

instance Eq A, Eq A => Eq (Pair A) where
  eq = \ x y . case x of
                 pair x1 y1 -> case y of
                                pair x2 y2 -> and (eq x1 x2) (eq y1 y2)

instance Eq A, Eq R => Eq (GSeqF A R) where
    eq = \ x y . case x of
                    nil -> case y of
                             nil -> true
                             cons z zs -> false
                    cons q qs -> case y of
                                   nil  -> false
    				   cons z zs -> and (eq q z) (eq qs zs)

instance Eq (F (Fix (Comp G F) G)) => Eq (Fix F G) where
   eq = \ x y . case x of
                  fix s -> case y of
 		      	    fix t -> eq s t

test = eq (fix (cons unit (fix (comp (pair nil nil))))) (fix nil)
reduce eq (fix (cons unit (fix (comp (pair nil nil))))) (fix (cons unit (fix (comp (pair nil nil)))))
--  (fix nil)
reduce test
-- (fix nil)

