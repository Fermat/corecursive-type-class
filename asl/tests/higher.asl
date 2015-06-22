module higher where
-- SPJ: higher rank types

data Incr V where
  zero :: Incr V
  succ :: V -> Incr V
  
data Term V where 
  var :: V -> Term V 
  app :: Term V -> Term V -> Term V
  lam :: (Term (Incr V)) ->  Term V

fixMT :: ((forall A B . (A -> B) -> Term A -> Term B) -> (forall A B . (A -> B) -> Term A -> Term B)) -> (forall A B . (A -> B) -> Term A -> Term B)
fixMT = \ f . f (fixMT f)

mapI :: (A -> B) -> Incr A -> Incr B
mapI = \ f s . case s of
                 zero -> zero
                 succ x -> succ (f x)

-- It does not work because in this case one has to instantiate lambda bound type...
-- mapT :: forall A B . (A -> B) -> Term A -> Term B
mapT = fixMT (\ mt . \ f t .
                      case t of
                         var x -> var (f x)
                         app t1 t2 -> app (mt f t1) (mt f t2) 
                         lam t -> lam (mt (mapI f) t))



-- g : U -> U
-- f : (forall Y . Y) -> U
-- (forall Y . Y)
-- (forall Z . Z)
-- (forall A . A -> M A ) ~ (forall Z . Z -> M Z)
