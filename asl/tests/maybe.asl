module maybe where
-- Type checking Mark Jones's examples

data Bool where
  true :: Bool
  false :: Bool

data Monad M where
  mc :: (forall A . A -> M A) -> (forall A B . M A -> (A -> M B) -> M B) -> Monad M

unit = \ x . case x of
              mc a b -> a

bind = \ x . case x of
               mc a b -> b

join  = \ m xss . bind m xss (\ x . x)               


data Maybe A where
  nothing :: Maybe A
  just :: A -> Maybe A

unit' = \ x . just x

bind' = \ x f . case x of 
                 nothing -> nothing
                 just y -> f y
                 
maybeMonad = mc unit' bind' 

data Church where
  ch :: (forall A . (A -> A) -> A -> A) -> Church

unCh = \ x . case x of ch y -> y

zero = ch (\ f x . x)
one = ch (\ f x . f x)

suc = \ n . ch (\ f x . unCh n f (f x))

isZ = \ n . unCh n (\ x . false) true

add = \ n m . unCh n suc m

mult = \ n m . unCh n (add m) zero

data Times A B where
 times :: A -> B -> Times A B

fst = \ x . case x of times a b -> a

s' = \ a . case a of times x y -> times y (suc y)
z' = times zero zero

pred = \ n . fst (unCh n s' z')

-- data List A where
--  cl :: (forall B . (A -> B -> B) -> B -> B) -> List A

-- fold = \ x . case x of cl f -> f

-- nil = cl (\ c n . n)
-- cons = \ x xs . cl (\ c n . c x (fold xs c n))

-- hd = \ l . fold l (\ x xs . x) zero

-- c' = \ x y . case y of times l t -> times t (cons x t)
-- n' = times nil nil
-- tl = \ l . fst (fold l c' n')

data List A where
  nil :: List A
  cons :: A -> List A -> List A

append = \ l1 l2 . case l1 of
                     nil -> l2
                     cons x xs -> cons x (append xs l2)
                     
lUnit = \ x . cons x nil
lBind = \ l f . case l of
                 nil -> nil
                 cons x xs -> append (f x) (lBind xs f)
listM = mc lUnit lBind

-- class Monad M where
--    return :: Monad M => A -> M A
--    bind :: Monad M => M A -> (A -> M B) -> M B


-- instance => Monad Maybe where
--   return = just
--   bind = \ x f . case x of
--                     just a -> f a
--                     nothing -> nothing
