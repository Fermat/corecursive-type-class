module poly where

data Nat where
  z :: Nat
  s :: Nat -> Nat

data List U where
  nil :: List U
  cons :: U -> List U -> List U

data Pair U V where
  times :: U -> V -> Pair U V

id = \ x . x
c = id
exp = let x = id in x

bb = \ x y z . x z (y z)

bb1 = \ x y . x
cc = bb bb1 bb1
aa = let ss = \ x y z . x z (y z)
         kk = \ x y . x
        in ss kk kk




zip1  = \ b e. case b of
                nil -> nil
                cons a t -> case e of
		       	      nil -> nil
                              cons b t' -> cons (times a b) (zip1 t t')

-- zip2 = \ b e . case b of
--                  nil -> case e of
--                           nil -> nil
--                  cons a t -> case e of
--                                cons q t' -> zip2 t t'