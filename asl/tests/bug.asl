module bug where
data Bool where
  true :: Bool
  false :: Bool

data N where
   zz:: N
   ss :: N -> N

data Times A B where
 times :: A -> B -> Times A B

f' = \ g . times (g true) (g false)

eq = \ x y . case x of
               zz -> case y of
                        zz -> true
                        ss n -> false
               ss n -> case y of
                         zz -> false
                         ss a -> eq n a
                        
f1 = \ g . g true zz
-- f2 = eq true zz
f3 = eq (zz) (ss zz)
reduce eq (zz) (ss zz)