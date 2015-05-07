module add where

-- add1 = \ n m . n (\ y . add1 y m) m 
-- suc = \ n s z . s n
-- zero = \ s z . z
-- one = suc zero
-- two = suc (suc zero)
-- occur check will fail, meaning scott encoding is 
-- not typable
add = \ n m . let f = (\ y . add y m) in n f m 

-- for = add one zero
-- reduce for
-- reduce add two one