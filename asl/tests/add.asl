module add where


suc = \ n s z . s n
zero = \ s z . z
one = suc zero
two = suc (suc zero)
-- occur check will fail, meaning scott encoding is 
-- not typable
-- add = \ n m . n (\ y . add y m) m 