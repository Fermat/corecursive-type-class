module hughes where

data Bool where
  true :: Bool
  false :: Bool

class Collection C Cxt where
  empty :: Collection C Cxt, Cxt A => C A
  singleton :: Collection C Cxt, Cxt A => A -> C A
  union :: Collection C Cxt, Cxt A => C A -> C A -> C A
  member :: Collection C Cxt, Cxt A => A -> C A -> Bool