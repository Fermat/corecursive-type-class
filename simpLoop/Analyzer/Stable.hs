module Analyzer.Stable where
import Data.List
import Analyzer.Syntax
--import LPTM
import Analyzer.PrettyPrint
import Text.PrettyPrint
import Test.QuickCheck
import Control.Monad.State
import Debug.Trace



flatten (App t1 t2) = flatten t1 ++ [t2]
flatten t = [t]

unflatten (x:xs) = foldl App x xs

prop1 a = unflatten (flatten a) == a

prop2 [] = True
prop2 ((App _ _):xs) = True
prop2 ls@(_:xs) = flatten (unflatten ls) == ls

test1 = quickCheck prop1
test2 = quickCheck prop2

-- whether a term's spine is a functional variable 
isApp ((Var x):y:ys) = True
isApp _ = False

t3 = App (App (App (App (Var "NAK") (App Star Star)) (App (Var "A") (Var "2"))) Star) Star

-- whether a term contains any spine functional var
hasApp t = let args = map flatten $ tail $ flatten t
           in foldr (\ x y -> isApp x || y) False args

t5 = App (Pred "Eq") (App (App (App (Var "x") (App (Var "y") (App (Var "c") (Fun "f")))) (Var "z")) (Var "q"))
t6 = App (App (Pred "Eq")  (Var "x")) (App (Var "q") (Var "p"))
-- (App (App (Var "x") (Var "y")) (Var "z"))
runExtend t = evalState (extend t) 1
testExtend = disp $ runExtend t6
-- rule extension on a particular applicative argument
testInner = disp $ runInner (Pred "Eq") [] [] (Var "x") [(App (Var "y") (App (Var "c") (Fun "f"))), (Var "z"), (Var "q")]

runInner pred res pre fun l = evalState (inner pred res pre fun l) 1

inner pred res pre fun [] = return []
inner pred res pre fun (a:args) = do
  names <- makeNames "y" (a:args)
  let t = fun 
      c = foldl' (\ x y -> App x y) Star $ map Var names
      cxt = unflatten $ pred : (reverse pre ++ (c:res))
      rel = App (App (Pred "Xi") t) cxt
      x:xs = flatten a
  if isApp (x:xs)  then do
    ls' <- inner pred res pre x xs
    let r' = unflatten $ pred : (reverse pre ++ (a:res))    
        lss = map (\ (rs, t1) -> (rel:rs, t1)) ls'
    ls <- inner pred res pre (App fun a) args
    return $ (ls++lss)
    else do
      ls <- inner pred res pre (App fun a) args
      let r' = unflatten $ pred : (reverse pre ++ (a:res))    
      return $ ([rel], r'):ls

extend t = do
  let (l:ls) = flatten t
      pred = l 
  res <- genStable pred ls []
  return [ (rels, t') | (rels, t') <- res, not (hasApp t')]

genStable pred [] pre  = return []
genStable pred (r:rs) pre = 
  case flatten r of
    (Var x):y:ys -> do
        ls <- inner pred rs pre (Var x) (y:ys)
        ls' <- process ls
        return $ ls ++ ls'
    _ -> genStable pred rs (r:pre) 

process [] = return []
process ((rel,t):ts) = do
  ls <- extend t
  res <- process ts
  let a = map (\ (r, t') -> (rel++r, t')) ls
  return $ a++res
  
ruleExtension :: [Rule] -> [Rule]
ruleExtension rls =
  let rs = map right rls
      ls = map left rls
      news = map runExtend rs in
  rls ++ helper ls news
  where helper [] [] = []
        helper (x:xs) (ris:rss) =
          let n = map (\ (rels, t) -> Rule rels x t) ris in
          n ++ helper xs rss

t7 = App (Pred "Eq")
     (App (Var "F") (App (App (Fun "Fix") (App (App (Fun "Cmp") (Var "G")) (Var "F"))) (Var "G")))

r1 = Rule [] (App (Pred "Eq") (App (App (Fun "Fix") (Var "F")) (Var "G"))) t7
r2 = Rule [] (App (Pred "Eq") (App (App (App (Fun "Cmp") (Var "F")) (Var "G")) (Var "A")))
     (App (Pred "Eq") (App (Var "F") (App (Var "G") (Var "A"))))
     
r3 = Rule [] (App (Pred "Eq") (App (App (Fun "Gs") (Var "A")) (Var "R"))) (App (Pred "Eq") (Var "A"))     

r4 = Rule [] (App (Pred "Eq") (App (App (Fun "Gs") (Var "A")) (Var "R"))) (App (Pred "Eq") (Var "R"))     

r5 = Rule [] (App (Pred "Eq") (App (Fun "Pair") (Var "A"))) (App (Pred "Eq") (Var "A"))

tom = vcat $ map disp [r1, r2, r3, r4, r5]
exTom = vcat (map disp $ ruleExtension [r1, r2, r3, r4, r5])
axiomE = vcat (map disp $ axiomExtension (ruleExtension [r1, r2, r3, r4, r5]))
--forward ((x:xs), ys) = (xs, x:ys)
-- 
axiomExtension :: [Rule] -> [Form]
axiomExtension [] = []
axiomExtension ((Rule cs l r):rs) =
  case match r l of
    ((x,t):[]):[] ->
      case flatten t of
        (a:b:as) ->
          let (left, right) = break (== x) (b:as) in
          if null right then axiomExtension rs
          else let apps = foldl' (\ x y -> App x y) Star right
                   focus = foldl' (\ x y -> App x y) a left
                   (left', t':right') = break (== t) (flatten l)
                   cxt = unflatten $ left' ++ (apps:right')
                   rel = App (App (Pred "Xi") focus) cxt
                   rule = Form rel cs 
               in rule : axiomExtension rs 
        _ -> axiomExtension rs
    _ -> axiomExtension rs
          
          
      
  -- if length zs == 1 then
  --   case 
  --   else axiomExtension rs
