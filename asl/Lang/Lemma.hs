-- | Construction of an Intermediate Lemma
-- author: Andrew Pond
module Lang.Lemma where
import Lang.Examples
import Lang.RTree
import Lang.Functionalisation
import Lang.Syntax hiding(flatten)
import Lang.AntiUnify
import Data.Maybe(fromJust, catMaybes, mapMaybe)
import Data.List(delete, nub)
import Data.Tree(Tree(..), flatten)
import Control.Monad(join, liftM2)
import Debug.Trace

fixLemma e p tmp = case (constructLemma e p) of
                    [] -> tmp
                    l -> let ns = map (\ x -> "a" ++ show x) [1 .. length l]
                             l' = zip ns l in
                         fixLemma e (l' ++ p) (tmp ++ l)
                  
-- | Given an expression and a program, construct an Intermediate Lemma
constructLemma :: Exp -> Program -> [Exp]
constructLemma e prog = map assembleLemma hasLoopNodes
  where rt = constructRTree e prog
        loops = map getLoops (findLoops rt)
        adjLoops = map (map adjustLoop) loops
        absTrees = abstractTrees rt loops prog
        hasLoopNodes = catMaybes $ zipWith containsLoops absTrees adjLoops

-- | Given an expression and a program, construct an Intermediate Lemma alongside
-- each step of the construction.
constructLemma' :: Exp -> Program -> (RTree Exp,[([RTNode Exp],RTree Exp)],[RTree Exp],[([(Seq, Exp)], Exp)])
constructLemma' e prog = (rt, findLoops' rt, absTrees, lemmas )
  where rt = constructRTree e prog
        loops = map getLoops (findLoops rt)
        adjLoops = map (map adjustLoop) loops
        absTrees = abstractTrees rt loops prog
        hasLoopNodes = catMaybes $ zipWith containsLoops absTrees adjLoops
        lemmas = map assembleLemma' hasLoopNodes

-- | Given a Abstract RTree paired with a list of loops, construct a lemma
assembleLemma:: (RTree Exp, [Loop]) -> Exp
assembleLemma (rt, loops) = Imply b h
  where h = fromJust $ expr $ rootLabel rt
        b = map (fromJust . expr) loopless
        loopless = nub $ removeLoops loops ls -- probably needless (covered by extLeaves)
        ls = extLeaves rt

assembleLemma' :: (RTree Exp, [Loop]) -> ([(Seq, Exp)], Exp)
assembleLemma' (rt, loops) = ([(hid,h)] ++ (zip bid b) ,Imply b h)
  where h = fromJust $ expr $ rootLabel rt
        hid = idx $ rootLabel rt
        b = map (fromJust . expr) loopless
        bid = map idx loopless
        loopless = nub $ removeLoops loops ls -- probably needless
        ls = extLeaves rt

-- | Given an expression and a program, construct an Intermediate Lemma includes
-- matchability test.
consMatchableLemma :: Exp -> Program -> [(Bool, Exp)]
consMatchableLemma e prog = lemma
  where rt = constructRTree e prog
        loops = map getLoops (findLoops rt)
        adjLoops = map (map adjustLoop) loops
        absTrees = abstractTrees rt loops prog
        hasLoopNodes = catMaybes $ zipWith containsLoops absTrees adjLoops
        lemma =  map (flip assembleMatchableLemma prog) hasLoopNodes

-- | Given an Abstract RTree paired with a list of loops, check if the lemma is
-- provable and construct the lemma
assembleMatchableLemma :: (RTree Exp, [Loop]) -> Program -> (Bool, Exp)
assembleMatchableLemma d@(rt, loops) prog =
  case and (map fst3 checked) of
    True  -> (True, assembleLemma d)
    False -> case or (map fst3 checked) of
               False -> (False, assembleLemma d)
               True  -> (False, assembleLemma d) -- THis case can be expanded in future to handle situations with mutual recursion
  where checked = map (matchability rt prog) loops

-- | Check that the head of the loop is matchable with the end of the of the loop
-- and that the resulting trees all satisfy the other  matchability conditions.
matchability :: RTree Exp -> Program -> Loop -> (Bool, Seq, Exp)
matchability rt prog l@(_, sid, eid) =
  case sub of
    Nothing -> (False, eid, loopEnd)
    Just s  -> let subbed = map (fmap (applyE s)) ls
                   es = zip oes (map (fromJust . expr) subbed)
                   noMatch = filter (\(_,b) -> not $ isMatchable loopHead b) es
               in  (checkMatch loopHead noMatch prog, eid, loopEnd)
  where loopHead = fromJust $ join $ fmap expr $ lookupTree sid rt
        loopEnd  = fromJust $ join $ fmap expr $ lookupTree eid rt
        sub = matchLoop rt l
        ls = extLeaves rt
        oes = map (fromJust . expr) ls

-- | Given an Expression (loop head before substituion), a list of pairs of
-- expressions (Before and after substituion) and the program check that al pairs
-- satsify matchability checks.
checkMatch :: Exp -> [(Exp,Exp)] -> Program -> Bool
checkMatch lh es prog = and $ map (singleCheck lh) (zip (map fst es) trees)
  where trees = map (flip constructAbstractTree prog) (map snd es)

-- | Given an Expresion (The head of the loop before substitution) and a pair
-- of expression (root of the RTree before subsititon) and RTree constructed from
-- the expersion where the substituion has been applied, check if matchability is
-- satisfied.
singleCheck :: Exp -> (Exp,RTree Exp) -> Bool
singleCheck lh (e, rt) = and (checks ++ lhMatch)
  where als = allLeaves rt
        problematic = filter (isProblematic) als
        nonProblematic = filter (not . isProblematic) als
        lhMatch = map (isMatchable lh) (map (fromJust . expr) problematic)
        checks = map (\l -> expr l == Just e) nonProblematic

-- | Given a tree and a loop, match the head and end of the loop
matchLoop :: RTree Exp -> Loop -> Maybe [(VName, Exp)]
matchLoop rt (_,sid,eid) = mt
  where st = join $ fmap expr $ lookupTree sid rt
        en = join $ fmap expr $ lookupTree eid rt
        mt = join $ liftM2 match st en

-- | Is the first expresion matchable with the second.
isMatchable :: Exp -> Exp -> Bool
isMatchable e1 e2 = case match e1 e2 of
                      Nothing -> False
                      _       -> True

-- | Does the RTree contain no loops
noLoops :: RTree Exp -> Bool
noLoops rt =
  case filter (isProblematic) nodes of
    [] -> True
    _  -> False
  where nodes = flatten rt

-- | Given a RTree and a list of list of loops construct abstract trees for each
-- list of loops
abstractTrees :: RTree Exp -> [[Loop]] -> Program  -> [RTree Exp]
abstractTrees rt loops prog = map (flip constructAbstractTree prog) antiunifiers
  where antiunifiers = map (antiunifier rt) loops

-- | Given a Tree and a list of loops return the least general antiunifier
antiunifier :: RTree Exp -> [Loop] -> Exp
antiunifier rt l = foldl antiUnify st ends
  where (st, ends) = loopExp rt l

-- | Given a Tree and a list of loops return the expresions at the start of the
-- loop and a list of all expresions at the end of the loop
loopExp :: RTree Exp -> [Loop] -> (Exp, [Exp])
loopExp rt ls = (start, ends)
  where (_,st,_) = ls !! 0
        start = fromJust $ join $ fmap expr (lookupTree st rt)
        nodes = mapMaybe (flip lookupTree rt) (map thd3 ls)
        ends  = catMaybes $ map expr nodes

-- | Given an expresion and a program construct a RTree
constructAbstractTree :: Exp -> Program -> RTree Exp
constructAbstractTree e prog = constructTree (not . extendableTree) exhaustiveMatch root prog
  where root = newRoot e

-- | Given a list of leaves and a program return the ID of the next node to
-- expand, the clause matched against and a list of substitutions. Proceeding
-- to the next leaf until a match is found or there are no more leaves
exhaustiveMatch :: [RTNode Exp] -> Program -> Maybe Match
exhaustiveMatch [] _ = Nothing
exhaustiveMatch (x:xs) prg =
  case expr x of
    Nothing -> exhaustiveMatch xs prg
    Just e  -> case matchNode (idx x) e prg of
                      Nothing -> exhaustiveMatch xs prg
                      sub     -> sub

-- | Given a RTree and a list of loops check the tree contains the end nodes in the loop
containsLoops :: RTree Exp -> [Loop] -> Maybe (RTree Exp, [Loop])
containsLoops rt ls =
  case contains of
    True  -> Just (rt, ls)
    False -> Nothing
  where contains = and (map (\(_,_,ed) -> subTree ed rt /= Nothing) ls)

-- | Given a list of loops and list of nodes remove the loop end nodes
removeLoops :: [Loop] -> [RTNode Exp] -> [RTNode Exp]
removeLoops ls exps = concat $ map (flip removeLoop exps) ls

-- | Given a loop and a list of nodes remove the loop end nodes from the list
removeLoop ::  Loop -> [RTNode Exp] -> [RTNode Exp]
removeLoop (_,_,ed) exps = filter (\n -> idx n /= ed) exps

-- | Adjusts a loops position so that it matches a tree generated from the
-- antiunifier
adjustLoop :: Loop -> Loop
adjustLoop (k,st,ed) = (k,[],adjust st ed)
  where adjust [] eds = eds
        adjust (s:sts) eds = adjust sts (delete s eds)


fst3 :: (a,b,c) -> a
fst3 (a,_,_) = a

-- | Get the third of a triple
thd3 :: (a,b,c) -> c
thd3 (_,_,c) = c

{-
assemblePartial :: [Exp] -> (RTree Exp, [Loop]) -> Exp
assemblePartial ch (rt, loops) = Imply b h
  where h = fromJust $ expr $ rootLabel rt
        b = (map (fromJust . expr) ls) ++ ch
        ls = extLeaves rt

stepConsLemma :: Exp -> Program -> [(Bool, Exp)]
stepConsLemma e prog = lemma
  where rt = constructAbstractTree e prog
        loops = map getLoops (findLoops rt)
        adjLoops = map (map adjustLoop) loops
        absTrees = abstractTrees rt loops prog
        hasLoopNodes = catMaybes $ zipWith containsLoops absTrees adjLoops
        lemma =  map (flip assembleProvableLemma prog) hasLoopNodes

interCase :: [(Bool, Seq, Exp)] -> (RTree Exp, [Loop]) -> Program -> (Bool,[Exp])
interCase ch rtl prog = map helper nextStep
  where failed = filter (\(a,_,_) -> not a) ch
        treeHeads = map (thd3) failed
        newPrg = [("a" ++ show $ length prog, assemblePartial treeHeads rtl)] ++ prog
        nextStep = map (flip stepConsLemma newPrg) treeHeads -- [[(Bool,Exp)]]

helper :: [(Bool, Exp)] -> (Bool, [Exp])
helper xs = (and (map fst xs), map snd xs)-}
