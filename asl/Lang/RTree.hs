-- | Construction of a rewriting tree
-- author: Andrew Pond
module Lang.RTree where

import           Data.List  (isPrefixOf, delete, nub)
import           Data.Maybe (catMaybes, fromJust)
import           Data.Tree
import           Lang.Syntax hiding(flatten)
import           Lang.Functionalisation
import           Lang.PrettyPrint
import           Control.Monad
import qualified Data.MultiSet as MS

symbs :: Exp -> MS.MultiSet Exp
symbs a@(EVar _) = MS.insert a MS.empty
symbs a@(Con _) = MS.insert a MS.empty
symbs a@(FApp t1 t2) = symbs t1 `MS.union` symbs t2

getSymb t = case flatApp t of
                h:hs -> MS.unions $ map symbs hs

-- isPaterson A B means whether A => B satisfies Paterson's condition
isPaterson :: Exp -> Exp -> Bool
isPaterson t1 t2 = let s1 = getSymb t1
                       s2 = getSymb t2 in
                   MS.isProperSubsetOf s1 s2

type Seq = [Int] -- ID for a node
type Program = [Clause]
type Clause  = (VName, Exp)
type Loop = (VName,Seq,Seq)
type Match = (Seq, Clause, [(VName, Exp)])

data Proj  = P String Int Bool | PEmpty
           deriving (Eq, Ord)

instance Show Proj where
  show (P k i b) = (filter (/= '"') $ show k ++ ", " ++ show i ++ ", " ++ show b)
  show (PEmpty) = ""

data RTNode a = NodeData { idx  :: Seq
                         , proj :: Proj
                         , expr :: Maybe a
                         , loop :: Maybe Loop
                         , ext  :: Bool
                         } deriving (Eq, Ord)

instance (Eq a, Disp a) => Show (RTNode a) where
  show nd
    | isSuccess nd     = "Success"
    | isProblematic nd = filter (/= '"') $ (fromJust $ fmap (show . disp) (expr nd))
                         ++ "\nLoop:" ++ show (fromJust $ loop nd)
    | otherwise        = fromJust $ fmap (show . disp) (expr nd)

instance Functor RTNode where
  fmap f nd = nd {expr = fmap f (expr nd)}

type RTree a = Tree (RTNode a)

drawRTree :: (Eq a, Disp a) => RTree a -> IO ()
drawRTree rt = putStrLn $ drawTree (fmap show rt)

-- | Given an Exp and a Program, construct the RTree until it is no longer
-- expandable
constructRTree :: Exp -> Program -> RTree Exp
constructRTree e prog = constructTree (not . extendableTree) firstLeafMatch rt prog
  where rt = newRoot e

-- | Give a termination check function, a matching function, a RTree and a Program
-- construct a tree until it is terminated.
constructTree :: (RTree Exp -> Bool) ->
                 ([RTNode Exp] -> Program -> Maybe Match) ->
                 RTree Exp -> Program -> RTree Exp
constructTree termFunc matchFunc rt prog =
  case termFunc nextRTree || nextRTree == rt of
    True  -> nextRTree
    False -> constructTree termFunc matchFunc nextRTree prog
  where nextRTree = stepTree matchFunc rt prog

-- | Given a matching fucntion, a RTree, a number of steps and a program, expand
-- the RTree the number of steps times.
stepNTree :: ([RTNode Exp] -> Program -> Maybe Match) ->
             RTree Exp -> Int -> Program -> RTree Exp
stepNTree _mf rt 0 _prog = rt
stepNTree matchFunc rt s prog  = case nxt of
                        Nothing -> rt
                        Just sub -> stepNTree matchFunc (extRTree rt sub) (s-1) prog
  where ls = extLeaves rt
        nxt = matchFunc ls prog

-- |  Given a matching function, a RTree and a Program, expand the RTree one step
stepTree :: ([RTNode Exp] -> Program -> Maybe Match) ->
            RTree Exp -> Program -> RTree Exp
stepTree matchFunc rt prog = case nxt of
                               Nothing -> rt
                               Just sub -> extRTree rt sub
  where ls = extLeaves rt
        nxt = matchFunc ls prog

-- | Given a RTree and details for an expansion apply the expansion to the RTree
extRTree ::  RTree Exp -> Match -> RTree Exp
extRTree rt (par, clause, subs) = fmap (fmap (applyE subs)) (appendRTree rt par chNodes)
  where chNodes = replaceProbNodes rt newNodes
        newNodes = nodesFromImply clause par


-- | Given a RTree, the ID of the leaf and a list of new children nodes
-- constructed from the leaf append the new nodes to the leaf
appendRTree :: RTree a -> Seq -> [RTNode a] -> RTree a
appendRTree rt _ [] = rt
appendRTree (Node nd []) [] nns =
  case ps of
    [] -> Node (nd {ext = False}) (map (flip Node []) nns)
    ns -> Node (nd {loop = loop (head ns), ext = False }) []
  where ps = filter isProblematic nns
appendRTree (Node nd nds) (x:xs) nns = Node (nd {ext = False}) (h ++ [modNode] ++ r)
  where modNode = appendRTree (head m) xs nns
        (h, t) = splitAt (x-1) nds
        (m, r) = splitAt 1 t

-- | Given a RTree and a list of constructed nodes return a list of nodes where
-- problematic nodes have been replaced
replaceProbNodes :: RTree a -> [RTNode a] -> [RTNode a]
replaceProbNodes ot rts = map (replaceProbNode ot) rts

-- | Given a RTree(which the node is constructed from) and a node return the
-- node if it is not problematic otherwise replace it with a problematic node
replaceProbNode :: RTree a -> RTNode a -> RTNode a
replaceProbNode ot nd
  | isPattersons nd = nd
  | otherwise       = case lookup (proj nd) (parentsProj ot (idx nd)) of
                        Just a  -> let P k _ _ = proj nd in
                                   nd { loop = Just (k, init a, init (idx nd))
                                      , ext = False
                                      }
                        Nothing -> nd

-- | Given a clause and a parent ID, create the new nodes of this expansion
nodesFromImply :: Clause -> Seq -> [RTNode Exp]
nodesFromImply (n, (Imply [] _h)) par =
  [NodeData { idx  = par ++ [1]
           , proj = P n 0 True
           , expr = Nothing
           , loop = Nothing
           , ext  = False
           }]
nodesFromImply (n, (Imply b h)) par = zipWith (newNode par n h) b [1..]
nodesFromImply (_, _) _ = []

-- | Create a new node with the details given
newNode :: Seq -> VName -> Exp -> Exp ->  Int -> RTNode Exp
newNode par cname pexp nexp ch =
  NodeData { idx  = par ++ [ch]
           , proj = P cname ch (isPaterson nexp pexp)
           , expr = Just nexp
           , loop = Nothing
           , ext  = True
           }

newRoot :: Exp -> RTree Exp
newRoot e = Node nd []
  where nd = NodeData { idx  = []
                      , proj = PEmpty
                      , expr = Just e
                      , loop = Nothing
                      , ext  = True
                      }

-- | Given a list of nodes and a program return the ID of the next node to
-- expand, the clause matched against and a list of substitutions.
firstLeafMatch :: [RTNode Exp] -> Program -> Maybe Match
firstLeafMatch [] _ = Nothing
firstLeafMatch (x:_xs) prg = case expr x of
                               Nothing -> Nothing
                               Just ex -> matchNode (idx x) ex prg

-- | Given a node ID an expression and a program, return the first match
matchNode :: Seq -> Exp -> Program -> Maybe Match
matchNode _   _ []                        = Nothing
matchNode nid e (pc@(_, (Imply _b h)):cs) =
  case match h e of
    Nothing -> matchNode nid e cs
    Just su -> Just (nid, pc, su)
matchNode _ _ ((_, _):_) = Nothing

-- | Return the projection of all the parents of a node
parentsProj :: RTree a -> Seq -> [(Proj, Seq)]
parentsProj rt nid = parentsWith proj nid rt

-- | Given a function, a node ID and a RTree, return the function applied to all
-- the nodes which are parents of the node ID and these parent IDs
parentsWith :: (RTNode a -> b) -> Seq -> RTree a -> [(b, Seq)]
parentsWith f nid rt = map (\x -> (f x, idx x)) parents
  where parents = filter (\x -> isPrefixOf (idx x) nid) (flatten rt)

-- | Given a RTree find all loops within and return all the problematic nodes
-- with their truncated RTree.
loopedTruncs :: (Eq a) => RTree a -> [(RTNode a, Maybe (RTree a))]
loopedTruncs rt = map (\x -> (x, join $ fmap (truncLoop rt) (loop x))) probNodes
  where probNodes = filterNodes (isProblematic) rt

-- | Given a RTree and a loop truncate the RTree to the loop
truncLoop :: (Eq a) => RTree a -> Loop -> Maybe (RTree a)
truncLoop rt (_,st,end) = trunc rt st end

-- | Given a RTree, start ID and end ID truncate a RTree to the start subtree
-- and remove any nodes after then end on that branch
trunc :: (Eq a) => RTree a -> Seq -> Seq -> Maybe (RTree a)
trunc rt st end = case subTree st rt of
                      Nothing -> Nothing
                      Just s  -> Just (pruneTree end s)

-- | Prune a RTree to removing any nodes under the loop but leaving all other branches intacts
pruneTree :: Seq -> RTree a -> RTree a
pruneTree pid rt@(Node nd rts)
  | pid == idx nd = rt { subForest = [] }
  | otherwise = rt { subForest = map (pruneTree pid) rts}

-- | Given an ID and a RTree, return the subtree at that position
subTree :: (Eq a) => Seq -> RTree a -> Maybe (RTree a)
subTree sid rt@(Node nd rts)
  | sid == idx nd = Just rt
  | rts == [] = Nothing
  | otherwise = msum $ map (subTree sid) rts

-- | Given an ID and a RTree, return the node at that position
lookupTree :: (Eq a) => Seq -> RTree a -> Maybe (RTNode a)
lookupTree sid rt = case subTree sid rt of
                      Just x  -> Just (rootLabel x)
                      Nothing -> Nothing

-- | Check if a RTree has any more extendable nodes
extendableTree ::  RTree a -> Bool
extendableTree rt = or (map ext (flatten rt))

-- | Given a RTree return all the extendable leaves
extLeaves :: RTree a -> [RTNode a]
extLeaves rt = filterNodes (\x -> ext x) rt

allLeaves :: RTree a -> [RTNode a]
allLeaves (Node nd []) = [nd]
allLeaves (Node _  rs) = concat $ map (allLeaves) rs

-- | Given a RTree and a predicate return a list of nodes that satisfy the predicate
filterNodes :: (RTNode a -> Bool) -> RTree a -> [RTNode a]
filterNodes f rt = filter f (flatten rt)

-- | Given a Node check if it represents a Success Node
isSuccess :: (Eq a) => RTNode a -> Bool
isSuccess nd
  | expr nd == Nothing = True
  | otherwise          = False

-- | Given a Node check if it represents a Problematic Node
isProblematic :: RTNode a -> Bool
isProblematic nd
  | Nothing == loop nd = False
  | otherwise          = True

-- | Given a Node check if it meets Pattersons
isPattersons :: RTNode a -> Bool
isPattersons nd =
  case proj nd of
    PEmpty  -> True
    P _ _ b -> b

-- | Given a Node check if it represents a Normal Node (Neither Success nor Problematic)
isNormal :: (Eq a) => RTNode a -> Bool
isNormal nd = not (isSuccess nd) && not (isProblematic nd)

-- | Given a RTree find the minimal Loops. If none exist find loops which have
-- multiple leaves.
findLoops :: (Eq a) => RTree a -> [[RTNode a]]
findLoops rt = case minL of
                 [] -> multipleLeafLoops rt
                 ls -> map (\x -> x:[]) ls
  where minL = minimalLoops rt

-- | Given a RTree find the minimal Loops. If none exist find loops which have
-- multiple leaves.
findLoops' :: (Eq a) => RTree a -> [([RTNode a], RTree a)]
findLoops' rt = case minL of
                 [] -> multipleLeafLoops' rt
                 ls -> map (\(x,y) -> (x:[],y)) ls
  where minL = minimalLoops' rt

-- | Get the minimal loop nodes in a RTree
minimalLoops :: (Eq a) => RTree a -> [RTNode a]
minimalLoops rt = map fst minimal
  where truncs  = loopedTruncs rt
        minimal = filter (\(ln, t) -> isLoopFree ln t) truncs

-- | Get the minimal loops in a RTree
minimalLoops' :: (Eq a) => RTree a -> [(RTNode a, RTree a)]
minimalLoops' rt = map (\(ln, t) -> (ln, fromJust t)) minimal
  where truncs = loopedTruncs rt
        minimal = filter (\(ln, t) -> isLoopFree ln t) truncs

-- | Is the RTree loop free
isLoopFree :: (Eq a) => RTNode a -> Maybe (RTree a) -> Bool
isLoopFree _ln Nothing   = False
isLoopFree ln (Just rt) = case (delete ln $ filterNodes (isProblematic) rt) of
                            [] -> True
                            _  -> False

-- | Given a RTree find loops with multiple leaves
multipleLeafLoops :: (Eq a) => RTree a -> [[RTNode a]]
multipleLeafLoops rt = nub singleLoops
  where truncs = map (fromJust . snd) (loopedTruncs rt)
        allLoops = map (filterNodes (isProblematic)) truncs
        singleLoops = filter (\x -> isSingleLoop x x) allLoops

-- | Given a RTree find loops with multiple leaves
multipleLeafLoops' :: (Eq a) => RTree a -> [([RTNode a], RTree a)]
multipleLeafLoops' rt = nub singleLoops
  where truncs = map (fromJust . snd) (loopedTruncs rt)
        allLoops = map (filterNodes (isProblematic)) truncs
        singleLoops = filter (\(x,_) -> isSingleLoop x x) (zip allLoops truncs)

-- | Check all the loops are part of the same loop
isSingleLoop :: (Eq a) => [RTNode a] -> [RTNode a] -> Bool
isSingleLoop []     _   = True
isSingleLoop (n:ns) lns = and (res ++ [isSingleLoop ns lns])
  where others = map (fromJust . loop) $ delete n lns
        res    = map (areSameLoop (fromJust $ loop n)) others

-- | Compare one loop with another to see if they belong to the same loop
areSameLoop ::  Loop -> Loop -> Bool
areSameLoop (_,st1,en1) (_,st2,en2)
  | st1 /= st2         = False
  | isPrefixOf en1 en2 = False
  | isPrefixOf en2 en1 = False
  | otherwise          = True

-- | Get all the loops in list of nodes
getLoops :: [RTNode a] -> [Loop]
getLoops rts = catMaybes $ map loop rts
