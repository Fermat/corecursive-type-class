-- author: Andrew Pond
module Lang.Examples where

import Lang.Syntax
--import TCEC.Render
import Lang.RTree
--import TCEC.Lemma
--import Data.Maybe(catMaybes, fromJust)
--import Control.Monad(join, liftM2, mfilter)

list = [("k1",c1), ("k2",c2)]
  where eq = Con "Eq"
        c1 = Imply [(FApp eq (EVar "x")),(FApp eq (FApp (Con "List") (EVar "x")))] (FApp eq (FApp (Con "List") (EVar "x")))
        c2 = Imply [] (FApp eq (Con "Nat"))

dlist :: [(VName, Exp)]
dlist = [("k1",c1), ("k2",c2)]
  where eq = Con "Eq"
        dl = Con "D"
        varX = (EVar "x")
        a1 = FApp eq (FApp dl varX)
        a2 = FApp eq varX
        a3 = FApp eq (FApp dl (FApp dl varX))
        a4 = FApp eq (Con "Char")
        c1 = Imply [a2,a3] a1
        c2 = Imply [] a4

dlistExp :: Exp
dlistExp = FApp (Con "Eq") (FApp (Con "D") (Con "Char"))

tList2 :: [(VName, Exp)]
tList2 = [("k1", k1), ("k2",k2)]
  where eq = Con "Eq"
        t = Con "T"
        unit = Con "unit"
        x = EVar "x"
        k1 = Imply [FApp eq x, FApp eq (FApp t (FApp t x)), FApp eq (FApp t (FApp t (FApp t x)))] (FApp eq (FApp t x))
        k2 = Imply [] (FApp eq unit)

tList2Exp :: Exp
tList2Exp = FApp eq (FApp t unit)
  where eq = Con "Eq"
        t = Con "T"
        unit = Con "unit"

tList3 :: [(VName, Exp)]
tList3 = [("k1", k1), ("k2",k2), ("k5", k5) ]
  where eq = Con "Eq"
        t = Con "T"
        unit = Con "unit"
        x = EVar "x"
        a = Con "A"
        k1 = Imply [FApp eq x, FApp a x] (FApp eq (FApp t x))
        k2 = Imply [FApp eq (FApp t (FApp t x))] (FApp a x)
        k5 = Imply [] (FApp eq unit)

tList3Exp :: Exp
tList3Exp = FApp eq (FApp t unit)
  where eq = Con "Eq"
        t = Con "T"
        unit = Con "unit"

tList4 :: [(VName, Exp)]
tList4 = [("k1", k1), ("k2",k2), ("k5", k5) ]
  where eq = Con "Eq"
        t = Con "T"
        unit = Con "unit"
        x = EVar "x"
        a = Con "A"
        k1 = Imply [FApp eq x, FApp a x, FApp eq x] (FApp eq (FApp t x))
        k2 = Imply [FApp eq (FApp t (FApp t x))] (FApp a x)
        k5 = Imply [] (FApp eq unit)

tList4Exp :: Exp
tList4Exp = FApp eq (FApp t unit)
  where eq = Con "Eq"
        t = Con "T"
        unit = Con "unit"

compPairExp :: Exp
compPairExp = FApp (Con "Eq") (FApp(FApp (Con "Fix") (FApp (Con "Gs") (Con "Unit"))) (Con "Pair"))

compPair :: [(VName, Exp)]
compPair = [("k1",c1), ("k2",c2), ("k3", c3), ("k4", c4), ("k5", c5)]
  where eq = Con "Eq"
        --dl = Con "D"
        pair = Con "Pair"
        fix = Con "Fix"
        comp = Con "Comp"
        gseq = Con "Gs"
        --gs = Con "GSeqF"
        unit = Con "Unit"
        varA = EVar "a"
        varR = EVar "r"
        varF = EVar "f"
        varG = EVar "g"
        tt1 = FApp eq unit
        c1 = Imply [] tt1
        tt2 = FApp eq (FApp varF (FApp varG varA))
        tt3 = FApp eq (FApp (FApp (FApp comp varF) varG) varA)
        c2 = Imply [tt2] tt3
        tt4 = FApp eq varA
        tt5 = FApp eq (FApp pair varA)
        c3 = Imply [tt4] tt5
        tt6 = FApp eq varA
        tt7 = FApp eq varR
        tt8 = FApp eq (FApp (FApp gseq varA) varR)
        c4 = Imply [tt6, tt7] tt8
        tt9 = FApp eq (FApp varF (FApp (FApp fix (FApp (FApp comp varG) varF)) varG))
        tt10 = FApp eq (FApp (FApp fix varF) varG)
        c5 = Imply [tt9] tt10

mutRec :: [(VName, Exp)]
mutRec = [("k1",k1), ("k2",k2), ("k3", k3), ("k5", k5), ("k6", k6)]
  where eq = Con "Eq"
        pair = Con "Pair"
        a = EVar "a"
        b = EVar "b"
        f = EVar "f"
        g = EVar "g"
        f1 = EVar "f1"
        f2 = EVar "f2"
        h1 = Con "H1"
        h2 = Con "H2"
        h1' = EVar "h1"
        h2' = EVar "h2"
        mu = Con "Mu"
        head1 = FApp eq (FApp (FApp (FApp h1 f1) f2) a)
        body1 = [FApp eq a, FApp eq (FApp (FApp pair (FApp f1 a)) (FApp f2 a)) ]
        k1 = Imply body1 head1
        head2 = FApp eq (FApp (FApp (FApp h2 f) g) a)
        body2 = [FApp eq (FApp (FApp pair (FApp g a)) (FApp f (FApp g a))) ]
        k2 = Imply body2 head2
        head3 = FApp eq (FApp (FApp (FApp mu h1') h2') a)
        body3 = [FApp eq (FApp (FApp (FApp h1' (FApp (FApp mu h1') h2')) (FApp (FApp mu h2') h1')) a)]
        k3 = Imply body3 head3
        head5 = FApp eq (FApp (FApp pair a) b)
        body5 = [FApp eq a, FApp eq b]
        k5 = Imply body5 head5
        k6 = Imply [](FApp eq (Con "Unit"))

mutRec2 :: [(VName, Exp)]
mutRec2 = [("a", a1), ("k1",k1), ("k2",k2), ("k3", k3), ("k5", k5), ("k6", k6)]
  where eq = Con "Eq"
        pair = Con "Pair"
        a = EVar "a"
        b = EVar "b"
        f = EVar "f"
        g = EVar "g"
        x = EVar "x"
        f1 = EVar "f1"
        f2 = EVar "f2"
        h1 = Con "H1"
        h2 = Con "H2"
        h1' = EVar "h1"
        h2' = EVar "h2"
        mu = Con "Mu"
        head1 = FApp eq (FApp (FApp (FApp h1 f1) f2) a)
        body1 = [FApp eq a, FApp eq (FApp (FApp pair (FApp f1 a)) (FApp f2 a)) ]
        k1 = Imply body1 head1
        head2 = FApp eq (FApp (FApp (FApp h2 f) g) a)
        body2 = [FApp eq (FApp (FApp pair (FApp g a)) (FApp f (FApp g a))) ]
        k2 = Imply body2 head2
        head3 = FApp eq (FApp (FApp (FApp mu h1') h2') a)
        body3 = [FApp eq (FApp (FApp (FApp h1' (FApp (FApp mu h1') h2')) (FApp (FApp mu h2') h1')) a)]
        k3 = Imply body3 head3
        head5 = FApp eq (FApp (FApp pair a) b)
        body5 = [FApp eq a, FApp eq b]
        k5 = Imply body5 head5
        k6 = Imply [](FApp eq (Con "Unit"))
        headA = (FApp eq (FApp (FApp (FApp mu h1) h2) x))
        bodyA = [FApp eq x, FApp eq (FApp (FApp (FApp mu h2) h1) x)]
        a1 = Imply bodyA headA

mutRecExp :: Exp
mutRecExp = FApp (Con "Eq") (FApp(FApp(FApp (Con "Mu") (Con "H1")) (Con "H2")) (Con "Unit"))

tList :: [(VName, Exp)]
tList = [("k1", k1), ("k2",k2)]
  where eq = Con "Eq"
        t = Con "T"
        unit = Con "unit"
        x = EVar "x"
        k1 = Imply [FApp eq x, FApp eq (FApp t (FApp t (FApp t x)))] (FApp eq (FApp t x))
        k2 = Imply [] (FApp eq unit)

tListExp :: Exp
tListExp = FApp eq (FApp t (FApp t unit))
  where eq = Con "Eq"
        t = Con "T"
        unit = Con "unit"

perfectTreeExp :: Exp
perfectTreeExp = FApp (Con "Eq") (FApp (FApp (Con "Mu") (Con "HPTree")) (Con "Unit"))

perfectTree :: [(VName, Exp)]
perfectTree = [("k1", k1), ("k2", k2), ("k3", k3), ("k4", k4)]
  where eq = Con "Eq"
        mu = Con "Mu"
        hpt = Con "HPTree"
        unit = Con "Unit"
        f = EVar "f"
        a =  EVar "a"
        b = EVar "b"
        pair = Con "Pair"
        head1 = FApp eq (FApp (FApp mu f) a)
        body1 = [FApp eq (FApp (FApp f (FApp mu f)) a)]
        k1 = Imply body1 head1
        head2 = FApp eq (FApp (FApp hpt f) a)
        body2 = [FApp eq a, FApp eq (FApp f (FApp (FApp pair a) a))]
        k2 = Imply body2 head2
        head3 = FApp eq (FApp (FApp pair a) b)
        body3 = [FApp eq a, FApp eq b]
        k3 = Imply body3 head3
        head4 = FApp eq unit
        k4 = Imply [] head4

gBush :: [(VName, Exp)]
gBush = [("k1", k1), ("k2", k2), ("k3", k3), ("k4", k4)]
  where eq = Con "Eq"
        mu = Con "Mu"
        pair = Con "Pair"
        hbush = Con "HBush"
        unit = Con "Unit"
        a = EVar "a"
        b = EVar "b"
        f = EVar "f"
        head1 = FApp eq (FApp (FApp mu f) a)
        body1 = [FApp eq (FApp (FApp f (FApp mu f)) a)]
        k1 = Imply body1 head1
        head2 = FApp eq (FApp (FApp hbush f) a)
        body2 = [FApp eq a, FApp eq (FApp (FApp pair a) (FApp f (FApp f a)))]
        k2 = Imply body2 head2
        head3 = FApp eq (FApp (FApp pair a) b)
        body3 = [FApp eq a, FApp eq b]
        k3 = Imply body3 head3
        k4 = Imply [] (FApp eq unit)

gBushExp :: Exp
gBushExp = FApp eq (FApp (FApp mu hbush) unit)
  where eq = Con "Eq"
        mu = Con "Mu"
        unit = Con "Unit"
        hbush = Con "HBush"

limitation :: [(VName, Exp)]
limitation = [("k1", k1), ("k2", k2)]
  where d = Con "D"
        s = Con "S"
        z = Con "Z"
        n = EVar "n"
        m = EVar "m"
        head1 = FApp (FApp d (FApp s n)) m
        body1 = [FApp (FApp d n) (FApp s m)]
        k1 = Imply body1 head1
        head2 = FApp (FApp d z) m
        body2 =[FApp (FApp d (FApp s m)) z]
        k2 = Imply body2 head2

limitationExp :: Exp
limitationExp = FApp (FApp (Con "D") (Con "Z")) (Con "Z")

gBushRT :: RTree Exp
gBushRT = constructRTree gBushExp gBush

compPairRT :: RTree Exp
compPairRT = constructRTree compPairExp compPair

dlistRT :: RTree Exp
dlistRT = constructRTree dlistExp dlist

mutRecRT :: RTree Exp
mutRecRT = constructRTree mutRecExp mutRec

tListRT :: RTree Exp
tListRT = constructRTree tListExp tList

tList2RT :: RTree Exp
tList2RT = constructRTree tList2Exp tList2

tList3RT :: RTree Exp
tList3RT =  constructRTree tList3Exp tList3

{-}
abs1 = FApp (Con "Eq") (FApp (FApp (FApp (Con "Mu") (Con "H1")) (Con "H2")) (EVar "x"))
absRT1 = constructAbstractTree abs1 mutRec
absLoops1 = map getLoops (findLoops absRT1)
absAdjLoop1 = map (map adjustLoop) absLoops1
--absTrees = abstractTrees absRT absLoops mutRec
absLoopNodes1 = catMaybes $ zipWith containsLoops [absRT1] absAdjLoop1
absLemma1 =  map (flip assembleMatchableLemma mutRec) absLoopNodes1

abs2 = FApp (Con "Eq") (FApp (FApp (FApp (Con "Mu") (Con "H2")) (Con "H1")) (EVar "x"))
absRT2 = constructAbstractTree abs2 mutRec2
absLoops2 = map getLoops (findLoops absRT2)
absAdjLoop2 = map (map adjustLoop) absLoops2
--absTrees = abstractTrees absRT absLoops mutRec
absLoopNodes2 = catMaybes $ zipWith containsLoops [absRT2] absAdjLoop2
absLemma2 =  map (flip assembleMatchableLemma mutRec2) absLoopNodes2

d2@(rt2,loops2) = absLoopNodes2 !! 0
l21@(_,sid21,eid21) = loops2 !! 0
l22@(_,sid22,eid22) = loops2 !! 1

loopHead21 = fromJust $ join $ fmap expr $ lookupTree sid21 rt2
loopEnd21  = fromJust $ join $ fmap expr $ lookupTree eid21 rt2
sub21 = matchLoop rt2 l21
ls21 = extLeaves rt2
oes21 = map (fromJust . expr) ls21
s21 = fromJust sub21
subbed21 = map (fmap (applyE s21)) ls21
es21 = zip oes21 (map (fromJust . expr) subbed21)
noMatch21 = filter (\(a,b) -> not $ isMatchable loopHead21 b) es21
res21 = (checkMatch loopHead21 noMatch21 mutRec2, eid21, loopEnd21)

trees21 = map (flip constructAbstractTree mutRec2) (map snd noMatch21)

loopHead22 = fromJust $ join $ fmap expr $ lookupTree sid22 rt2
loopEnd22  = fromJust $ join $ fmap expr $ lookupTree eid22 rt2
sub22 = matchLoop rt2 l22
ls22 = extLeaves rt2
oes22 = map (fromJust . expr) ls22
s22 = fromJust sub22
subbed22 = map (fmap (applyE s22)) ls22
es22 = zip oes22 (map (fromJust . expr) subbed22)
noMatch22 = filter (\(a,b) -> not $ isMatchable loopHead22 b) es22
res22 = (checkMatch loopHead22 noMatch22 mutRec2, eid22, loopEnd22)

trees22 = map (flip constructAbstractTree mutRec2) (map snd noMatch22)

als22 = allLeaves (head trees22)
problematic22 = filter (isProblematic) als22
nonProblematic22 = filter (not . isProblematic) als22
lhMatch22 = map (isMatchable loopHead22) (map (fromJust . expr) problematic22)
checks22 = map (\l -> expr l == Just (head $ map fst noMatch22)) nonProblematic22
-}

{-ts2 = FApp (Con "Eq") (FApp (Con "D") (EVar "x"))
ts1 = FApp (Con "Eq") (FApp (Con "D") (Con "Char"))

au1 = FApp (Con "Eq") (FApp (Con "D") (Con "Unit"))
au2 = FApp (Con "Eq") (FApp (Con "D") (FApp (Con "D") (Con "Unit")))
au3 = FApp (FApp (Con "p") (EVar "a")) (EVar "a")
au4 = FApp (FApp (Con "p") (EVar "b")) (EVar "c")

q1 = Imply [] (FApp (Con "Eq") (Con "Unit"))
q2 = Imply [(FApp (Con "Eq") (FApp (EVar "F") (FApp (EVar "G") (EVar "A"))))]
     (FApp (Con "Eq") (FApp (FApp (FApp (Con "Comp") (EVar "F")) (EVar "G")) (EVar "A")))

q3 = Imply [(FApp (Con "Eq") (EVar "y"))] (FApp (Con "Eq") (FApp (Con "Pair") (EVar "y")))

q4 = Imply [(FApp (Con "Eq") (EVar "A")), (FApp (Con "Eq") (EVar "R"))]
     (FApp (Con "Eq") (FApp (FApp (Con "GS") (EVar "A")) (EVar "R")))

q5 = Imply [Forall "X" $ Imply [(FApp (Con "Eq") (EVar "X"))] (FApp (Con "Eq") (FApp (EVar "F") (EVar "X")))]
     (FApp (Con "Eq") (FApp (FApp (Con "Fix") (EVar "F")) (Con "Pair")))

q6 = Imply [Con "B"] (FApp (Con "Eq") (FApp (FApp (Con "Fix") (FApp (Con "GS") (Con "Unit"))) (Con "Pair")))-}

{-step1 = stepRTree dlistRoot dlist
step2 = stepRTree step1 dlist
step3 = stepRTree step2 dlist
step1' = stepRTree compPairRoot compPair
step2' = stepRTree step1' compPair
step3' = stepRTree step2' compPair
step10 = stepNRTree compPairRoot 10 compPair-}
