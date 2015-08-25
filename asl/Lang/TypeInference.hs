module Lang.TypeInference where
import Lang.Syntax
import Lang.PrettyPrint
import Lang.Functionalisation
import Lang.Monad
import Lang.KindInference
import Lang.Lemma
import Lang.Formulas hiding(combine)
import Text.Parsec.Pos
import Text.PrettyPrint hiding(sep)
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import qualified Data.Map as M
import qualified Data.Set as S
import Data.List hiding(partition)
import Debug.Trace

-- StateT Subst for HM unification, [(VName, TScheme)] for typing local context (introduced by lambdas and definitions)

type TCMonad a = StateT Int (StateT Subst (ReaderT [(VName, TScheme)] Global)) a  

runTypeChecker :: Module -> IO (Either TCError (((), Subst), Env))
runTypeChecker m = 
  runExceptT $ runStateT
  (runGlobal (runReaderT (runStateT (evalStateT (checkModule m) 0) []) [])) emptyEnv

checkModule :: Module -> TCMonad ()
checkModule (Module _ []) = return ()

checkModule (Module a (d:ds)) = do
  checkDecl d
  checkModule (Module a ds)

-- no implicit polymorphic recursion
checkDecl :: Decl -> TCMonad ()

checkDecl (EvalDecl p) = do
  (p', _, assump) <- checkProg p
  subs <- lift $ get
  env <- lift $ lift get
  let assump' = map (\(a , b) -> (a, applyE subs b)) assump
      axs = axioms env
      lems = lemmas env
      preds = map snd assump'
--  emit $ vcat (map disp preds)
--  emit "enter"
      autoLems = concat $ map (\ x -> fixLemma x (lems ++ axs) []) preds
  autos <- mapM (\ x -> makeName "auto") autoLems
  zipWithM proving autos autoLems
  let
      as = lems ++ (zip autos autoLems) ++ axs
      preds' = map (\ p -> runRewrite p as) preds
  check preds' assump'   
  let names = map fst assump'
      preds'' = map (\ (Just x) -> x) preds'
      newP = foldr (\ x y -> Lambda x y) p' names
      term = foldl' (\ x y -> App x y) newP preds''
  lift $ lift $ modify (\ e -> extendEval term e)
  where check ls assump' =
          when (any ((==) Nothing) ls) $
          tcError "unable to construct evidence "
               [(disp "constraints ", disp assump')]
--        proving a b c | trace ("myfun " ++ show b ++ " " ++ show c) False = undefined
        proving n c = do
          env <- lift $ lift get
          let
              ax = lemmas env ++ axioms env
              lm = runPositive c ("C"++n++"D")
              (Imply [c'] _) = runPositive (Imply [c] (Con "Q")) ("Q"++n++"D")
              res = corecursive c' ax [(n, lm)]
          case res of
            Nothing -> tcError "typing error: "
                       [(disp "generated intermediate lemma is unprovable ", disp c)]
            Just r -> do
              lift $ lift $ modify (\ e -> extendLemma n lm e)
              lift $ lift $ modify (\ e -> extendProgDef n (Scheme [] (DArrow [] lm)) r e)


checkDecl (ProgDecl pos x p) = do
  n <- makeName "x"
  let ts = Scheme [] $ DArrow [] (EVar n)
  (p', f, assump) <- local (\ y -> (x, ts):y) $ checkProg p
  -- emit subs
  unification f (EVar n) `catchError` addErrorPos pos x
  subs' <- lift $ get
  let
      f'' = applyE subs' f
      assump' = map (\(a , b) -> (a, applyE subs' b)) assump
      names = map fst assump'
      preds = map snd assump'
      newP = foldr (\ x y -> Lambda x y) p' names 
  sc <- qToTScheme (DArrow preds f'')
  lift $ lift $ modify (\ e -> extendProgDef x sc newP e)

checkDecl (DataDecl pos d@(Data n _ _)) = 
  checkData d `catchError` addErrorPos pos n

checkDecl (InstDecl pos inst) =
  checkInst inst `catchError` addErrorPos pos (show $ disp (firstline inst))

checkDecl (ClassDecl pos c) =   
  checkClass c -- `catchError` addProgErrorPos pos c

checkDecl (LemmaDecl pos c) = do
  n <- makeName "lem"
  env <- lift $ lift get
  let ax = lemmas env ++ axioms env
      lm = runPositive c ("C"++n++"D")
      (Imply [c'] _) = runPositive (Imply [c] (Con "Q")) ("Q"++n++"D")
      res = corecursive c' ax [(n, lm)]
  case res of
    Nothing -> tcError "typing error: "
               [(disp "unprovable lemma ", disp c)]
    Just r -> do
      lift $ lift $ modify (\ e -> extendLemma n lm e)
      lift $ lift $ modify (\ e -> extendProgDef n (Scheme [] (DArrow [] lm)) r e)
  
-- (term, type, predicates assumptions)
checkProg ::  Exp -> TCMonad (Exp, Exp, [(VName, Exp)])
checkProg (Con y) = do
  env <- lift $ lift get
  case M.lookup y $ progDef env of
    Just (t, e) -> do
      DArrow [] t' <- freshInst t
      return (e, t', [])
    Nothing -> tcError "typing error: "
               [(disp "undefine constructor ", disp y)]
      
checkProg (EVar y) = do
  tcAssump <- ask
  case lookup y tcAssump of
    Just sc -> do
      ni <- freshInst sc
      return ((EVar y), getFType ni, [])
    Nothing -> do
      env <- lift $ lift get
      case M.lookup y $ progDef env of
        Just (ts, _) -> do
          qt <- freshInst ts
          case qt of
            DArrow [] ft -> return ((EVar y),ft, [])
            DArrow xs ft -> do
              newVars <- mapM (\ x -> makeName "e") xs
              let zs = zip newVars xs 
              --    env' =  zs ++ assump
                  pvars = map EVar newVars 
                  p = foldl' (\ x y -> App x y) (EVar y) pvars
              return (p, ft, zs)
        Nothing ->
          tcError "Undefined variable: "
          [(disp "Variable ", disp y)]
          
checkProg (App t1 t2) = do
  (t1', f1, a1) <- checkProg t1 
  (t2', f2, a2) <- checkProg t2 
  m <- makeName "x"
  unification f1 $ Arrow f2 (EVar m)
  return (App t1' t2', EVar m, a1++a2)

checkProg (Lambda x t) = do
  n <- makeName "x"
  let sc = Scheme [] $ DArrow [] (EVar n) 
      ty = EVar n
      new = (x, sc)
  (t', ty', newA) <- local (\y -> new:y) $ checkProg t 
  let ty'' = Arrow ty ty'
  return (Lambda x t', ty'', newA)

checkProg (Let xs p) = do
  ns <- mapM (\ x -> makeName "X") xs
  let tns = map (\ x -> Scheme [] $ DArrow [] (EVar x)) ns
      fns = map EVar ns
      names = map fst xs
      letEnv = zip names tns
      dets = zip (map snd xs) fns
  defs <- mapM (helper letEnv) dets
  sub <- lift get
  let cxt = zip names (map tSnd defs)
      bds = zip names (map tFst defs)
      assump1 = map tTrd defs
      assump' = concat assump1
  newCxt <- subGen sub assump1 cxt -- not supporting any let-polymorphism now.
           
  (p', f, newAssump) <- local (\ y -> newCxt ++ y) $ checkProg p 
  return (Let bds p',f, assump' ++ newAssump) 
  where helper env (t, f) = do
            (t', ft, as') <- local (\y -> env ++ y) $ checkProg t 
            unification ft f
            return (t', ft, as') 

checkProg (Match p branches) = do
  (p', datatype, assump') <- checkProg p 
  let b0 = head branches
  (t0', f0, assump0) <- checkBranch datatype b0 
  res <- mapM (helper datatype f0) (tail branches)
  let pats = map (\ (x, y, z) -> (x, y)) branches
      res' = (t0',f0, assump0):res
      newProgs = map (\ (t, f, _) -> t) res'
      newBranches = merge pats newProgs
      newAssump = concat $ map tTrd res'
  return (Match p' newBranches, f0, assump'++newAssump)
  where helper datatype ft branch = do
          (t, f, as') <- checkBranch datatype branch 
          unification f ft
          return (t, f, as')
        merge [] [] = []
        merge ((x,y):rs) (z:zs) = (x, y, z) : merge rs zs

checkProg (Pos pos p) =
  checkProg p `catchError` addProgErrorPos pos p

checkBranch datatype (c, args, t) = do
  env <- lift $ lift get
  case M.lookup c $ progDef env of
    Nothing -> tcError "Undefined data constructor: "
           [(disp "Constructor name: ", disp c)]
    Just (Scheme vars (DArrow [] ty), _) -> do
      arityCheck c ty (length args)
      newNames <- mapM (\ x -> makeName "x") vars
      let newVars = map EVar newNames
          subs = zip vars newVars
          newTy = applyE subs ty
          d1 = getDataType newTy
          typs = flatten newTy
          typs' = map (\ x -> Scheme [] $ DArrow [] x ) typs
          newCxt = zip args typs'
      unification d1 datatype
      local (\ y -> newCxt ++ y) $ checkProg t 

checkData :: Datatype -> TCMonad ()
checkData (Data d params cons) = do
  kname <- makeName "g"
  lift $ lift $ modify (\ e -> extendData d (KVar kname) True e)
  let d1 = if null params then Con d else makeFType d params
  subst <- lift $ lift $ lift $ runKinding $ getTypes cons
  let d2 = applyK subst (KVar kname)
  lift $ lift $ modify (\ e -> extendData d (ground d2) True e)
  mapM_ (checkCons d1) cons
  mapM_ extendCons cons
  return ()
  where getTypes cs = map (\(x,y) -> y) cs
        makeFType d params = foldl' (\ z x -> FApp z x) (Con d) (map EVar params) 
        checkCons d (c, f) = do
          let d' = getDataType f
          if d == d' then return ()
            else tcError "Constructor return data mismatch: "
           [(disp "can't match ", quotes (disp d) <+> disp "with"<+> quotes (disp d'))]
        extendCons (c, f) = do
          s <- toTScheme f
          lift $ lift $ modify (\ e -> extendProgDef c s (Con c) e)

checkClass :: Class -> TCMonad ()
checkClass (Class u params meths) = do
  kname <- makeName "g"
  lift $ lift $ modify (\ e -> extendData u (KVar kname) False e)
  let fts = map (\ (x, q) -> getFType q) meths
      d = makeType fts $ foldl' (\ z x -> FApp z x) (Con u) (map EVar params)
      toKC = map qToFType (map snd meths)
  subst <- lift $ lift $ lift $ runKinding $ toKC
  let d2 = applyK subst (KVar kname)
  lift $ lift $ modify (\ e -> extendData u (ground d2) False e) 
  s <- toTScheme d
  let c = "C"++u
  lift $ lift $ modify (\ e -> extendProgDef c s (Con c) e)
  let l = length fts
      pats = makeVarNs "t" l
--  emit pats
  defs <- mapM (makeSelector c pats) (zip [1..] meths)
  mapM_ ( \ (xi, sqi, defi) -> lift $ lift $ modify (\ e -> extendProgDef xi sqi defi e)) defs
  where makeSelector c pats (i, (xi, qti)) = do
          sq <- qToTScheme qti
          return (xi, sq, Lambda "d" (Match (EVar "d") [(c, pats, EVar $ pats !! (i-1)  )]))

makeVarNs s n | n >= 0 = map (\ y -> s ++ show y) [1..n]


checkInst :: Inst -> TCMonad ()
checkInst (Inst (qs, u) defs) = do
  let ft = makeType qs u
      ft1 = Imply qs u
      u' = getPred u
      args = makeVarNs "a" $ length qs
      methNames = map fst defs
  lift $ lift $ lift $ runKinding [ft]    -- kind check
  gEnv <- lift $ lift get
  res <- mapM (\ (x, t) -> checkProg t) defs    -- type check
  let progs = progDef gEnv
      tyss = map tSnd res
 --  emit $ (hcat $ map disp tyss) <+> disp u
  ensureInst tyss u progs -- ensure declared type match with the infered types
  uniRes <- lift get
  ft' <- toTScheme ft
  let  types = map (applyE uniRes) tyss
--       datas = map fst $ dataType gEnv
--  emit $ (hsep $ map disp types)
  defTypes <- mapM (\n -> checkMethod n progs) methNames -- check all implemented methods are defined
  ensureT types defTypes

  let impArgs = zip args qs
--      lEnv = impArgs  ++ [("dict", u) ]
      
      forms = divide $ map snd impArgs
--      lEnv' = reconstruct impArgs $ concat forms
      genAssumps = map (\ (x,y) -> (x, applyE uniRes y)) $ concat $ map tTrd res
      terms = map tFst res
      genForms = divide $ map snd genAssumps
      precondition = check genForms forms && check forms genForms
      -- (Let [("dict", d)] $ PVar "dict" )
  if precondition then
    let genForms' = reorder genForms forms
        sub = firstSub genForms' forms
        genAssumps' = reconstruct genAssumps $ concat genForms'
        phi = map (\(x,y) -> (x, EVar y )) $ zip (map fst genAssumps') (map fst impArgs)
        newTerms = map (applyE phi) terms
        d = foldl' (\ s arg -> App s arg) (EVar $ "C"++ u') newTerms
        constr = foldr (\ a b -> Lambda a b) d $ map fst impArgs in
    case sub of
      Nothing ->
        tcError "Required predicates does not match specified predicates: "
        [(disp "Required:", hsep $ map disp $ concat genForms'),(disp "Specified: ", hsep $ map disp $ concat forms)]
      Just _ -> do
 --       emit $ (hsep $ map disp genAssumps)
        name <- makeName "e"
        lift $ lift $ modify (\ e -> extendProgDef name ft' constr e) -- extend instance func
        lift $ lift $ modify (\ e -> extendAxiom name ft1 e) -- extend axioms
        -- let def  = makeDef qs (EVar name)
        --     Just (kindInfo, False) = lookup u' $ dataType gEnv
        --     kinds = flatten kindInfo            
        --     args1 = getArgs u
--            info = zip args1 kinds 
--            pats = map (\ x -> toPat x gEnv) $ args1
        --lift $ lift $ modify (\ e -> extendEq u' (pats, def) e)  -- extend functional type class    
  --      return ()
    else tcError "Required predicates does not match specified predicates: "
        [(disp "Required:", hsep $ map disp $ concat genForms),(disp "Specified: ", hsep $ map disp $ concat forms)]
  where reconstruct env (f:fs) = let a = keyOf f env in (a,f) : reconstruct (delete (a,f) env) fs
        reconstruct env [] = []
        keyOf f ((x, f'):xs) = if f == f' then x else keyOf f xs -- f must be found
        checkMethod a m = case M.lookup a m of
                            Nothing -> tcError "Undeclared method: " [(disp "Method Name:", disp a)]
                            Just (Scheme _ q, _) -> return $ getFType q
        ensureT t d = zipWithM unify (t) d

        getArgs (FApp p1 p2) = getArgs p1 ++ [p2]
        getArgs _ = []
        makeDef ls cons = foldl' (\ z x -> App z x) cons ls
        ensureInst tys t progs = do
          t' <- toTScheme t
          t'' <- freshInst t'
          let resTypes = foldr (\ z x -> Arrow z x) (getFType t'') tys 
          case M.lookup ("C"++(getPred t)) progs of
            Nothing -> tcError "Internal Error: " [(disp "from ensureInst", disp "in type checking instance decl")]
            Just (t, _) -> do
              t' <- freshInst t
              unification (getFType t') resTypes

{-
toPat p state = 
  let ps = toSpine p
      f = map (helper state) ps  in
  case f of
    ((Cons c []):t) ->

      -- let aris = arity c state
      -- in
      --  if aris == length t
      Cons c t
--       else error $ "Wrong arity from toPat"++ show c++show t++show aris++ show p
    ((Var m):[]) ->  Var m
    e -> error "unknown from toPat"
    where helper st (EVar a) = 
            if elem a (map fst $ dataType st)
              then (Cons a [])
              else (Var a)
          helper st c@(FApp a b)  = toPat c st
          helper st (Pos _ p) = helper st p 
-}
toSpine (EVar a) = [EVar a]
toSpine (FApp a b) = toSpine a ++ [b]
toSpine (Pos _ p) = toSpine p
-- helper functions

tFst (a,b,c) = a
tSnd (a,b,c) = b
tTrd (a,b,c) = c

addProgErrorPos ::  SourcePos -> Exp -> TCError -> TCMonad a
addProgErrorPos pos p (ErrMsg ps) = throwError (ErrMsg (ErrLocProg pos p:ps))

addErrorPos ::  SourcePos -> VName -> TCError -> TCMonad a
addErrorPos pos n (ErrMsg ps) = throwError (ErrMsg (ErrLocOther pos n:ps))
                         
type PSubst = [(VName, VName)]  

-- again, this is not capture avoiding substitution
-- , since
-- it is intended to substitute the generated
-- evidence variable with the generated variable.

  
makeType :: [Exp] -> Exp -> Exp
makeType [] u = u
makeType (x:xs) u = Arrow x (makeType xs u)
    

getDataType :: Exp -> Exp
getDataType (Arrow f1 f2) = getDataType f2
getDataType f = f

arityCheck :: VName -> Exp -> Int -> TCMonad ()
arityCheck c f n = do
  if arity f == n then return ()
    else tcError "Arity check failure: "
           [(disp "Constructor name: ", disp c)]
  where arity (Arrow _ ft) = arity ft + 1
        arity _ = 0

-- not supporting let-polymorphism anymore
subGen :: Subst -> [[(VName, Exp)]] -> [(VName, Exp)] -> TCMonad [(VName, TScheme)]
subGen sub assump as = do
  let assump' = map (map snd) assump
      as' = zip as assump'
  mapM (helper sub) as'
  where helper sub ((x, t), ps) = do
          let t' = applyE sub t
              p' = map (applyE sub) ps
              a = Scheme [] $ DArrow p' t'
        --  a <- toTScheme t' 
          return (x, a)

toTScheme :: Exp -> TCMonad TScheme
toTScheme ft = do
  env <- lift $ lift get
--  let def = map fst $ dataType env 
  return $ Scheme (nub [ x | x <- S.toList $ freeVar ft]) $ DArrow [] ft

qToTScheme :: QType -> TCMonad TScheme
qToTScheme (DArrow qs ft) = do
  env <- lift $ lift get
  let
    qvars = S.unions $ map freeVar qs
--  emit $ show def
  return $ Scheme (nub [ x | x <- S.toList $ S.union qvars (freeVar ft)]) $ DArrow qs ft

qToFType :: QType -> Exp
qToFType (DArrow xs f) = foldl' (\ z x -> Arrow z x) f xs

getFType :: QType -> Exp
getFType (DArrow _ f) = f

--getPred :: QType -> [FType]

-- tcError :: Disp d => d -> [(Doc, Doc)] -> TCMonad a


combine :: Subst -> Subst -> Subst
combine s2 s1 =
   s2 ++ [(v, applyE s2 t) | (v, t) <- s1] 


-- easy version to do unification and modify
-- substitution at the same time. 
unification :: Exp -> Exp -> TCMonad ()
unification t1 t2 = do
  subs <- lift get
  new <- unify (applyE subs t1) (applyE subs t2)
  lift $ put $ combine new subs

-- sideeffect: throwing error, using the global counter

unify :: Exp -> Exp -> TCMonad Subst

-- The following is a simple extension of unification to support data polymorphism a la Jones. 
unify (Forall y f) t = do
 n <- makeName "x"
 let f' = applyE [(y, EVar n)] f in
   unify f' t

unify t (Forall y f) = unify (Forall y f) t   
-----------------------------------
 
unify (Arrow t1 t2) (Arrow a1 a2) = do
  s1 <- unify t1 a1
  s2 <- unify (applyE s1 t2) (applyE s1 a2) 
  return $ combine s2 s1

unify (FApp t1 t2) (FApp a1 a2) = do
  s1 <- unify t1 a1
  s2 <- unify (applyE s1 t2) (applyE s1 a2) 
  return $ combine s2 s1

unify (EVar tn) t =
  varBind tn t
  
unify t (EVar tn) = varBind tn t

unify (Con x) (Con y) = if x == y then return [] else
                          tcError "Unification failure: "
                          [(disp "trying to unify ", disp x),(disp "with ", disp y)]
                          
unify t t' = tcError "Unification failure: "
           [(disp "trying to unify ", disp t),(disp "with ", disp t')]

varBind x t | t == EVar x = return []
            | x `S.member` freeVar t =
                tcError "Occur-Check failure: "
                [(disp "trying to unify ", disp x),(disp "with ", disp t)]
            | otherwise = return [(x, t)]
                    
freshInst :: TScheme -> TCMonad QType
freshInst (Scheme xs t) =
  if null xs
  then return t
  else do
   newVars <- mapM (\ x -> makeName "x") xs
   let substs = zip xs (map (\ y -> EVar y) newVars) in
     return $ applyQ substs t




