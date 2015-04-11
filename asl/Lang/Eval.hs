module Lang.Eval where
import Lang.Syntax
import Lang.Monad
import Lang.PrettyPrint
import Text.PrettyPrint hiding(sep)
import Control.Monad.State.Lazy
import Control.Monad.Reader
import Control.Monad.Except

import qualified Data.Map as M
import qualified Data.Set as S
import Data.List
-- StateT [(VName, FType)] is the query environment
-- ReaderT is for let binding
type Eval a = (ReaderT [(VName, Exp)] Global) a

runEval :: Env -> [Exp] -> IO [Either TCError Exp]
runEval env ls = mapM (\ p -> runReduce p env) ls

runReduce :: Exp -> Env -> IO (Either TCError Exp)
runReduce p env =
  runExceptT $ evalStateT (runGlobal (runReaderT (reduce p) [])) env

-- all the let-bind variable will be renamed to fresh variable.
reduce :: Exp -> Eval Exp
reduce (App (Lambda x t1) t2) = do
  emit $ (text "reducing" <+> disp (App (Lambda x t1) t2))  
  reduce $ apply t2 x t1

reduce (FApp (Lambda x t1) t2) = do
  emit $ (text "reducing" <+> disp (FApp (Lambda x t1) t2))  
  reduce $ apply t2 x t1

reduce (App t1 t2) = do
  emit $ (text "reducing" <+> disp (App t1 t2))  
  a <- reduce t1
  if isLambda a
    then reduce $ App a t2
    else return $ App a t2
  where isLambda (Lambda x t) = True
        isLambda (Pos _ p) = isLambda p
        isLambda _ = False

reduce (FApp t1 t2) = do
  emit $ (text "reducing" <+> disp (FApp t1 t2))  
  a <- reduce t1
  if isLambda a
    then reduce $ FApp a t2
    else return $ FApp a t2
  where isLambda (Lambda x t) = True
        isLambda (Pos _ p) = isLambda p
        isLambda _ = False

reduce (Lambda x t) = do
  emit $ (text "reducing" <+> disp (Lambda x t))
  return $ Lambda x t

reduce (EVar x) = do
    emit $ (text "reducing" <+> disp x)
    e <- get
    loc <- ask
    case lookup x loc of
      Just p -> reduce p
      Nothing -> 
        case M.lookup x (progDef e) of
          Just (_, t) -> if t == EVar x then return $ EVar x
                         else reduce t
          Nothing -> case lookup x (dataType e) of
                            Just _ -> return $ EVar x
                            Nothing -> tcError "stucking situation"
                                        [(disp "undefined variable: ", disp x), (disp "local env: ", disp $ show loc)]

reduce u@(Let defs t) = do
  emit $ (text "reducing" <+> disp u)
  let  old = map fst defs
       ds = map snd defs
       new = map (\ x -> "`"++x) old
       subs = zip old (map EVar new)
       ds' = map (substList subs) ds
       defs' = zip new ds'
       t' = substList subs t
  curr <- ask
  -- emit $ (text "current defs" <+> disp (show curr))
  -- emit $ (text "extended defs" <+> disp (show defs'))     
  t'' <- local (\ e -> defs' ++ e) $ reduce t'
  reduce $ substList defs' t''
    where substList sub p = foldl' (\ x (v, t) -> apply t v x) p sub

reduce ill@(Match p branches) = do
  emit $ (text "reducing" <+> disp ill)  
  p' <- reduce p
  case p' of
    a@(App p1 p2) -> do
      let ((EVar c):rs) = flatApp a
      createRed c rs branches
    b@(FApp p1 p2) -> do
      let ((EVar c):rs) = flatApp b
      createRed c rs branches  
    EVar c -> do
--      emit $ (text "in here" <+> disp ill)
      createRed c [] branches
    t -> tcError "stucking situation"
         [(disp "can't find a rule to reduce: ", disp t)]

reduce (Pos _ t) = reduce t

-- redDefs c l brs = createRed c (tail l) brs
  -- case head l of
  --   PVar c -> createRed c (tail l) brs
  --   t -> tcError "stucking situation"
  --        [(disp "unknown data constructor: ", disp t)]  

createRed c defs branches =
  case findBranch c branches of
    Nothing -> tcError "stucking situation"
               [(disp "unknown data constructor: ", disp c <+> (text $ show defs) <+> (text $ show branches) )]
    Just (_, args, p) -> reduce $ Let (zip args defs) p
  
findBranch c [] = Nothing
findBranch c ((cons, args, p):xs) =
  if c == cons then Just (cons, args, p)
    else findBranch c xs
  
createArgs ftype = do
  let argsType = flatten ftype
  args <- mapM (\ x -> makeName "d") argsType
  return $ zip (map EVar args) argsType

getHead (Arrow f1 f2) = getHead f2
getHead (Pos _ f) = getHead f
getHead o = o


-- ftype3 = FApp (FApp (FVar "Eq2") (FVar "Q")) (FVar "E")
-- ftype4 = FApp (FApp (FVar "Eq2") (FVar "Q")) (FVar "Q")

-- test :: Maybe [(VName, FType)]
-- test = formMatch ["Eq2"] [] ftype3 ftype4
--search u 


