{-# LANGUAGE NamedFieldPuns, DeriveDataTypeable, ParallelListComp, GeneralizedNewtypeDeriving, FlexibleInstances  #-}
module Lang.Monad where
import Lang.Syntax
import Lang.PrettyPrint

import Text.PrettyPrint
import Data.Typeable
import Control.Monad.State
import Control.Monad.Except
import Control.Exception
--import Control.Monad.Trans.Except
import qualified Data.Map as M
import Control.Applicative hiding (empty)
import Control.Monad.Reader
import Text.Parsec.Pos

-- the reason we make Env a state is we want
-- to access it after type checking, namely,
-- at the reduction phase. 
newtype Global a = Global { runGlobal :: (StateT Env (ExceptT TCError IO)) a}
  deriving (Functor, Monad, Applicative, MonadState Env, MonadError TCError, MonadIO)


data Env = Env{ progDef :: M.Map VName (Exp, Exp),  -- (type, def)
                dataType :: [(VName, (Exp, Bool))], -- (name, kind, whether it is genuine data)
                toEval :: [Exp], -- progs
                equations :: [(VName, Equation)]
              }
         deriving Show

emptyEnv :: Env
emptyEnv = Env {progDef = M.empty, dataType = [], toEval = [], equations = []}
                  
extendProgDef :: VName -> Exp -> Exp -> Env -> Env
extendProgDef v ts t e@(Env {progDef}) = e{progDef = M.insert v (ts, t) progDef}

extendEval :: Exp -> Env -> Env
extendEval p e@(Env {toEval}) = e{toEval = p:toEval}

extendData :: VName -> Exp -> Bool -> Env -> Env
extendData v k b e@(Env {dataType}) = e{dataType =  (v, (k, b)):dataType}

extendEq :: VName -> Equation -> Env -> Env
extendEq v ts e@(Env {equations}) = e{equations =  (v , ts) : equations}

-- extendAssump :: VName -> FType -> Env -> Env
-- extendAssump v ts e@(Env {assump}) = e{assump = M.insert v ts assump}

-- updateAssump :: (M.Map VName FType -> M.Map VName FType) -> Env -> Env
-- updateAssump f e@(Env {assump}) = e{assump = f assump}
-- extendAssump :: VName -> FType -> Env -> Env
-- extendAssump v ts e@(Env {assump}) = e{assump = M.insert v (ts, Nothing) assump}

--------------

instance Disp Env where
  disp env = hang (text "Program Definitions") 2 (vcat
                [disp n <+> text "::" <+> disp ts $$ text "=" <+> disp t <+> text "\n" | (n, (ts, t)) <- M.toList $ progDef env])  $$ hang (text "Datas") 2 (vcat [ disp n <+> text "::" <+> disp k | (n, (k, _)) <- dataType env])
             $$
             hang (text "Type Class Def") 2 (vcat [ disp n <+> disp k | (n, k) <- equations env])
             $$
             hang (text "To be reduce") 2 (vcat
                                           [ int i <+> text ":" <+> disp p  | (i, p) <- zip [1..] (toEval env)])

instance Disp [(Exp, Exp)] where
  disp ls = text "[" <+> (vcat $ map (\ (x, y) -> text "(" <+> disp x <+> text ","<+> disp y<+>text ")") ls)
            <+>text "]"
----------------

data TCError = ErrMsg [ErrInfo]
               deriving (Show, Typeable)

data ErrInfo = ErrInfo Doc -- A Summary
               [(Doc,Doc)] -- A list of details
             | ErrLocProg SourcePos Exp
             | ErrLocOther SourcePos String
             deriving (Show, Typeable)

instance Exception TCError
instance Disp TCError where
  disp (ErrMsg rinfo) =
       hang (pos positions) 2 (summary $$ nest 2 detailed $$  vcat terms)
    where info = reverse rinfo
          positions = [el | el <- info, f el == True]
          f (ErrLocOther _ _) = True
--          f (ErrLocProof _ _) = True
          f (ErrLocProg _ _) = True
          f _ = False
          messages = [ei | ei@(ErrInfo _ _) <- info]
          details = concat [ds | ErrInfo _ ds <- info]
--          pos ((ErrLocPre sp _):_) = disp sp
          pos ((ErrLocOther sp _):_) = disp sp
          pos ((ErrLocProg sp _):_) = disp sp
          pos _ = text "unknown position" <> colon
          summary = vcat [s | ErrInfo s _ <- messages]
          detailed = vcat [(int i <> colon <+> label) <+> d |
                           (label,d) <- details | i <- [1..]]
          terms = [hang (text "in") 2 (dispExpr t) |  t <- take 4 positions]
    --      dispExpr (ErrLocProof _ p) = disp p
          dispExpr (ErrLocOther _ p) = disp "the delaration:" <+> disp p
          dispExpr (ErrLocProg _ p) = disp "the expression:"<+> disp p

-- addProofErrorPos ::  SourcePos -> Proof -> PCError -> Global a
-- addProofErrorPos pos p (ErrMsg ps) = throwError (ErrMsg (ErrLocProof pos p:ps))

tcError summary details = throwError (ErrMsg [ErrInfo (disp summary) details])

ensure :: Disp d => Bool -> d -> Global ()
ensure p m = unless p $ die m

die :: Disp d => d -> Global a
die msg = pcError (disp msg) []

pcError :: Disp d => d -> [(Doc, Doc)] -> Global a
pcError summary details = throwError (ErrMsg [ErrInfo (disp summary) details])

addErrorInfo :: Disp d => d -> [(Doc, Doc)] -> TCError -> TCError
addErrorInfo summary details (ErrMsg ms) = ErrMsg (ErrInfo (disp summary) details:ms)

-- withErrorInfo :: (Disp d) => d -> [(Doc, Doc)] -> Global a -> Global a
-- withErrorInfo summary details m = m `catchError` (throwError . addErrorInfo summary details)

emit :: (Show a, MonadIO m) => a -> m ()
emit m = liftIO $ print m

(<++>) :: (Show t1, Show t2, Disp t1, Disp t2) => t1 -> t2 -> Doc
t1 <++> t2 = disp t1 <+> disp t2

($$$) :: (Disp d, Disp d1) => d -> d1 -> Doc
t1 $$$ t2 =  disp t1 $$ disp t2




