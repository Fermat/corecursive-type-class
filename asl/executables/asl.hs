{-# LANGUAGE  ScopedTypeVariables #-}
module Main where
import Lang.Parser
import Lang.Syntax
import Lang.PrettyPrint
import Lang.Monad
import Lang.Eval
-- import Lang.Pattern
-- import Lang.TypeInference
-- import Lang.PMCompile
import Control.Monad.Except hiding (join)
import Text.PrettyPrint
import Text.Parsec(ParseError)
import System.Console.CmdArgs
import Data.Typeable
import Control.Exception
import Control.Monad.State
import System.Environment
import System.Exit
import System.IO(withFile,hGetContents,IOMode(..),hClose,openFile)
import Data.Map

main = flip catches handlers $ do
  args <- getArgs
--  putStrLn $ "Computing\n"
  case args of
    [filename] -> do
      cnts <- readFile filename
      case parseModule filename cnts of
             Left e -> throw e
             Right a -> do putStrLn $ "Parsing success! \n"
                           print $ disp a
                           {-
                           res <- runTypeChecker a
                           ((_, subs),env) <- liftEither res
                           putStrLn $ "Type Checking success! \n"
                           let env' = convert env -- converting the pattern into case-exp
                           print $ disp env'
--                           print $ disp subs
--                           putStrLn $ "Beginning Evaluation.  \n"
                           evalRes <- runEval env' $ toEval env'
                           norms <- mapM liftEither evalRes
                           let norms' = zip [1..] norms
                           putStrLn $ "Result of evaluation.  \n"
                           mapM_ (\ (i, t) -> print (int i <+>  text ":"<+> disp t)) norms'

                           -- let (Module v a') = a
                           -- ensureTypeCheck a'
                           -- putStrLn $ "Preprocessing.. \n"
                           -- b <- checkDefs a
                           -- case b of
                           --   Left e1 -> throw e1
                           --   Right (env, e) ->  do
                           --     putStrLn "ProofChecking success!"
                           --     print $ disp env
                               
--look at local variable                              print $ disp e
-}

    _ -> putStrLn "usage: asl <filename>"
  where handlers = [Handler parseHandler, Handler typeHandler]
        typeHandler e@(ErrMsg _) = print (disp e) >> exitFailure
        parseHandler (e :: ParseError)= print (disp e) >> exitFailure

liftEither (Left err) = throw err
liftEither (Right val) = return val

-- ensureTypeCheck a' = do
--   re <- runTypeCheck a'
--   case re of
--     Left e -> throw e
--     Right ((defs, _), substs) -> do
--       putStrLn $ "Type Check success! \n"
--       mapM_ (print . disp) defs
--      mapM_ (print . disp) substs
