{-#LANGUAGE PackageImports, StandaloneDeriving, DeriveDataTypeable, FlexibleContexts#-}
module Lang.Parser
       (parseModule) where
import Lang.Syntax

import Prelude hiding (pred)
import Text.Parsec hiding (ParseError,Empty, State)
import qualified Text.Parsec as P
import Text.Parsec.Language
import Text.Parsec.Expr(Operator(..),Assoc(..),buildExpressionParser)
import qualified Text.Parsec.Token as Token
import Text.Parsec.Indent

import Control.Applicative hiding ((<|>),many, optional)
import Control.Monad.State.Lazy
import "mtl" Control.Monad.Identity
import Control.Exception(Exception)

import qualified Data.IntMap as IM
import Data.Typeable
import Data.Char
import Data.List

parseModule :: String -> String -> Either P.ParseError Module
parseModule srcName cnts =
  runIndent srcName $
  runParserT gModule initialParserState srcName cnts

type Parser a = IndentParser String ParserState a

-- User state, so that we can update the operator parsing table.

data ParserState =
  ParserState {
    progParser :: IndentParser String ParserState Exp,
    progOpTable :: IM.IntMap [Operator String ParserState (State SourcePos) Exp]
    }

initialParserState :: ParserState
initialParserState = ParserState {
  progParser = buildExpressionParser [] progA, 
  progOpTable = IM.fromAscList (zip [0 ..] [[]])
  }


binOp :: Assoc -> String -> (a -> a -> a) -> Operator String u (State SourcePos) a
binOp assoc op f = Infix (reservedOp op >> return f) assoc

postOp :: String -> (a -> a) -> Operator String u (State SourcePos) a
postOp op f = Postfix (reservedOp op >> return f)

preOp :: String -> (a -> a) -> Operator String u (State SourcePos) a
preOp op f = Prefix (reservedOp op >> return f)

toOp op "infix" app var = binOp AssocNone op (binApp op app var)
toOp op "infixr" app var = binOp AssocRight op (binApp op app var)
toOp op "infixl" app var = binOp AssocLeft op (binApp op app var)
toOp op "pre" app var = preOp op (preApp op app var)
toOp op "post" app var = postOp op (postApp op app var) 
toOp _ fx app var = error (fx ++ " is not a valid operator fixity.")

postApp op app var x = app (var op) x

preApp op app var x = app (var op) x

binApp op app var x y = app (app (var op) x) y

deriving instance Typeable P.ParseError
instance Exception P.ParseError 

-- parse module
gModule :: Parser Module
gModule = do
  whiteSpace
  reserved "module"
  modName <- identifier
  reserved "where"
  bs <- many gDecl
  eof
  return $ Module modName bs

gDecl :: Parser Decl
gDecl = try sigDecl <|> gDataDecl <|>  instDecl
        <|> classDecl <|> progDecl <|> reduceDecl

setVar :: Parser String
setVar = do
  n <- identifier
  when (isLower (head n)) $
    unexpected "Data names must begin with an uppercase letter."
  return n
-- type signature

sigDecl = do
  f <- termVar
  reservedOp "::"
  t <- ftype
  pos <- getPosition
  return $ SigDecl pos f t
  
-- datatype
gDataDecl :: Parser Decl
gDataDecl = do
  reserved "data"
  n <- setVar
  pos <- getPosition
  ps <- params
  reserved "where"
  cs <- block cons
  return $ DataDecl pos (Data n ps cs) 
  where cons = do
          c <- termVar
          reservedOp "::"
          t <- ftype
          return (c,t)
        params = many setVar

termVar :: Parser String
termVar = do
  n <- identifier
  when (isUpper (head n)) $
    unexpected "Term names must begin with an lowercase letter."
  return n

-- parser for FType--
ftype :: Parser Exp
ftype = buildExpressionParser ftypeOpTable base

base :: Parser Exp
base = try qtype <|> try compound <|> try forall <|> parens ftype

ftypeOpTable :: [[Operator String u (State SourcePos) Exp]]
ftypeOpTable = [[binOp AssocRight "->" Arrow]]

forall = do
  reserved "forall"
  vars <- many1 setVar
  reservedOp "."
  f <- ftype
  return $ foldr (\ z x -> Forall z x) f vars
  
compound = do
  n <- setVar
  as <- compoundArgs
  if null as then return $ EVar n
    else return $ foldl' (\ z x -> FApp z x) (EVar n) as 

compoundArgs = 
  many $ indented >>
  ((try (setVar >>= \ n -> return $ EVar n))
   <|> try (parens ftype))

qtype = do
  qs <- sepBy compound comma
  if null qs then unexpected "Empty predicates"
    else do
    reservedOp "=>"
    f <- ftype
    return $ DArrow qs f
    
-----  Parser for Program ------

progDecl :: Parser Decl
progDecl = do
  n <- termVar
  pos <- getPosition
  reservedOp "="
  p <- prog
  return $ ProgDecl pos n p
  
progA :: Parser Exp  
progA = wrapPos $ absProg <|> caseTerm <|> appProg <|> letbind <|> parens prog

prog :: Parser Exp
prog = getState >>= progParser 

termVarProg :: Parser Exp
termVarProg = termVar >>= \n-> return $ EVar n

appProg = do
  sp <- try termVarProg <|> try (parens prog) 
  as <- many $ indented >> (try (parens prog) <|> try termVarProg)
  if null as then return sp
    else return $ foldl' (\ z x -> App z x) sp as

letbind = do
  reserved "let"
  bs <- block branch
  reserved "in"
  p <- prog
  return $ Let bs p
  where branch = do 
          v <- termVar
          reservedOp "="
          p <- prog
          return $ (v, p)
          
caseTerm = do
  reserved "case"
  n <- prog
  reserved "of"
  bs <- block branch
  return $ Match n bs
  where
    branch = do
      v <- termVar 
      l <- many $ termVar
      reservedOp "->"
      pr <- prog
      return $ (v, l, pr)

absProg = do
  reservedOp "\\"
  as <- many1 termVar
  reservedOp "."
  p <- prog
  return $ foldr (\ x y -> Lambda x y) p as

-- reduce decl
reduceDecl :: Parser Decl  
reduceDecl = do
  reserved "reduce"
  p <- prog
  return $ EvalDecl p

-- class decl

classDecl :: Parser Decl
classDecl = do
  reserved "class"
  n <- setVar
  pos <- getPosition
  ps <- params
  reserved "where"
  cs <- block medths
  return $ ClassDecl pos (Class n ps cs) 
  where medths = do
          c <- termVar
          reservedOp "::"
          t <- ftype
          return (c,t)
        params = many1 setVar

-- inst decl

pred :: Parser Exp
pred = do
  n <- setVar
  ps <- many1 (try single <|> parens ftype)
  return $  foldl' (\ z x -> FApp z x) (EVar n) ps 
 where single = do{x <- setVar; return $ EVar x }

multi :: Parser [Exp]
multi = do
  ps <- sepBy pred comma
  reservedOp "=>"
  return ps
  
instDecl :: Parser Decl
instDecl = do
  reserved "instance"
  ps <- option [] $ try multi 
  pos <- getPosition
  u <- pred
  reserved "where"
  cs <- block meds
  return $ InstDecl pos (Inst (ps,u) cs) 
  where meds = do
          c <- termVar
          reservedOp "="
          t <- prog
          return (c,t)
        
-----------------------Positions -------
  
wrapPos :: Parser Exp -> Parser Exp
wrapPos p = pos <$> getPosition <*> p
  where pos x (Pos y e) | x==y = (Pos y e)
        pos x y = Pos x y


-------------------------------

-- Tokenizer definition

gottlobStyle :: (Stream s m Char, Monad m) => Token.GenLanguageDef s u m
gottlobStyle = Token.LanguageDef
                { Token.commentStart   = "{-"
                , Token.commentEnd     = "-}"
                , Token.commentLine    = "--"
                , Token.nestedComments = True
                , Token.identStart     = letter
                , Token.identLetter    = alphaNum <|> oneOf "_'"
                , Token.opStart        = oneOf ":!#$%&*+.,/<=>?@\\^|-"
                , Token.opLetter       = (oneOf ":!#$%&*+.,/<=>?@\\^|-") <|> alphaNum
                , Token.caseSensitive  = True
                , Token.reservedNames =
                  [
                    "forall", "iota", "reduce", 
                    "cmp","invcmp", "inst", "mp", "discharge", "ug", "beta", "invbeta",
                    "by", "from", "in", "let", "simpCmp", "invSimp",
                    "case", "of",
                    "data", "if", "then", "else",
                    "theorem", "proof", "qed",
                    "show",
                    "where", "module",
                    "infix", "infixl", "infixr", "pre", "post",
                    "formula", "prog", "set",
                    "tactic", "deriving", "Ind"
                  ]
               , Token.reservedOpNames =
                    ["\\", "->", "|", ".","=", "::", ":", "=>"]
                }

tokenizer :: Token.GenTokenParser String u (State SourcePos)
tokenizer = Token.makeTokenParser gottlobStyle

identifier :: ParsecT String u (State SourcePos) String
identifier = Token.identifier tokenizer

whiteSpace :: ParsecT String u (State SourcePos) ()
whiteSpace = Token.whiteSpace tokenizer

reserved :: String -> ParsecT String u (State SourcePos) ()
reserved = Token.reserved tokenizer

reservedOp :: String -> ParsecT String u (State SourcePos) ()
reservedOp = Token.reservedOp tokenizer

operator :: ParsecT String u (State SourcePos) String
operator = Token.operator tokenizer

colon :: ParsecT String u (State SourcePos) String
colon = Token.colon tokenizer

integer :: ParsecT String u (State SourcePos) Integer
integer = Token.integer tokenizer

brackets :: ParsecT String u (State SourcePos) a -> ParsecT String u (State SourcePos) a
brackets = Token.brackets tokenizer

parens :: ParsecT String u (State SourcePos) a -> ParsecT String u (State SourcePos) a
parens  = Token.parens tokenizer

braces :: ParsecT String u (State SourcePos) a -> ParsecT String u (State SourcePos) a
braces = Token.braces tokenizer

dot :: ParsecT String u (State SourcePos) String
dot = Token.dot tokenizer

commaSep1 :: ParsecT String u (State SourcePos) a -> ParsecT String u (State SourcePos) [a]
commaSep1 = Token.commaSep1 tokenizer

semiSep1 :: ParsecT String u (State SourcePos) a -> ParsecT String u (State SourcePos) [a]
semiSep1 = Token.semiSep1 tokenizer

comma :: ParsecT String u (State SourcePos) String
comma = Token.comma tokenizer

