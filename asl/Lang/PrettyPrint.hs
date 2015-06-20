{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Lang.PrettyPrint where
import Lang.Syntax

import Text.PrettyPrint
import Text.Parsec.Pos
import Data.Char
import Text.Parsec.Error(ParseError,showErrorMessages,errorPos,errorMessages)

class Disp d where
  disp :: d -> Doc
  precedence :: d -> Int
  precedence _ = 0
  
instance Disp Doc where
  disp = id

instance Disp String where
  disp x = if (isUpper $ head x) || (isLower $ head x)
           then text x
           else if head x == '`'
                then text x
                else parens $ text x

instance Disp Int where
  disp = integer . toInteger

dParen:: (Disp a) => Int -> a -> Doc
dParen level x =
   if level >= (precedence x)
   then parens $ disp x 
   else disp x

instance Disp Exp where
  disp (EVar x) = disp x
  disp (s@(App s1 s2)) =
    dParen (precedence s - 1) s1 <+>
    dParen (precedence s) s2
  disp (Lambda x t) = text "\\" <+> text x
                      <+> text "." <+> disp t
  disp (Match p alts) = text "case" <+> disp p <+>
                        text "of" $$
                        nest 2 (vcat (map dAlt alts))
    where dAlt (c, args, p) =
            fsep [disp c <+> hsep (map disp args) <+> text "->", nest 2 $ disp p]
  disp (Let ls p) = text "let" $$ nest 2 (vcat ( map dDefs ls)) <+> text "in" $$  disp p
    where dDefs (v, t) = fsep [text v <+> text "=", nest 2 $ disp t]
          
  disp (Pos _ t) = disp t

  disp (KVar x) = disp x
  disp Star = text "*"
  disp (a@(KArrow t1 t2)) =
    dParen (precedence a) t1
    <+> text "->"
    <+> dParen (precedence a - 1) t2


  disp (s@(FApp s1 s2)) =
    dParen (precedence s - 1) s1 <+>
    dParen (precedence s) s2
  disp (a@(Arrow t1 t2)) =
    dParen (precedence a) t1
    <+> text "->"
    <+> dParen (precedence a - 1) t2

  disp (a@(Forall x f)) =
    text "forall" <+> disp x
    <+> text "."
    <+> disp f

  disp (DArrow ts f) =
    if null ts then disp f
    else (hsep $ punctuate comma (map disp ts))
         <+> text "=>" <+> disp f

  precedence (FApp _ _) = 10

  precedence (Arrow _ _) = 4

  precedence (Star) = 12
  precedence (KArrow _ _) = 4
  precedence (KVar _) = 12

  precedence (Pos _ t) = precedence t
  precedence (EVar _) = 12
  precedence (App _ _) = 10
  precedence _ = 0

instance Disp Pattern where
  disp (Var x) = disp x
  disp (Cons c pats) = disp c <+> hsep (map disp pats)
  
instance Disp Equation where
  disp (pats, prog) =  hsep (map helper pats) <+> text "=" <+> disp prog
    where helper (Var x) = disp x
          helper a = parens $ disp a
          

instance Disp (VName, Exp) where
  disp (v, sc) = disp v <+> text "::" <+> disp sc

-- instance Disp (VName, Exp) where
--   disp (v, sc) = disp v <+> text "mapsto" <+> disp sc

instance Disp Datatype where
  disp (Data d params cons) = 
    hang (text "data" <+> text d
          <+> hsep (map text params)
          <+> text "where") 2 (vcat (map dispCon cons))
   where dispCon (n, t) = disp n <+> text "::"
                          <+> disp t

instance Disp Class where
  disp (Class d params cons) = 
    hang (text "class" <+> text d
          <+> hsep (map text params)
          <+> text "where") 2 (vcat (map dispCon cons))
   where dispCon (n, t) = disp n <+> text "::"
                          <+> disp t

instance Disp Inst where
  disp (Inst ([], f) cons) = 
    hang (text "instance" 
          <+> disp f 
          <+> text "where") 2 (vcat (map dispCon cons))
    where dispCon (n, t) = disp n <+> text "="
                           <+> disp t

  disp (Inst (ts, f) cons) = 
    hang (text "instance" 
          <+> (hsep $ punctuate comma (map disp ts)) <+> text "=>"
          <+> disp f 
          <+> text "where") 2 (vcat (map dispCon cons))
   where dispCon (n, t) = disp n <+> text "="
                          <+> disp t

instance Disp Module where
  disp (Module name decl) = text "module" <+> text name <+> text "where" $$ vcat (map disp decl)

instance Disp Decl where
  disp (ProgDecl _ x p) = disp x <+> text "=" <+>disp p
  disp (DataDecl p d) = disp d
  disp (ClassDecl p d) = disp d
  disp (InstDecl p d) = disp d
  disp (SigDecl p v d) = disp v <+> text "::" <+> disp d
  disp (EvalDecl p) = text "reduce" <+> disp p

-- instance Disp Constraints where
--   disp l = vcat $ map dispPair l
--     where dispPair (t1,t2) = disp t1 <+> text "=" <+> disp t2

instance Disp SourcePos where
  disp sp =  text (sourceName sp) <> colon <> int (sourceLine sp)
             <> colon <> int (sourceColumn sp) <> colon

instance Disp ParseError where
 disp pe = (disp (errorPos pe)) $$
           (text "Parse Error:" $$ sem)
  where sem = text $ showErrorMessages "or" "unknown parse error"
              "expecting" "unexpected" "end of input"
              (errorMessages pe)

instance Disp Subst where
  disp s = vcat $ map (\ (x, y) -> disp x <> text "|->" <> disp y) s

--test = disp (Pi "n" (FVar "Nat") (Arrow (FVar "U") (Arrow (FCons "Vec" [ArgType (FVar "U"),ArgProg (Name "n")]) (FCons "Vec" [ArgType (FVar "U"),ArgProg (Applica (Name "s") (Name "n"))]))))
--test1 = disp (Data "Nat" [] [("z",FVar "Nat"),("s",Arrow (FVar "Nat") (FVar "Nat"))])
