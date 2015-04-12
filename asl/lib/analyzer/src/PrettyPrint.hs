{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
module PrettyPrint where
import Syntax
import Text.PrettyPrint

class Disp d where
  disp :: d -> Doc
  precedence :: d -> Int
  precedence _ = 0
  
instance Disp Doc where
  disp = id

instance Disp Int where
  disp = integer . toInteger

dParen:: (Disp a) => Int -> a -> Doc
dParen level x =
   if level >= (precedence x)
   then parens $ disp x 
   else disp x

instance Disp Term where
  disp (Star) = text "*"
  disp (s@(App s1 s2)) =
    dParen (precedence s - 1) s1 <+>
    dParen (precedence s) s2
  disp (Var x) = text x
  disp (Fun x) = text x
  disp (Pred x) = text x
                           
  precedence (App _ _) = 10

  precedence (Star) = 12
  precedence (Var _) = 12
  precedence (Fun _) = 12
  precedence (Pred _) = 12

instance Disp ([Term], Term) where
  disp (t1, t2) = text "(" <> brackets (hcat (punctuate (text ",") $ map disp t1)) <+> text "," <+> disp t2 <> text ")"

instance Disp Term => Disp [([Term], Term)] where
  disp ls = vcat $ map disp ls

instance Disp Rule where
  disp (Rule conds l r) =
    (hcat (punctuate (text ",") $ map disp conds)) <+> text "=>" <+> disp l <+> text "->" <+> disp r

instance Disp Form where
  disp (Form h b) =
    (hcat (punctuate (text ",") $ map disp b)) <+> text "=>" <+> disp h

instance Disp Subst where
  disp ls = vcat $ map (\(x, y) -> (disp x <+> text "|->" <+> disp y )) ls
