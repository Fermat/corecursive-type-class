module Analyzer.Interface where
import Analyzer.Syntax
import Analyzer.Stable
import Analyzer.Narrowing
import Analyzer.PrettyPrint


filtering :: [Rule] -> [Rule]
filtering rs = [ a | a@(Rule _ l r) <- rs, not (hasApp r)]
stable :: [Form] -> [Form, ]
stable rls = let dpPair = dpGen rls
                 rules = rueExtension dpPair
                 axioms = axiomExtension rules
                 rules' = filtering rules
                 res = runNarrowing rules' 
                 
