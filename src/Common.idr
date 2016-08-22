module Common

%access public export

syntax [test] "?" [t] ":" [e] = if test then t else e;

null : List a -> Bool
null [] = True
null _  = False
