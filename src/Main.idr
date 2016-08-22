module Main

import TSTI
import Types
import Unify
import Infer
import TypeClass

Program : Type
Program = List BindGroup

tiProgram : ClassEnv -> List Assump -> Program -> List Assump
tiProgram ce as bgs = runTI $
                      do (ps, as') <- tiSeq tiBindGroup ce as bgs
                         s         <- getSubst
                         rs        <- reduce ce (apply s ps)
                         s'        <- defaultSubst ce [] rs
                         return $ apply (s' @@ s) as'

main : IO ()
main = putStrLn "thh"
