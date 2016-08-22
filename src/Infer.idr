module Infer

import Types
import TypeClass
import TSTI

Infer : Type -> Type -> Type
Infer e t = ClassEnv -> List Assump -> e -> TI (List Pred, t)

data Literal = LitInteger  Integer
             | LitChar Char
             | LitDouble  Double
             | LitString  String

tiLit : Literal -> TI (List Pred, T)
tiLit (LitChar _) = return ([], tChar)
tiLit (LitInteger _) = do v <- newTVar Star
                          return ([IsIn "Num" v], v)
tiLit (LitString _) = return ([], tString)
tiLit (LitDouble _) = do v <- newTVar Star
                         return ([IsIn "Fractional" v], v)
