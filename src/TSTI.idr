module TSTI

import Types
import Unify
import TypeClass
import Debug.Error

data Scheme = Forall (List Kind) (Qual T)

Eq Scheme where
  (Forall ks1 q1) == (Forall ks2 q2) = ks1 == ks2 && q1 == q2

Types Scheme where
  apply s (Forall ks qt) = Forall ks (apply s qt)
  tv (Forall ks qt)      = tv qt

quantify : List Tyvar -> Qual T -> Scheme
quantify vs qt = Forall ks (apply s qt)
  where vs' : List Tyvar
        vs' = [ v | v <- tv qt, v `elem` vs ]
        ks : List Kind
        ks  = map kind vs'
        len : Int
        len = (toIntNat $ length vs') - 1
        s : Subst
        s   = zip vs' (map TGen [0..len])

toScheme : T -> Scheme
toScheme t = Forall [] ([] :=> t)

infixr 5 :>:
data Assump = (:>:) Id Scheme

Types Assump where
  apply s (i :>: sc) = i :>: (apply s sc)
  tv (i :>: sc)      = tv sc

find : Monad m => Id -> List Assump -> m Scheme
find i [] = error $ "unbound identifier: " ++ i
find i ((i' :>: sc) :: as) = if i == i' then return sc else find i as

