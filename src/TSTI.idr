module TSTI

import Types
import Unify
import TypeClass
import Debug.Error

%access public export

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
        len : Integer
        len = (toIntegerNat $ length vs') - 1
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

data TI a = TIC (Subst -> Integer -> (Subst, Integer, a))

Functor TI where
  map f (TIC ti) = TIC (\s, n => let (s, i, a) = ti s n in (s, i, f a))

Applicative TI where
  pure x = TIC (\s, n => (s, n, x))
  (TIC f) <*> (TIC ti) = TIC (\s, n => let (s, i, a) = ti s n in
                                       let (s', i', ab) = f s i in
                                       (s', i', ab a))

Monad TI where
  (TIC f) >>= g = TIC (\s, n => let (s',m,x) = f s n in
                                let TIC gx = g x in
                                gx s' m)

runTI : TI a -> a
runTI (TIC f) = let (_, _, x) = f emptySubst 0 in x

getSubst : TI Subst
getSubst = TIC (\s, n => (s,n,s))

extSubst : Subst -> TI ()
extSubst s' = TIC (\s, n => (s' @@ s, n, ()))

unify : T -> T -> TI ()
unify t1 t2 = do s <- getSubst
                 u <- mgu (apply s t1) (apply s t2)
                 extSubst u

newTVar : Kind -> TI T
newTVar k = TIC (\s, n => let v = MkTyvar (enumId n) k
                          in (s, n + 1, TVar v))

interface Instantiate t where
  inst : List T -> t -> t

Instantiate T where
  inst ts (TApp l r) = TApp (inst ts l) (inst ts r)
  inst ts (TGen n)   = case index' idx ts of
                         Just t => t
                         Nothing => error "index out of bound"
    where idx : Nat
          idx = fromIntegerNat n
  inst ts t          = t

Instantiate a => Instantiate (List a) where
  inst ts = map (inst ts)

Instantiate Pred where
  inst ts (IsIn c t) = IsIn c (inst ts t)

Instantiate t => Instantiate (Qual t) where
  inst ts (ps :=> t) = inst ts ps :=> inst ts t

freshInst : Scheme -> TI (Qual T)
freshInst (Forall ks qt) = do ts <- traverse newTVar ks
                              return (inst ts qt)

