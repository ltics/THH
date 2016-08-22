module Unify

import Types
import Common
import Debug.Error
import Data.List

%access public export

Subst : Type
Subst = List (Tyvar, T)

emptySubst : Subst
emptySubst = []

infixr 4 +->
(+->) : Tyvar -> T -> Subst
u +-> t = [(u, t)]

interface Types t where
  apply : Subst -> t -> t -- apply substitution
  tv    : t -> List Tyvar -- get type variables

Types T where
  apply s t@(TVar u) = fromMaybe t $ lookup u s
  apply s (TApp l r) = TApp (apply s l) (apply s r)
  apply _ t = t

  tv (TVar u) = [u]
  tv (TApp l r) = tv l `union` tv r
  tv t = []

Types t => Types (List t) where
  apply s = map (apply s)
  tv      = nub . concat . map tv

-- apply (s1 @@ s2) = apply s1 . apply s2
infixr 4 @@
(@@) : Subst -> Subst -> Subst
s1 @@ s2 = [(u, apply s1 t) | (u, t) <- s2] ++ s1

merge : Monad m => Subst -> Subst -> m Subst
merge s1 s2 = if agree then return (s1 ++ s2) else error "merge fails"
  where agree = all (\v => apply s1 (TVar v) == apply s2 (TVar v))
                    (map fst s1 `intersect` map fst s2)

varBind : Monad m => Tyvar -> T -> m Subst
varBind u t = (t == TVar u) ? (return emptySubst)
            : (u `elem` tv t) ? (error "occurs check fails")
            : (kind u /= kind t) ? (error "kinds do not match")
            : return $ u +-> t

-- most general unifier
mgu : Monad m => T -> T -> m Subst
mgu (TApp l r) (TApp l' r') = do s1 <- mgu l l'
                                 s2 <- mgu (apply s1 r) (apply s1 r')
                                 return (s2 @@ s1)
mgu (TVar u) t = varBind u t
mgu t (TVar u) = varBind u t
-- think about the trivial types TInt TBool TChar TPair TList
mgu (TCon tc1) (TCon tc2) with (tc1 == tc2) | True = return emptySubst
mgu t1 t2 = error "types do not unify"

match : Monad m => T -> T -> m Subst
match (TApp l r) (TApp l' r') = do sl <- match l l'
                                   sr <- match r r'
                                   merge sl sr
match (TVar u) t with (kind u == kind t) | True = return (u +-> t)
match (TCon tc1) (TCon tc2) with (tc1==tc2) | True = return emptySubst
match t1 t2 = error "types do not match"
