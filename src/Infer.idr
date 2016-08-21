module Infer

import Types
import Debug.Error
import Data.List

Subst : Type
Subst = List (Tyvar, T)

emptySet : Subst
emptySet = []

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
