module TypeClass

import Types
import Infer
import Debug.Error

-- (Num a) ⇒ a → Int -> [IsIn "Num" (TVar (Tyvar "a" Star))] :⇒ (TVar (Tyvar "a" Star) 'fn' tInt)

data Pred   = IsIn Id T
data Qual t = Imp (List Pred) t

Types Pred where
  apply s (IsIn i t) = IsIn i (apply s t)
  tv (IsIn i t)      = tv t

Types t => Types (Qual t) where
  apply s (Imp ps t) = Imp ps t
  tv (Imp ps t)      = tv ps `union` tv t

-- lift Type to Pred
lift : Monad m => (T -> T -> m Subst) -> Pred -> Pred -> m Subst
lift m (IsIn i t) (IsIn i' t') with (i == i')
  | True  = m t t'
  | False = error "classes differ"

mguPred : Pred -> Pred -> Maybe Subst
mguPred = lift mgu

matchPred : Pred -> Pred -> Maybe Subst
matchPred = lift match

Inst : Type
Inst = Qual Pred

Class : Type
Class = (List Id, List Inst)

{-
quit reasonable to represent type and type class hierarchy
(["Eq"], [[] :⇒ IsIn "Ord" tUnit,
          [] :⇒ IsIn "Ord" tChar,
          [] :⇒ IsIn "Ord" tInt,
          [IsIn "Ord" (TVar (Tyvar "a" Star)),
           IsIn "Ord" (TVar (Tyvar "b" Star))]
             :⇒ IsIn "Ord" (pair (TVar (Tyvar "a" Star))
                           (TVar (Tyvar "b" Star)))])
-}
