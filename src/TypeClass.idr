module TypeClass

import Types
import Infer
import Debug.Error

-- (Num a) ⇒ a → Int -> [IsIn "Num" (TVar (MkTyvar "a" Star))] :⇒ (TVar (MkTyvar "a" Star) 'fn' tInt)

data Pred   = IsIn Id T
data Qual t = QArrow (List Pred) t

Types Pred where
  apply s (IsIn i t) = IsIn i (apply s t)
  tv (IsIn i t)      = tv t

Types t => Types (Qual t) where
  apply s (QArrow ps t) = QArrow ps t
  tv (QArrow ps t)      = tv ps `union` tv t

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
          [IsIn "Ord" (TVar (MkTyvar "a" Star)),
           IsIn "Ord" (TVar (MkTyvar "b" Star))]
             :⇒ IsIn "Ord" (pair (TVar (MkTyvar "a" Star))
                           (TVar (MkTyvar "b" Star)))])
-}

record ClassEnv where
  constructor MkClassEnv
  classes : Id -> Maybe Class
  defaults : List T

super : ClassEnv -> Id -> List Id
super ce i = case classes ce i of
               Just (is, _) => is
               Nothing      => []

insts : ClassEnv -> Id -> List Inst
insts ce i = case classes ce i of
               Just (_, its) => its
               Nothing       => []

defined : Maybe a -> Bool
defined (Just x) = True
defined Nothing  = False

modify : ClassEnv -> Id -> Class -> ClassEnv
modify ce i c = record { classes = \j => if i == j then Just c else classes ce j } ce

initialEnv : ClassEnv
initialEnv = MkClassEnv (\i => error "class not defined") [tInteger, tDouble]

EnvTransformer : Type
EnvTransformer = ClassEnv -> Maybe ClassEnv

-- Kleisli composition operator
-- in normal function composition
-- b -> c . a -> b => a -> c
-- and now
-- Monad m => b -> m c . a -> m b => a -> m c
-- think about (<=<) operator in Control.Monad
infixr 5 <:>
(<:>) : EnvTransformer -> EnvTransformer -> EnvTransformer
f <:> g = \ce => do ce' <- f ce
                    g ce'

addClass : Id -> List Id -> EnvTransformer
addClass i is ce = (defined $ classes ce i) ? (error "class already defined")
                 : (any (not . defined . classes ce) is) ? (error "superclass not defined")
                 : return $ modify ce i (is, [])

addCoreClasses : EnvTransformer
addCoreClasses = addClass "Eq" []
             <:> addClass "Ord" ["Eq"]
             <:> addClass "Show" []
             <:> addClass "Read" []
             <:> addClass "Bounded" []
             <:> addClass "Enum" []
             <:> addClass "Functor" []
             <:> addClass "Monad" []

addNumClasses : EnvTransformer
addNumClasses = addClass "Num" ["Eq", "Show"]
            <:> addClass "Real" ["Num", "Ord"]
            <:> addClass "Fractional" ["Num"]
            <:> addClass "Integral" ["Real", "Enum"]
            <:> addClass "RealFrac" ["Real", "Fractional"]
            <:> addClass "Floating" ["Fractional"]
            <:> addClass "RealFloat" ["RealFrac", "Floating"]


addPreludeClasses : EnvTransformer
addPreludeClasses = addCoreClasses <:> addNumClasses

overlap : Pred -> Pred -> Bool
overlap p q = defined (mguPred p q)

addInst : List Pred -> Pred -> EnvTransformer
addInst ps p@(IsIn i t) ce = (not $ defined $ classes ce i) ? (error "no class for instance")
                           : (any (overlap p) qs) ? (error "overlapping instance")
                           : return $ modify ce i c
  where its : List Inst
        its = insts ce i
        qs : List Pred
        qs  = [ q | (QArrow _ q) <- its ]
        c : Class
        c   = (super ce i, (QArrow ps (IsIn i t)) :: its)

exampleInsts : EnvTransformer
exampleInsts = addPreludeClasses
           <:> addInst [] (IsIn "Ord" tUnit)
           <:> addInst [] (IsIn "Ord" tChar)
           <:> addInst [] (IsIn "Ord" tInt)
           <:> addInst [IsIn "Ord" (TVar (MkTyvar "a" Star)),
                        IsIn "Ord" (TVar (MkTyvar "b" Star))]
                       (IsIn "Ord" (pair (TVar (MkTyvar "a" Star))
                                         (TVar (MkTyvar "b" Star))))

