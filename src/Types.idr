module Types

%access public export

Id : Type
Id = String

enumId : Int -> Id
enumId n = "@" ++ show n

data Kind = Star
          | KFun Kind Kind

Eq Kind where
  Star == Star = True
  (KFun k11 k12) == (KFun k21 k22) = k11 == k21 && k12 == k22
  _ == _ = False

data Tyvar = MkTyvar Id Kind

Eq Tyvar where
  (MkTyvar id1 k1) == (MkTyvar id2 k2) = id1 == id2 && k1 == k2
  _ == _ = False

data Tycon = MkTycon Id Kind

Eq Tycon where
  (MkTycon id1 k1) == (MkTycon id2 k2) = id1 == id2 && k1 == k2
  _ == _ = False

data T = TVar Tyvar
       | TCon Tycon
       | TApp T T
       | TGen Int -- generic type

Eq T where
  (TVar v1) == (TVar v2) = v1 == v2
  (TCon c1) == (TCon c2) = c1 == c2
  (TApp t11 t12) == (TApp t21 t22) = t11 == t21 && t21 == t22
  (TGen i1) == (TGen i2) = i1 == i2
  _ == _ = False

tUnit : T
tUnit = TCon (MkTycon "()" Star)

tChar : T
tChar = TCon (MkTycon "Char" Star)

tInt : T
tInt = TCon (MkTycon "Int" Star)

tInteger : T
tInteger = TCon (MkTycon "Integer" Star)

tFloat : T
tFloat = TCon (MkTycon "Float" Star)

tDouble : T
tDouble = TCon (MkTycon "Double" Star)

tList : T
tList = TCon (MkTycon "[]" (KFun Star Star))

tArrow : T
tArrow = TCon (MkTycon "(->)" (KFun Star (KFun Star Star)))

tTuple2 : T
tTuple2  = TCon (MkTycon "(,)" (KFun Star (KFun Star Star)))

list : T -> T
list t = TApp tList t

pair : T -> T -> T
pair a b = TApp (TApp tTuple2 a) b

tString : T
tString = list tChar

infixr 4 ~>
(~>) : T -> T -> T
a ~> b = TApp (TApp tArrow a) b

-- extract kind of a type
interface HasKind t where
  kind : t -> Kind

HasKind Tyvar where
  kind (MkTyvar v k) = k

HasKind Tycon where
  kind (MkTycon v k) = k

HasKind T where
  kind (TCon tc) = kind tc
  kind (TVar u) = kind u
  kind (TApp t _) = case (kind t) of
                      (KFun _ k) => k
