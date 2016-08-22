module Infer

import Types
import TypeClass
import Unify
import TSTI
import Common
import Debug.Error
import Data.List

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

data Pat = PVar Id
         | PWildcard
         | PAs  Id Pat
         | PLit Literal
         | PNpk Id Integer
         | PCon Assump (List Pat)

mutual
  tiPats : List Pat -> TI (List Pred, List Assump, List T)
  tiPats pats = do psasts <- traverse tiPat pats
                   let ps = concat [ ps' | (ps', _, _) <- psasts ]
                   let as = concat [ as' | (_, as', _) <- psasts ]
                   let ts = [ t | (_, _, t) <- psasts ]
                   return (ps, as, ts)

  tiPat : Pat -> TI (List Pred, List Assump, T)
  tiPat (PVar i) = do v <- newTVar Star
                      return ([], [i :>: toScheme v], v)
  tiPat PWildcard = do v <- newTVar Star
                       return ([], [], v)
  tiPat (PAs i pat) = do (ps, as, t) <- tiPat pat
                         return (ps, (i :>: toScheme t) :: as, t)
  tiPat (PLit l) = do (ps, t) <- tiLit l
                      return (ps, [], t)
  tiPat (PNpk i k) = do t <- newTVar Star
                        return ([IsIn "Integral" t], [i :>: toScheme t], t)
  tiPat (PCon (i :>: sc) pats) = do (ps,as,ts) <- tiPats pats
                                    t'         <- newTVar Star
                                    (qs :=> t) <- freshInst sc
                                    unify t (foldr (~>) t' ts)
                                    return (ps ++ qs, as, t')

  data Expr = Var   Id
            | Lit   Literal
            | Const Assump
            | App   Expr Expr
            | Let   BindGroup Expr

  tiExpr : Infer Expr T
  tiExpr ce as (Var i) = do sc         <- find i as
                            (ps :=> t) <- freshInst sc
                            return (ps, t)
  tiExpr ce as (Const (i :>: sc)) = do (ps :=> t) <- freshInst sc
                                       return (ps, t)
  tiExpr ce as (Lit l) = do (ps,t) <- tiLit l
                            return (ps, t)
  tiExpr ce as (App e f) = do (ps,te) <- tiExpr ce as e
                              (qs,tf) <- tiExpr ce as f
                              t       <- newTVar Star
                              unify (tf ~> t) te
                              return (ps ++ qs, t)
  tiExpr ce as (Let bg e) = do (ps, as') <- tiBindGroup ce as bg
                               (qs, t)   <- tiExpr ce (as' ++ as) e
                               return (ps ++ qs, t)

  Alt : Type
  Alt = (List Pat, Expr)

  tiAlt : Infer Alt T
  tiAlt ce as (pats, e) = do (ps, as', ts) <- tiPats pats
                             (qs, t) <- tiExpr ce (as' ++ as) e
                             return (ps ++ qs, foldr (~>) t ts)

  tiAlts : ClassEnv -> List Assump -> List Alt -> T -> TI (List Pred)
  tiAlts ce as alts t = do psts <- traverse (tiAlt ce as) alts
                           traverse (unify t) (map snd psts)
                           return (concat (map fst psts))

  Ambiguity : Type
  Ambiguity = (Tyvar, List Pred)

  ambiguities : ClassEnv -> List Tyvar -> List Pred -> List Ambiguity
  ambiguities ce vs ps = [ (v, filter (\t => elem v $ tv t) ps) | v <- tv ps \\ vs ]

  numClasses : List Id
  numClasses  = ["Num", "Integral", "Floating", "Fractional", "Real", "RealFloat", "RealFrac"]

  stdClasses : List Id
  stdClasses  = ["Eq", "Ord", "Show", "Read", "Bounded", "Enum", "Ix", "Functor", "Monad", "MonadPlus"] ++ numClasses

  candidates : ClassEnv -> Ambiguity -> List T
  candidates ce (v, qs) = [ t' | t' <- defaults ce,
                                 all ((TVar v) ==) ts,
                                 any (\c => c `elem` numClasses) is,
                                 all (\c => c `elem` stdClasses) is,
                                 all (entail ce []) [ IsIn i t' | i <- is ] ]
    where is : List Id
          is = [ i | IsIn i t <- qs ]
          ts : List T
          ts = [ t | IsIn i t <- qs ]

  withDefaults : Monad m => (List Ambiguity -> List T -> a) -> ClassEnv -> List Tyvar -> List Pred -> m a
  withDefaults f ce vs ps = (any null tss) ? (error "cannot resolve ambiguity")
                          : return $ f vps $ map (\l => case l of
                                                          [] => error "type list is empty"
                                                          (h :: _) => h) tss
    where vps : List Ambiguity
          vps = ambiguities ce vs ps
          tss : List (List T)
          tss = map (candidates ce) vps

  defaultedPreds : Monad m => ClassEnv -> List Tyvar -> List Pred -> m (List Pred)
  defaultedPreds = withDefaults (\vps, ts => concat (map snd vps))

  defaultSubst : Monad m => ClassEnv -> List Tyvar -> List Pred -> m Subst
  defaultSubst = withDefaults (\vps, ts => zip (map fst vps) ts)

  split : Monad m => ClassEnv -> List Tyvar -> List Tyvar -> List Pred -> m (List Pred, List Pred)
  split ce fs gs ps = do ps' <- reduce ce ps
                         let (ds, rs) = partition (all (\t => t `elem` fs) . tv) ps'
                         rs' <- defaultedPreds ce (fs ++ gs) rs
                         return (ds, rs \\ rs')

  Expl : Type
  Expl = (Id, Scheme, List Alt)

  tiExpl : ClassEnv -> List Assump -> Expl -> TI (List Pred)
  tiExpl ce as (i, sc, alts) = do (qs :=> t) <- freshInst sc
                                  ps         <- tiAlts ce as alts t
                                  s          <- getSubst
                                  let qs'    = apply s qs
                                  let t'     = apply s t
                                  let fs     = tv (apply s as)
                                  let gs     = tv t' \\ fs
                                  let sc'    = quantify gs (qs' :=> t')
                                  let ps'    = filter (not . entail ce qs') (apply s ps)
                                  (ds,rs)    <- split ce fs gs ps'
                                  (sc /= sc') ? (error "signature too general")
                                : (not $ null rs) ? (error "context too weak")
                                : return ds

  Impl : Type
  Impl = (Id, List Alt)

  restricted : List Impl -> Bool
  restricted bs = any simple bs
    where simple (i, alts) = any (null . fst) alts

  tiImpls : ClassEnv -> List Assump -> List Impl -> TI (List Pred, List Assump)
  tiImpls ce as bs = do ts <- traverse (\_ => newTVar Star) bs
                        let is    = map fst bs
                        let scs   = map toScheme ts
                        let as'   = zipWith (:>:) is scs ++ as
                        let altss = map snd bs
                        pss <- sequence (zipWith (tiAlts ce as') altss ts)
                        s   <- getSubst
                        let ps'   = apply s (concat pss)
                        let ts'   = apply s ts
                        let fs    = tv (apply s as)
                        let vss   = map tv ts'
                        let gs    = foldr1 union vss \\ fs
                        (ds,rs) <- split ce fs (foldr1 intersect vss) ps'
                        if restricted bs then
                            let gs'  = gs \\ tv rs
                                scs' = map (quantify gs' . (\t => [] :=> t)) ts'
                            in return (ds++rs, zipWith (:>:) is scs')
                        else
                            let scs' = map (quantify gs . (\t => rs :=> t)) ts'
                            in return (ds, zipWith (:>:) is scs')

  BindGroup : Type
  BindGroup = (List Expl, List (List Impl))

  tiBindGroup : Infer BindGroup (List Assump)
  tiBindGroup ce as (es,iss) =
    do let as' = [ v :>: sc | (v,sc,alts) <- es ]
       (ps, as'') <- tiSeq tiImpls ce (as' ++ as) iss
       qss        <- traverse (tiExpl ce (as'' ++ as' ++ as)) es
       return (ps ++ concat qss, as'' ++ as')

  tiSeq : (ClassEnv -> List Assump -> bg -> TI (List Pred, List Assump)) -> (ClassEnv -> List Assump -> List bg -> TI (List Pred, List Assump))
  tiSeq _ _ _ [] = return ([], [])
  tiSeq ti ce as (bs :: bss) = do (ps, as')  <- ti ce as bs
                                  (qs, as'') <- tiSeq ti ce (as' ++ as) bss
                                  return (ps ++ qs, as'' ++ as')
