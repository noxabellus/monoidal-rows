module Infer where

import Data.Functor ((<&>))
import Data.Bifunctor

import Data.Map.Strict qualified as Map
import Data.List qualified as List

import Control.Monad.Except
import Control.Monad.State.Class

import Util
import Pretty
import Ast
import Subst
import Ti
import Solve




generalize :: TVars a => Env -> Qualified a -> Ti (Scheme a)
generalize env qt = do
    evs <- ftvsM env
    tvs <- ftvsM qt
    let xvs = tvs List.\\ evs
        m = zip xvs [0..] <&> \(tv, i) -> (tv, BoundType i $ kindOf tv)
        bvs = snd <$> m
        g = Map.fromList $ second (TVar . TvBound) <$> m
    s <- gets snd
    let qt' = apply (g <> s) qt
    pure (Forall bvs qt')

instantiate :: TVars a => Scheme a -> Ti (Qualified a)
instantiate (Forall bvs qt) = do
    i <- Map.fromList <$> forM bvs \bv ->
        (TvBound bv, ) <$> fresh (kindOf bv)
    pure (apply i qt)

instantiateWith :: (Pretty a, TVars a) => [Type] -> Scheme a -> Ti (Qualified a)
instantiateWith ps sc@(Forall bvs qt) = do
    catchError do
            when (length bvs /= length ps) do
                fail $ "expected " <> show (length bvs) <> " type arguments, got " <> show (length ps)
            unless (all (uncurry (==)) $ zip (kindOf <$> bvs) (kindOf <$> ps)) do
                fail $ "kind mismatch: " <> pretty bvs <> " vs " <> pretty (kindOf <$> ps)
        \e ->
            throwError $ "cannot instantiate scheme " <> pretty sc <> " with parameters " <> pretty ps <> ": " <> e

    let i = Map.fromList $ zip (TvBound <$> bvs) ps
    pure (apply i qt)


infer :: Env -> UntypedTerm -> Ti (Qualified (TypedTerm, Evidence))
infer env ut = do
    -- iid <- getId
    -- traceM $ replicate iid ' ' <> "inferring " <> pretty ut
    -- res <-
    case ut of
        Var v -> do
            cs :=> t <- envLookup env v >>= instantiate
            pure $ cs :=>
                (Var v `Ann` t, TEffectRowNil)
        
        Unit -> pure $ [] :=>
            (Unit `Ann` TUnit, TEffectRowNil)

        Int i -> pure $ [] :=>
            (Int i `Ann` TInt, TEffectRowNil)

        Lambda p x -> do
            cs'p :=> (p'@(PAnnOf t'p), e'p) <- inferPatt env p
            cs'x :=> (x'@(AnnOf t'x), es) <- infer (e'p <> env) x
            pure $ cs'p <> cs'x :=>
                (Lambda p' x' `Ann` TFun t'p t'x es, TEffectRowNil)

        App f x -> do
            cs'x :=> (x'@(AnnOf t'x), es'x) <- infer env x
            t'y <- fresh KType
            es'a <- fresh KEffectRow
            cs'f :=> (f', es'f) <- check env (TFun t'x t'y es'a) f
            es'fx <- fresh KEffectRow
            es <- fresh KEffectRow
            pure $ cs'x <> cs'f <> fmap CRow [ConcatRow es'x es'f es'fx, ConcatRow es'fx es'a es] :=>
                (App f' x' `Ann` t'y, es)

        Ann x t -> do
            cs :=> x' <- check env t x
            pure $ cs :=> x'

        Match x cs -> do
            cs'x :=> (x'@(AnnOf t'x), es'x) <- infer env x
            t'r <- fresh KType
            ccs :=> (cs', es) <-
                foldByM (cs'x :=> (mempty, es'x)) cs
                \(p, y) (ccs :=> (cs', es'cs)) -> do
                    cs'p :=> (p', e'p) <- checkPatt env t'x p
                    cs'y :=> (y', es'y) <- check (e'p <> env) t'r y
                    es <- fresh KEffectRow
                    pure $ cs'p <> cs'y <> [CRow $ ConcatRow es'cs es'y es] <> ccs :=>
                        ((p', y') : cs', es)
            pure $ ccs :=>
                (Match x' cs' `Ann` t'r, es)

        ProductConstructor fs -> do
            cs'm :=> (r, m', es'm) <-
                foldByM ([] :=> (mempty, mempty, TEffectRowNil)) fs
                \(n, x) (cs'm :=> (r, m', es'm)) -> do
                    cs'x :=> (x'@(AnnOf t'x), es'x) <- infer env x
                    es <- fresh KEffectRow
                    pure $ cs'x <> [CRow $ ConcatRow es'm es'x es] <> cs'm :=>
                        (Map.insert n t'x r, (n, x') : m', es)
            pure $ cs'm :=>
                (ProductConstructor m' `Ann` TProd (TDataRow r), es'm)

        ProductConcat a b -> do
            cc@(ConcatRow r'a r'b r'c) <- freshDataConcat
            cs'a :=> (a', es'a) <- check env (TProd r'a) a
            cs'b :=> (b', es'b) <- check env (TProd r'b) b
            es <- fresh KEffectRow
            pure $ CRow cc : cs'a <> cs'b <> [CRow $ ConcatRow es'a es'b es] :=>
                (ProductConcat a' b' `Ann` TProd r'c, es)

        ProductNarrow x -> do
            sc@(SubRow r'a r'b) <- freshDataSub
            cs'x :=> (x', es'x) <- check env (TProd r'b) x
            pure $ CRow sc : cs'x :=>
                (ProductNarrow x' `Ann` TProd r'a, es'x)

        ProductSelect x n -> do
            t <- fresh KType
            t'r <- fresh KDataRow
            cs'x :=> (x', es'x) <- check env (TProd t'r) x
            pure $ CRow (SubRow (dataSingleton n t) t'r) : cs'x :=>
                (ProductSelect x' n `Ann` t, es'x)

        SumConstructor n x -> do
            t'r <- fresh KDataRow
            cs'x :=> (x'@(AnnOf t'x), es'x) <- infer env x
            pure $ CRow (SubRow (dataSingleton n t'x) t'r) : cs'x :=>
                (SumConstructor n x' `Ann` TSum t'r, es'x)

        SumExpand x -> do
            cs@(SubRow r'a r'b) <- freshDataSub
            cs'x :=> (x', es'x) <- check env (TSum r'a) x
            pure $ CRow cs : cs'x :=>
                (SumExpand x' `Ann` TSum r'b, es'x)
        
        Handler t hm b -> do
            let (effName, effArgs) = splitEffectType t
            cs'em :=> em <- effLookup env effName >>= instantiateWith effArgs

            when (Map.keys hm /= Map.keys em) do
                fail $ "handler effect mismatch: expected cases " <> pretty (Map.keys hm)
                    <> ", got " <> pretty (Map.keys em)

            cs'hm :=> (hm', es'hm) <-
                foldByM ([] :=> (mempty, TEffectRowNil)) (Map.toList em)
                \(caseName, (expectedIn, expectedOut)) (cs'hm :=> (hm', es'hm)) -> do
                    let (p, x) = hm Map.! caseName
                    cs'p :=> (p', env'p) <- checkPatt env expectedIn p
                    cs'x :=> (x', es'x) <- check (env'p <> env) expectedOut x
                    es <- fresh KEffectRow
                    pure $ CRow (ConcatRow es'x es'hm es)
                         : cs'p <> cs'x <> cs'x <> cs'hm :=>
                            (Map.insert caseName (p', x') hm', es)
            
            cs'b :=> (b'@(AnnOf t'b), es'b) <- infer env b
            [es'rb, es] <- freshN [KEffectRow, KEffectRow]
            pure $ CRow (ConcatRow (effectSingleton t) es'rb es'b)
                 : CRow (ConcatRow es'rb es'hm es)
                 : cs'b <> cs'hm <> cs'em :=>
                    (Handler t hm' b' `Ann` t'b, es)

    -- res <$ traceM do
    --     replicate iid ' ' <> "result " <> pretty res
    where
    splitEffectType = \case
        TApp a b -> let (name, args) = splitEffectType a in (name, args <> [b])
        TCon (n, _) -> (n, [])
        t -> error $ "expected effect type/effect type application, got " <> pretty t

check :: Env -> Type -> UntypedTerm -> Ti (Qualified (TypedTerm, Evidence))
check env tx ut = do
    -- cid <- getId
    -- traceM $ replicate cid ' ' <> "checking " <> pretty tx <> " :: " <> pretty ut
    -- res <-
    case (tx, ut) of
        (TInt, Int i) -> pure $ [] :=>
            (Int i `Ann` TInt, TEffectRowNil)

        (TUnit, Unit) -> pure $ [] :=>
            (Unit `Ann` TUnit, TEffectRowNil)

        (TFun a b e, Lambda p x) -> do
            cs'p :=> (p', e'p) <- checkPatt env a p
            cs'x :=> (x', es'x) <- check (e'p <> env) b x
            pure $ cs'p <> cs'x <> [CEqual (e, es'x)] :=>
                (Lambda p' x' `Ann` TFun a b e, TEffectRowNil)

        (t@(TProd (TDataRow r)), x@(ProductConstructor fs)) -> do
            cs'm :=> (m', es'm) <-
                foldByM ([] :=> (mempty, TEffectRowNil)) fs
                \(n, v) (cs'm :=> (m', es'm)) ->
                    case Map.lookup n r of
                        Just t'v -> do
                            cs'v :=> (v', es'v) <- check env t'v v
                            es <- fresh KEffectRow
                            pure $ cs'v <> cs'm <> [CRow $ ConcatRow es'm es'v es] :=>
                                ((n, v') : m', es)
                        _ -> fail $ "field " <> n <> " of product constructor " <> pretty x <> " not in type " <> pretty t
            pure $ cs'm :=>
                (ProductConstructor m' `Ann` t, es'm)

        (TProd r'c, ProductConcat a b) -> do
            [r'a, r'b] <- freshN [KDataRow, KDataRow]
            cs'a :=> (a', es'a) <- check env (TProd r'a) a
            cs'b :=> (b', es'b) <- check env (TProd r'b) b
            es <- fresh KEffectRow
            pure $ cs'a <> cs'b <> fmap CRow [ConcatRow r'a r'b r'c, ConcatRow es'a es'b es] :=>
                (ProductConcat a' b' `Ann` TProd r'c, es)

        (TProd r'a, ProductNarrow x) -> do
            r'b <- fresh KDataRow
            cs'x :=> (x', es'x) <- check env (TProd r'b) x
            pure $ cs'x <> [CRow (SubRow r'a r'b)] :=>
                (ProductNarrow x' `Ann` TProd r'a, es'x)

        (t, ProductSelect x n) -> do
            t'r <- fresh KDataRow
            cs'x :=> (x', es'x) <- check env (TProd t'r) x
            pure $ cs'x <> [CRow (SubRow (dataSingleton n t) t'r)] :=>
                (ProductSelect x' n `Ann` t, es'x)

        (t@(TSum r'b), SumConstructor n x)
            | TDataRow m <- r'b ->
                case Map.lookup n m of
                    Just t'x -> do
                        cs'x :=> (x', es'x) <- check env t'x x
                        pure $ cs'x :=>
                            (SumConstructor n x' `Ann` TSum r'b, es'x)
                    _ -> fail $ "variant " <> n <> " of sum constructor " <> pretty x <> " not in type " <> pretty t
            | otherwise -> do
                cs'x :=> (x'@(AnnOf t'x), es'x) <- infer env x
                pure $ cs'x <> [CRow (SubRow (dataSingleton n t'x) r'b)] :=>
                    (SumConstructor n x' `Ann` TSum r'b, es'x)

        (TSum r'b, SumExpand x) -> do
            r'a <- fresh KDataRow
            cs'x :=> (x', es'x) <- check env (TSum r'a) x
            pure $ cs'x <> [CRow (SubRow r'a r'b)] :=>
                (SumExpand x' `Ann` TSum r'b, es'x)

        (t, x) -> do
            cs'x :=> (x'@(AnnOf t'x), es'x) <- infer env x
            pure $ cs'x <> [CEqual (t, t'x)] :=>
                (x', es'x)

    -- res <$ traceM do
    --     replicate cid ' ' <> "result " <> pretty res



inferPatt :: Env -> UntypedPatt -> Ti (Qualified (TypedPatt, Env))
inferPatt env = \case
    PVar v -> do
        t'v <- fresh KType
        pure $ [] :=>
            (PVar v `PAnn` t'v, envSingleton v t'v)

    PUnit -> pure $ [] :=>
        (PUnit `PAnn` TUnit, mempty)

    PInt i -> pure $ [] :=>
        (PInt i `PAnn` TInt, mempty)

    PProductConstructor m -> do
        r'a <- fresh KDataRow
        (cs'm :=> (mr'm, m', e'm)) <-
            foldByM mempty (Map.toList m)
            \(n, p) (cs'm :=> (mr'm, m', e'm)) -> do
                cs'p :=> (p'@(PAnnOf t'p), e'p) <- inferPatt env p
                pure (cs'p <> cs'm :=> (Map.insert n t'p mr'm, Map.insert n p' m', e'p <> e'm))
        pure $ CRow (SubRow (TDataRow mr'm) r'a) : cs'm :=>
            (PProductConstructor m' `PAnn` TProd r'a, e'm)

    PSumConstructor n p -> do
        r'a <- fresh KDataRow
        cs'p :=> (p'@(PAnnOf t'p), e'p) <- inferPatt env p
        pure $ CRow (SubRow (dataSingleton n t'p) r'a) : cs'p :=>
            (PSumConstructor n p' `PAnn` TSum r'a, e'p)

    PWildcard -> do
        t'w <- fresh KType
        pure $ [] :=>
            (PWildcard `PAnn` t'w, mempty)

    PAnn p t -> do
        cs'p :=> (p'@(PAnnOf t'p), e'p) <- inferPatt env p
        pure $ CEqual (t, t'p) : cs'p :=>
            (p', e'p)

checkPatt :: Env -> Type -> UntypedPatt -> Ti (Qualified (TypedPatt, Env))
checkPatt env = curry \case
    (TInt, PInt i) -> pure $ [] :=>
        (PInt i `PAnn` TInt, env)
    (TUnit, PUnit) -> pure $ [] :=>
        (PUnit `PAnn` TUnit, env)

    (t, PWildcard) -> pure $ [] :=>
        (PWildcard `PAnn` t, env)

    (TProd r'a, PProductConstructor m) -> do
        cs'm :=> (mr'm, m', e'm) <-
            foldByM mempty (Map.toList m)
            \(n, p) (cs'm :=> (mr'm, m', e'm)) -> do
                cs'p :=> (p'@(PAnnOf t'p), e'p) <- inferPatt env p
                pure $ cs'p <> cs'm :=>
                    (Map.insert n t'p mr'm, Map.insert n p' m', e'p <> e'm)
        pure $ CRow (SubRow (TDataRow mr'm) r'a) : cs'm :=>
            (PProductConstructor m' `PAnn` TProd r'a, e'm)

    (TSum r'a, PSumConstructor n p) -> do
        cs'p :=> (p'@(PAnnOf t'p), e'p) <- inferPatt env p
        pure $ CRow (SubRow (dataSingleton n t'p) r'a) : cs'p :=>
            (PSumConstructor n p' `PAnn` TSum r'a, e'p)

    (t, p) -> do
        cs'p :=> (p'@(PAnnOf t'p), e'p) <- inferPatt env p
        pure $ CEqual (t, t'p) : cs'p :=> 
            (p', e'p)





ti :: Env -> UntypedTerm -> Either String (Scheme (Type, TypedTerm), Subst)
ti env x = second snd <$> runTi action 0 (0, mempty) where
    action = do
        cs :=> (x'@(AnnOf t'x), es'x) <- infer env x
        cs' <- solve (CEqual (TEffectRowNil, es'x) : cs)
        generalize env (cs' :=> (t'x, x'))



-- FIXME: ????
-- tc :: Env -> Type -> UntypedTerm -> Either String (Scheme TypedTerm)
-- tc env t x = fst <$> flip runTi (0, mempty) do
--     cs :=> x' <- check env t x
--     cs' <- solve cs
--     generalize env (cs' :=> x')

