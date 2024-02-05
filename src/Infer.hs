module Infer where

import Data.Bifunctor

import Data.Map.Strict qualified as Map

import Control.Monad.Except

import Util
import Pretty
import Ast
import Subst
import Ti
import Solve



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
            pure $ cs'x <> cs'f <> [CConcatRow es'x es'f es'fx, CConcatRow es'fx es'a es] :=>
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
                    pure $ cs'p <> cs'y <> [CConcatRow es'cs es'y es] <> ccs :=>
                        ((p', y') : cs', es)
            pure $ ccs :=>
                (Match x' cs' `Ann` t'r, es)

        ProductConstructor fs -> do
            cs'm :=> (r, m', es'm) <-
                foldByM ([] :=> (mempty, mempty, TEffectRowNil)) fs
                \(n, x) (cs'm :=> (r, m', es'm)) -> do
                    cs'x :=> (x'@(AnnOf t'x), es'x) <- infer env x
                    es <- fresh KEffectRow
                    pure $ cs'x <> [CConcatRow es'm es'x es] <> cs'm :=>
                        (Map.insert n t'x r, (n, x') : m', es)
            d <- fresh KType
            pure $ CProd d (TDataRow r) : cs'm :=>
                (ProductConstructor m' `Ann` d, es'm)

        ProductConcat a b -> do
            cc@(ConcatRow r'a r'b r'c) <- freshDataConcat
            [d'a, d'b, d'c] <- freshN [KType, KType, KType]
            cs'a :=> (a', es'a) <- check env (TProd d'a r'a) a
            cs'b :=> (b', es'b) <- check env (TProd d'b r'b) b
            es <- fresh KEffectRow
            pure $ CProd d'a r'a : CProd d'b r'b : CProd d'c r'c : CRow cc
                 : cs'a <> cs'b <> [CConcatRow es'a es'b es] :=>
                    (ProductConcat a' b' `Ann` d'c, es)

        ProductNarrow x -> do
            sc@(SubRow r'a r'b) <- freshDataSub
            [d'a, d'b] <- freshN [KType, KType]
            cs'x :=> (x', es'x) <- check env (TProd d'b r'b) x
            pure $ CProd d'a r'a : CProd d'b r'b : CRow sc : cs'x :=>
                (ProductNarrow x' `Ann` d'a, es'x)

        ProductSelect x n -> do
            [t, d'r, t'r] <- freshN [KType, KType, KDataRow]
            cs'x :=> (x', es'x) <- check env (TProd d'r t'r) x
            pure $ CProd d'r t'r : CSubRow (dataSingleton n t) t'r : cs'x :=>
                (ProductSelect x' n `Ann` t, es'x)

        SumConstructor n x -> do
            [d'r, t'r] <- freshN [KType, KDataRow]
            cs'x :=> (x'@(AnnOf t'x), es'x) <- infer env x
            pure $ CSum d'r t'r : CSubRow (dataSingleton n t'x) t'r : cs'x :=>
                (SumConstructor n x' `Ann` d'r, es'x)

        SumExpand x -> do
            cs@(SubRow r'a r'b) <- freshDataSub
            [d'a, d'b] <- freshN [KType, KType]
            cs'x :=> (x', es'x) <- check env (TSum d'a r'a) x
            pure $ CSum d'a r'a : CSum d'b r'b : CRow cs : cs'x :=>
                (SumExpand x' `Ann` d'b, es'x)
        
        Handler t hm b -> do
            (effName, effArgs) <- maybe
                (fail $ "expected type constructor (with optional args), got: " <> pretty t)
                pure
                (splitTypeCon t)

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
                    pure $ CConcatRow es'x es'hm es
                         : cs'p <> cs'x <> cs'x <> cs'hm :=>
                            (Map.insert caseName (p', x') hm', es)
            
            cs'b :=> (b'@(AnnOf t'b), es'b) <- infer env b
            [es'rb, es] <- freshN [KEffectRow, KEffectRow]
            pure $ CConcatRow (effectSingleton t) es'rb es'b
                 : CConcatRow es'rb es'hm es
                 : cs'b <> cs'hm <> cs'em :=>
                    (Handler t hm' b' `Ann` t'b, es)

    -- res <$ traceM do
    --     replicate iid ' ' <> "result " <> pretty res



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

        (t@(TProd d (TDataRow r)), x@(ProductConstructor fs)) -> do
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
                (ProductConstructor m' `Ann` d, es'm)

        (TProd d'c r'c, ProductConcat a b) -> do
            [d'a, r'a, d'b, r'b] <- freshN [KType, KDataRow, KType, KDataRow]
            cs'a :=> (a', es'a) <- check env (TProd d'a r'a) a
            cs'b :=> (b', es'b) <- check env (TProd d'b r'b) b
            es <- fresh KEffectRow
            pure $ CProd d'a r'a : CProd d'b r'b
                 : cs'a <> cs'b <> [CConcatRow r'a r'b r'c, CConcatRow es'a es'b es] :=>
                    (ProductConcat a' b' `Ann` d'c, es)

        (TProd d'a r'a, ProductNarrow x) -> do
            [d'b, r'b] <- freshN [KType, KDataRow]
            cs'x :=> (x', es'x) <- check env (TProd d'b r'b) x
            pure $ CProd d'b r'b : cs'x <> [CSubRow r'a r'b] :=>
                (ProductNarrow x' `Ann` d'a, es'x)

        (t, ProductSelect x n) -> do
            [d'r, t'r] <- freshN [KType, KDataRow]
            cs'x :=> (x', es'x) <- check env (TProd d'r t'r) x
            pure $ CProd d'r t'r : cs'x <> [CSubRow (dataSingleton n t) t'r] :=>
                (ProductSelect x' n `Ann` t, es'x)

        (t@(TSum d'b r'b), SumConstructor n x)
            | TDataRow m <- r'b ->
                case Map.lookup n m of
                    Just t'x -> do
                        cs'x :=> (x', es'x) <- check env t'x x
                        pure $ cs'x :=>
                            (SumConstructor n x' `Ann` d'b, es'x)
                    _ -> fail $ "variant " <> n <> " of sum constructor " <> pretty x <> " not in type " <> pretty t
            | otherwise -> do
                cs'x :=> (x'@(AnnOf t'x), es'x) <- infer env x
                pure $ cs'x <> [CSubRow (dataSingleton n t'x) r'b] :=>
                    (SumConstructor n x' `Ann` d'b, es'x)

        (TSum d'b r'b, SumExpand x) -> do
            [d'a, r'a] <- freshN [KType, KDataRow]
            cs'x :=> (x', es'x) <- check env (TSum d'a r'a) x
            pure $ CSum d'a r'a : cs'x <> [CSubRow r'a r'b] :=>
                (SumExpand x' `Ann` d'b, es'x)

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
        [d'a, r'a] <- freshN [KType, KDataRow]
        (cs'm :=> (mr'm, m', e'm)) <-
            foldByM mempty (Map.toList m)
            \(n, p) (cs'm :=> (mr'm, m', e'm)) -> do
                cs'p :=> (p'@(PAnnOf t'p), e'p) <- inferPatt env p
                pure (cs'p <> cs'm :=> (Map.insert n t'p mr'm, Map.insert n p' m', e'p <> e'm))
        pure $ CProd d'a r'a : CSubRow (TDataRow mr'm) r'a : cs'm :=>
            (PProductConstructor m' `PAnn` d'a, e'm)

    PSumConstructor n p -> do
        [d'a, r'a] <- freshN [KType, KDataRow]
        cs'p :=> (p'@(PAnnOf t'p), e'p) <- inferPatt env p
        pure $ CSum d'a r'a : CSubRow (dataSingleton n t'p) r'a : cs'p :=>
            (PSumConstructor n p' `PAnn` d'a, e'p)

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

    (TProd d'a r'a, PProductConstructor m) -> do
        cs'm :=> (mr'm, m', e'm) <-
            foldByM mempty (Map.toList m)
            \(n, p) (cs'm :=> (mr'm, m', e'm)) -> do
                cs'p :=> (p'@(PAnnOf t'p), e'p) <- inferPatt env p
                pure $ cs'p <> cs'm :=>
                    (Map.insert n t'p mr'm, Map.insert n p' m', e'p <> e'm)
        pure $ CSubRow (TDataRow mr'm) r'a : cs'm :=>
            (PProductConstructor m' `PAnn` d'a, e'm)

    (TSum d'a r'a, PSumConstructor n p) -> do
        cs'p :=> (p'@(PAnnOf t'p), e'p) <- inferPatt env p
        pure $ CSubRow (dataSingleton n t'p) r'a : cs'p :=>
            (PSumConstructor n p' `PAnn` d'a, e'p)

    (t, p) -> do
        cs'p :=> (p'@(PAnnOf t'p), e'p) <- inferPatt env p
        pure $ CEqual (t, t'p) : cs'p :=> 
            (p', e'p)





ti :: Env -> UntypedTerm -> Either String (Scheme (Type, TypedTerm), Subst)
ti env x = second snd <$> runTi action 0 (0, mempty) where
    action = do
        cs :=> (x'@(AnnOf t'x), es'x) <- infer env x
        cs' <- solve env (CEqual (TEffectRowNil, es'x) : cs)
        generalize env (cs' :=> (t'x, x'))



-- FIXME: ????
-- tc :: Env -> Type -> UntypedTerm -> Either String (Scheme TypedTerm)
-- tc env t x = fst <$> flip runTi (0, mempty) do
--     cs :=> x' <- check env t x
--     cs' <- solve cs
--     generalize env (cs' :=> x')

