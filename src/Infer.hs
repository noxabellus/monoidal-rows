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

        ProductConstructor (Left fs) -> do
            cs'm :=> (r, m', es'm) <-
                foldByM ([] :=> (mempty, mempty, TEffectRowNil)) (zip [0..] fs)
                \(i, x) (cs'm :=> (r, m', es'm)) -> do
                    cs'x :=> (x'@(AnnOf t'x), es'x) <- infer env x
                    es <- fresh KEffectRow
                    v'n <- fresh KString
                    pure $ cs'x <> [CConcatRow es'm es'x es] <> cs'm :=>
                        (((TcInt i, v'n), t'x) : r, x' : m', es)
            d <- fresh KType
            pure $ CProd d (TDataRow r) : cs'm :=>
                (ProductConstructor (Left m') `Ann` d, es'm)

        ProductConstructor (Right fs) -> do
            cs'm :=> (r, m', es'm) <-
                foldByM ([] :=> (mempty, mempty, TEffectRowNil)) fs
                \(n, x) (cs'm :=> (r, m', es'm)) -> do
                    cs'x :=> (x'@(AnnOf t'x), es'x) <- infer env x
                    es <- fresh KEffectRow
                    v'x <- fresh KInt
                    pure $ cs'x <> [CConcatRow es'm es'x es] <> cs'm :=>
                        (((v'x, TcString n), t'x) : r, (n, x') : m', es)
            d <- fresh KType
            pure $ CProd d (TDataRow r) : cs'm :=>
                (ProductConstructor (Right m') `Ann` d, es'm)

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

        ProductSelect x (Left l) -> do
            [t, d'r, t'r] <- freshN [KType, KType, KDataRow]
            cs'x :=> (x', es'x) <- check env (TProd d'r t'r) x
            v'n <- fresh KString
            pure $ CProd d'r t'r : CSubRow (dataSingleton ((TcInt l, v'n), t)) t'r : cs'x :=>
                (ProductSelect x' (Left l) `Ann` t, es'x)
                
        ProductSelect x (Right n) -> do
            [t, d'r, t'r] <- freshN [KType, KType, KDataRow]
            cs'x :=> (x', es'x) <- check env (TProd d'r t'r) x
            v'l <- fresh KInt
            pure $ CProd d'r t'r : CSubRow (dataSingleton ((v'l, TcString n), t)) t'r : cs'x :=>
                (ProductSelect x' (Right n) `Ann` t, es'x)

        SumConstructor (Left l) x -> do
            [d'r, t'r] <- freshN [KType, KDataRow]
            cs'x :=> (x'@(AnnOf t'x), es'x) <- infer env x
            v'n <- fresh KString
            pure $ CSum d'r t'r : CSubRow (dataSingleton ((TcInt l, v'n), t'x)) t'r : cs'x :=>
                (SumConstructor (Left l) x' `Ann` d'r, es'x)

        SumConstructor (Right n) x -> do
            [d'r, t'r] <- freshN [KType, KDataRow]
            cs'x :=> (x'@(AnnOf t'x), es'x) <- infer env x
            v'l <- fresh KInt
            pure $ CSum d'r t'r : CSubRow (dataSingleton ((v'l, TcString n), t'x)) t'r : cs'x :=>
                (SumConstructor (Right n) x' `Ann` d'r, es'x)

        SumExpand x -> do
            cs@(SubRow r'a r'b) <- freshDataSub
            [d'a, d'b] <- freshN [KType, KType]
            cs'x :=> (x', es'x) <- check env (TSum d'a r'a) x
            pure $ CSum d'a r'a : CSum d'b r'b : CRow cs : cs'x :=>
                (SumExpand x' `Ann` d'b, es'x)
        
        Handler t hm r b -> do
            (effName, effArgs) <- maybe
                (fail $ "expected type constructor (with optional args), got: "
                    <> pretty t)
                pure
                (splitTypeCon t)

            cs'em :=> em <- effLookup env effName >>= instantiateWith effArgs

            when (Map.keys hm /= Map.keys em) do
                fail $ "handler effect mismatch: expected cases "
                    <> pretty (Map.keys hm)
                    <> ", got " <> pretty (Map.keys em)

            [t'b, es'rb, es'] <- freshN [KType, KEffectRow, KEffectRow]

            cs'r :=> (r', t'r, es'r) <- case r of
                Just (p, x) -> do
                    cs'p :=> (p', e'p) <- checkPatt env t'b p
                    cs'x :=> (x'@(AnnOf t'x), es'x) <- infer (e'p <> env) x
                    pure $ cs'p <> cs'x :=>
                        (Just (p', x'), t'x, es'x)
                _ -> pure $ [] :=>
                    (Nothing, t'b, TEffectRowNil)

            cs'hm :=> (hm', es'hm) <-
                foldByM (cs'r :=> (mempty, es'r)) (Map.toList em)
                \(caseName, (expectedIn, expectedOutQ))
                 (cs'hm :=> (hm', es'hm)) -> do
                    expectedOut <- instantiate expectedOutQ
                    let (p, x) = hm Map.! caseName
                    cs'p :=> (p', env'p) <- checkPatt env expectedIn p
                    cs'x :=> (x', es'x) <-
                        check
                            (envSingleton "continue"
                                (TFun expectedOut t'r es'rb)
                            <> env'p <> env)
                            t'r
                            x
                    es <- fresh KEffectRow
                    pure $ CConcatRow es'x es'hm es
                         : cs'p <> cs'x <> cs'x <> cs'hm :=>
                            (Map.insert caseName (p', x') hm', es)
            
            cs'b :=> (b', es'b) <- check env t'b b
            pure $ CConcatRow (effectSingleton t) es'rb es'b
                 : CConcatRow es'rb es'hm es'
                 : cs'b <> cs'hm <> cs'em :=>
                    (Handler t hm' r' b' `Ann` t'r, es')

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
            pure $ cs'p <> cs'x <> [CEqual e es'x] :=>
                (Lambda p' x' `Ann` TFun a b e, TEffectRowNil)

        (TProd d r, ProductConstructor (Left fs)) -> do
            cs'm :=> (r', m', es'm) <-
                foldByM ([] :=> (mempty, mempty, TEffectRowNil)) (zip [0..] fs)
                \(i, v) (cs'm :=> (r', m', es'm)) -> do
                    cs'v :=> (v'@(AnnOf t'v), es'v) <- infer env v
                    es <- fresh KEffectRow
                    v'n <- fresh KString
                    pure $ CConcatRow es'm es'v es : cs'v <> cs'm :=>
                        (((TcInt i, v'n), t'v) : r', v' : m', es)
            pure $ CEqual r (TDataRow r') : cs'm :=>
                (ProductConstructor (Left m') `Ann` d, es'm)

        (TProd d r, ProductConstructor (Right fs)) -> do
            cs'm :=> (r', m', es'm) <-
                foldByM ([] :=> (mempty, mempty, TEffectRowNil)) fs
                \(n, v) (cs'm :=> (r', m', es'm)) -> do
                    cs'v :=> (v'@(AnnOf t'v), es'v) <- infer env v
                    es <- fresh KEffectRow
                    v'l <- fresh KInt
                    pure $ CConcatRow es'm es'v es : cs'v <> cs'm :=>
                        (((v'l, TcString n), t'v) : r', (n, v') : m', es)
            pure $ CEqual r (TDataRow r') : cs'm :=>
                (ProductConstructor (Right m') `Ann` d, es'm)

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

        (t, ProductSelect x (Left l)) -> do
            [d'r, t'r] <- freshN [KType, KDataRow]
            cs'x :=> (x', es'x) <- check env (TProd d'r t'r) x
            v'n <- fresh KString
            pure $ CProd d'r t'r : cs'x <> [CSubRow (dataSingleton ((TcInt l, v'n), t)) t'r] :=>
                (ProductSelect x' (Left l) `Ann` t, es'x)

        (t, ProductSelect x (Right n)) -> do
            [d'r, t'r] <- freshN [KType, KDataRow]
            cs'x :=> (x', es'x) <- check env (TProd d'r t'r) x
            v'l <- fresh KInt
            pure $ CProd d'r t'r : cs'x <> [CSubRow (dataSingleton ((v'l, TcString n), t)) t'r] :=>
                (ProductSelect x' (Right n) `Ann` t, es'x)

        (TSum d'b r'b, SumConstructor (Left l) x) -> do
                cs'x :=> (x'@(AnnOf t'x), es'x) <- infer env x
                v'n <- fresh KString
                pure $ cs'x <> [CSubRow (dataSingleton ((TcInt l, v'n), t'x)) r'b] :=>
                    (SumConstructor (Left l) x' `Ann` d'b, es'x)

        (TSum d'b r'b, SumConstructor (Right n) x) -> do
                cs'x :=> (x'@(AnnOf t'x), es'x) <- infer env x
                v'l <- fresh KInt
                pure $ cs'x <> [CSubRow (dataSingleton ((v'l, TcString n), t'x)) r'b] :=>
                    (SumConstructor (Right n) x' `Ann` d'b, es'x)

        (TSum d'b r'b, SumExpand x) -> do
            [d'a, r'a] <- freshN [KType, KDataRow]
            cs'x :=> (x', es'x) <- check env (TSum d'a r'a) x
            pure $ CSum d'a r'a : cs'x <> [CSubRow r'a r'b] :=>
                (SumExpand x' `Ann` d'b, es'x)

        (t, x) -> do
            let t' = case t of TProd d _ -> d; TSum d _ -> d; _ -> t
            cs'x :=> (x'@(AnnOf t'x), es'x) <- infer env x
            pure $ cs'x <> [CEqual t' t'x] :=>
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

    PProductConstructor (Left m) -> do
        [d'a, r'a] <- freshN [KType, KDataRow]
        (cs'm :=> (mr'm, m', e'm)) <-
            foldByM mempty (zip [0..] m)
            \(i, p) (cs'm :=> (mr'm, m', e'm)) -> do
                cs'p :=> (p'@(PAnnOf t'p), e'p) <- inferPatt env p
                v'n <- fresh KString
                pure $ cs'p <> cs'm :=>
                    (((TcInt i, v'n), t'p) : mr'm, p' : m', e'p <> e'm)
        pure $ CProd d'a r'a : CSubRow (TDataRow mr'm) r'a : cs'm :=>
            (PProductConstructor (Left m') `PAnn` d'a, e'm)
    PProductConstructor (Right m) -> do
        [d'a, r'a] <- freshN [KType, KDataRow]
        (cs'm :=> (mr'm, m', e'm)) <-
            foldByM mempty m
            \(n, p) (cs'm :=> (mr'm, m', e'm)) -> do
                cs'p :=> (p'@(PAnnOf t'p), e'p) <- inferPatt env p
                v'l <- fresh KInt
                pure (cs'p <> cs'm :=> (((v'l, TcString n), t'p) : mr'm, (n, p') : m', e'p <> e'm))
        pure $ CProd d'a r'a : CSubRow (TDataRow mr'm) r'a : cs'm :=>
            (PProductConstructor (Right m') `PAnn` d'a, e'm)

    PSumConstructor (Left l) p -> do
        [d'a, r'a] <- freshN [KType, KDataRow]
        cs'p :=> (p'@(PAnnOf t'p), e'p) <- inferPatt env p
        v'n <- fresh KString
        pure $ CSum d'a r'a : CSubRow (dataSingleton ((TcInt l, v'n), t'p)) r'a : cs'p :=>
            (PSumConstructor (Left l) p' `PAnn` d'a, e'p)
    PSumConstructor (Right n) p -> do
        [d'a, r'a] <- freshN [KType, KDataRow]
        cs'p :=> (p'@(PAnnOf t'p), e'p) <- inferPatt env p
        v'l <- fresh KInt
        pure $ CSum d'a r'a : CSubRow (dataSingleton ((v'l, TcString n), t'p)) r'a : cs'p :=>
            (PSumConstructor (Right n) p' `PAnn` d'a, e'p)

    PWildcard -> do
        t'w <- fresh KType
        pure $ [] :=>
            (PWildcard `PAnn` t'w, mempty)

    PAnn p t -> do
        cs'p :=> (p'@(PAnnOf t'p), e'p) <- inferPatt env p
        pure $ CEqual t t'p : cs'p :=>
            (p', e'p)

checkPatt :: Env -> Type -> UntypedPatt -> Ti (Qualified (TypedPatt, Env))
checkPatt env = curry \case
    (TInt, PInt i) -> pure $ [] :=>
        (PInt i `PAnn` TInt, env)
    (TUnit, PUnit) -> pure $ [] :=>
        (PUnit `PAnn` TUnit, env)

    (t, PWildcard) -> pure $ [] :=>
        (PWildcard `PAnn` t, env)

    (TProd d'a r'a, PProductConstructor (Left m)) -> do
        cs'm :=> (mr'm, m', e'm) <-
            foldByM mempty (zip [0..] m)
            \(i, p) (cs'm :=> (mr'm, m', e'm)) -> do
                cs'p :=> (p'@(PAnnOf t'p), e'p) <- inferPatt env p
                v'n <- fresh KString
                pure $ cs'p <> cs'm :=>
                    (((TcInt i, v'n), t'p) : mr'm, p' : m', e'p <> e'm)
        pure $ CSubRow (TDataRow mr'm) r'a : cs'm :=>
            (PProductConstructor (Left m') `PAnn` d'a, e'm)

    (TProd d'a r'a, PProductConstructor (Right m)) -> do
        cs'm :=> (mr'm, m', e'm) <-
            foldByM mempty m
            \(n, p) (cs'm :=> (mr'm, m', e'm)) -> do
                cs'p :=> (p'@(PAnnOf t'p), e'p) <- inferPatt env p
                v'l <- fresh KInt
                pure $ cs'p <> cs'm :=>
                    (((v'l, TcString n), t'p) : mr'm, (n, p') : m', e'p <> e'm)
        pure $ CSubRow (TDataRow mr'm) r'a : cs'm :=>
            (PProductConstructor (Right m') `PAnn` d'a, e'm)

    (TSum d'a r'a, PSumConstructor (Left l) p) -> do
        cs'p :=> (p'@(PAnnOf t'p), e'p) <- inferPatt env p
        v'n <- fresh KString
        pure $ CSubRow (dataSingleton ((TcInt l, v'n), t'p)) r'a : cs'p :=>
            (PSumConstructor (Left l) p' `PAnn` d'a, e'p)
    (TSum d'a r'a, PSumConstructor (Right n) p) -> do
        cs'p :=> (p'@(PAnnOf t'p), e'p) <- inferPatt env p
        v'l <- fresh KInt
        pure $ CSubRow (dataSingleton ((v'l, TcString n), t'p)) r'a : cs'p :=>
            (PSumConstructor (Right n) p' `PAnn` d'a, e'p)

    (t, p) -> do
        let t' = case t of TProd d _ -> d; TSum d _ -> d; _ -> t
        cs'p :=> (p'@(PAnnOf t'p), e'p) <- inferPatt env p
        pure $ CEqual t' t'p : cs'p :=> 
            (p', e'p)





ti :: Env -> UntypedTerm ->
    Either String (Scheme (Type, TypedTerm), Subst)
ti env x = second snd <$> runTi action 0 (0, mempty) where
    action = do
        cs :=> (x'@(AnnOf t'x), es'x) <- infer env x
        cs' <- solve env (CEqual TEffectRowNil es'x : cs)
        generalize env (cs' :=> (t'x, x'))

tiPoly :: Env -> Scheme UntypedTerm ->
    Either String (Scheme (Type, TypedTerm), Subst)
tiPoly env qx = second snd <$> runTi action 0 (0, mempty) where
    action = do
        cs'x :=> x <- instantiate qx
        cs :=> (x'@(AnnOf t'x), es'x) <- infer env x
        cs' <- solve env (CEqual TEffectRowNil es'x : cs <> cs'x)
        generalize env (cs' :=> (t'x, x'))



-- FIXME: ????
-- tc :: Env -> Type -> UntypedTerm -> Either String (Scheme TypedTerm)
-- tc env t x = fst <$> flip runTi (0, mempty) do
--     cs :=> x' <- check env t x
--     cs' <- solve cs
--     generalize env (cs' :=> x')

