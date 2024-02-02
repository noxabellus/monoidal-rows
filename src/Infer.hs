module Infer where

import Data.Functor ((<&>))
import Data.Bifunctor

import Data.Map.Strict qualified as Map
import Data.List qualified as List

import Data.Maybe (fromMaybe)

import Control.Monad.Except
import Control.Monad.State.Class

import Util
import Pretty
import Ast
import Subst
import Ti





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



solve :: [Constraint] -> Ti [Constraint]
solve cs = fmap CRow <$> uncurry solveSplit (constraintSplit cs)

solveSplit :: [EqualityConstraint] -> [RowConstraint] -> Ti [RowConstraint]
solveSplit eqs rows = do
    adlRows <- solveEqs eqs
    (eqs', rows') <- solveRows (rows <> adlRows)
    if null eqs'
        then do
            (eqs'', rows'') <- apMergeSubRows <$> applyM rows'
            if null eqs''
                then pure rows''
                else solveSplit eqs'' rows''
        else solveSplit eqs' rows'

solveEqs :: [EqualityConstraint] -> Ti [RowConstraint]
solveEqs eqs = concat <$> traverse (uncurry $ appliedM2 apUnify) eqs

solveRows :: [RowConstraint] -> Ti ([EqualityConstraint], [RowConstraint])
solveRows [] = pure mempty
solveRows (x:cs') = do
    (eqs, unsolved) <- constraintSplit <$> appliedM apConstrainRows x
    bimap (eqs <>) (unsolved <>) <$> solveRows cs'
    
constraintSplit :: [Constraint] -> ([EqualityConstraint], [RowConstraint])
constraintSplit = partitionWith \case
    CEqual c -> Left c
    CRow c -> Right c




apUnify :: Type -> Type -> Ti [RowConstraint]
apUnify = curry \case
    (TVar tv'a, b) -> [] <$ apUnifyVar tv'a b
    (a, TVar tv'b) -> [] <$ apUnifyVar tv'b a

    (TCon c'a, TCon c'b) | c'a == c'b -> pure []

    -- NOTE: Kind check??
    (TApp x'a y'a, TApp x'b y'b) -> liftM2 (<>) (apUnify x'a x'b) (apUnify y'a y'b)

    (TProd a, TProd b) -> apUnify a b

    (TSum a, TSum b) -> apUnify a b

    (TDataRow m'a, TDataRow m'b) -> do
        let ks'a = Map.keys m'a
            ks'b = Map.keys m'b
        when (ks'a /= ks'b) do
            fail $ "row labels mismatch: " <> pretty m'a <> " ∪ " <> pretty m'b
        concat <$> forM (zip (Map.elems m'a) (Map.elems m'b)) (uncurry apUnify)

    (TEffectRow a, TEffectRow b) ->
        liftM2 (<>) (mergeEff (a List.\\ b) b) (mergeEff (b List.\\ a) a)
        where
        mergeEff l'a l'b = foldByM mempty l'a \e'a cs -> case scanEff l'b e'a of
            [] -> fail $ "effect " <> pretty e'a <> " not found: " <> pretty a <> " ∪ " <> pretty b
            [e'b] -> apUnify e'a e'b <&> (<> cs)
            bs -> pure (SubRow (effectSingleton e'a) (TEffectRow bs) : cs)

    (a, b) -> fail $ "cannot unify " <> pretty a <> " ∪ " <> pretty b
        
apUnifyVar :: TypeVar -> Type -> Ti ()
apUnifyVar tv (TVar tv') | tv == tv' = pure ()
apUnifyVar tv t = do
    tvs <- ftvsM t
    when (kindOf tv /= kindOf t) do
        fail $ "kind mismatch: " <> pretty tv <> " : " <> pretty (kindOf tv) <> " ∪ " <> pretty t <> " : " <> pretty (kindOf t)
    when (tv `elem` tvs) do
        fail $ "occurs check failed: " <> pretty tv <> " occurs in " <> pretty t
    modify (second (Map.insert tv t))





apConstrainRows :: RowConstraint -> Ti [Constraint]
apConstrainRows = \case
    SubRow a b -> apSubRows a b
    ConcatRow a b c -> apConcatRows a b c

apSubRows :: Type -> Type -> Ti [Constraint]
apSubRows = curry \case
    (TDataRow m'a, TDataRow m'b) ->
        forM (Map.toList m'a) \(k, t'a) ->
            case Map.lookup k m'b of
                Just t'b -> pure $ CEqual (t'a, t'b)
                _ -> fail $ "row label " <> pretty k <> " not found: " <> pretty m'a <> " ◁ " <> pretty m'b

    (TEffectRow m'a, TEffectRow m'b) -> forM m'a (findEff m'b) where
        findEff m t =
            case exactEff m t of
                Just t' -> pure $ CEqual (t, t')
                _ -> case scanEff m t of
                    [] -> fail $ "effect" <> pretty t <> "not found: " <> pretty m'a <> " ◁ " <> pretty m'b
                    [t'] -> pure $ CEqual (t, t')
                    ts -> pure $ CRow $ SubRow (effectSingleton t) (TEffectRow ts)

    (TVar tv'a, TVar tv'b)
        | let k = kindOf tv'a
        , k == kindOf tv'b
        , k == KDataRow || k == KEffectRow ->
            pure [CRow $ SubRow (TVar tv'a) (TVar tv'b)]

    (TVar tv'a, TDataRow m'b)  | kindOf tv'a == KDataRow -> pure [CRow $ SubRow (TVar tv'a) (TDataRow m'b) ]
    (TDataRow m'a,  TVar tv'b) | kindOf tv'b == KDataRow -> pure [CRow $ SubRow (TDataRow m'a)  (TVar tv'b)]

    (TVar tv'a, TEffectRow m'b)  | kindOf tv'a == KEffectRow -> pure [CRow $ SubRow (TVar tv'a) (TEffectRow m'b) ]
    (TEffectRow m'a,  TVar tv'b) | kindOf tv'b == KEffectRow -> pure [CRow $ SubRow (TEffectRow m'a)  (TVar tv'b)]

    (a, b) -> fail $ "expected row types (of the same kind) for row sub, got " <> pretty a <> " ◁ " <> pretty b


exactEff :: [Type] -> Type -> Maybe Type
exactEff m t = List.find (== t) m

scanEff :: [Type] -> Type -> [Type]
scanEff m t = List.filter (unifiable t) m

unifiable :: Type -> Type -> Bool
unifiable = curry \case
    (TVar tv'a, TVar tv'b) -> kindOf tv'a == kindOf tv'b
    (TVar tv'a, b) -> kindOf tv'a == kindOf b
    (a, TVar tv'b) -> kindOf tv'b == kindOf a
    (TCon c'a, TCon c'b) -> c'a == c'b
    (TApp a'a b'a, TApp a'b b'b) -> unifiable a'a a'b && unifiable b'a b'b
    (TDataRow a, TDataRow b) -> Map.keys a == Map.keys b && all (uncurry unifiable) (Map.elems a `zip` Map.elems b)
    _ -> False

            

apMergeSubRows :: [RowConstraint] -> ([EqualityConstraint], [RowConstraint])
apMergeSubRows cs =
    let (subs, concats) = subSplit cs
        (dataSubs, effectSubs) = kindSplit subs
        (dataSubMap, eqs, ignore) = mergeData dataSubs
        (effectSubMap, eqs2, ignore2) = mergeEffect effectSubs
        dataSubs' = Map.toList dataSubMap <&> \(b, as) -> SubRow (TDataRow as) (TVar b)
        effectSubs' = Map.toList effectSubMap <&> \(b, as) -> SubRow (TEffectRow as) (TVar b)
    in (eqs <> eqs2, dataSubs' <> effectSubs' <> ignore <> ignore2 <> concats) where
    subSplit = partitionWith \case
        SubRow a b -> Left (a, b)
        c -> Right c
    kindSplit = partitionWith \case
        (a, b) | kindOf a == KDataRow || kindOf b == KDataRow -> Left (a, b)
        c -> Right c

    mergeData subs =
        foldBy mempty subs \constr (subMap, eqs, ignore) ->
            case constr of
                (TDataRow aMap, TVar b) ->
                    let bMap = fromMaybe mempty (Map.lookup b subMap)
                        (bMap', newEqs) = joinDataMap (bMap, mempty) (Map.toList aMap)
                    in (Map.insert b bMap' subMap, newEqs <> eqs, ignore)
                (a, b) -> (subMap, eqs, SubRow a b : ignore)
    joinDataMap =
        foldr \(k, t) (bMap, eqs) ->
            case Map.lookup k bMap of
                Just t' -> (bMap, (t, t') : eqs)
                _ -> (Map.insert k t bMap, eqs)

    mergeEffect subs =
        foldBy mempty subs \constr (subMap, eqs, ignore) ->
            case constr of
                (TEffectRow aList, TVar b) ->
                    let bList = fromMaybe mempty (Map.lookup b subMap)
                        (bList', newEqs, newSubs) = joinEffectMap (bList, mempty, mempty) aList
                    in (Map.insert b bList' subMap, newEqs <> eqs, ignore <> newSubs)
                (a, b) -> (subMap, eqs, SubRow a b : ignore)
    joinEffectMap =
        foldr \t (bList, eqs, subs) ->
            case exactEff bList t of
                Just _ -> (bList, eqs, subs)
                _ -> case scanEff bList t of
                    [] -> (t : bList, eqs, subs)
                    [t'] -> (bList, (t, t') : eqs, subs)
                    ts -> (bList, eqs, SubRow (effectSingleton t) (TEffectRow ts) : subs)


apConcatRows :: Type -> Type -> Type -> Ti [Constraint]
apConcatRows ta tb tc = case (ta, tb, tc) of
    (TDataRow m'a, TDataRow m'b, t'c) -> do
        m'c <- foldByM mempty (Map.keys m'a `List.union` Map.keys m'b) \k m ->
            case (Map.lookup k m'a, Map.lookup k m'b) of
                (Just t'a, Nothing) -> pure (Map.insert k t'a m)
                (Nothing, Just t'b) -> pure (Map.insert k t'b m)
                _ -> fail $ "label " <> pretty k <> " is not disjoint in sub-rows of concat " <> pretty m'a <> " ⊙ " <> pretty m'b
        pure [CEqual (TDataRow m'c, t'c)]
      

    (TVar tv'a, TDataRow m'b, TDataRow m'c) -> pure (mergeDataVar tv'a m'b m'c)
    (TDataRow m'a, TVar tv'b, TDataRow m'c) -> pure (mergeDataVar tv'b m'a m'c)

    (TEffectRow a, TEffectRow b, t'c) -> do
        let (cs, c) =
                foldBy (mempty  :: ([Constraint], [Type])) (a <> b)
                \e (xs, ts) -> case exactEff ts e of
                    Just _ -> (xs, ts)
                    _ -> case scanEff ts e of
                        [] -> (xs, e : ts)
                        [e'] -> (CEqual (e, e') : xs, ts)
                        es' -> (CRow (SubRow (effectSingleton e) (TEffectRow es')) : xs, ts)
        pure (CEqual (TEffectRow c, t'c) : cs)

    
    (TVar tv'a, TEffectRow l'b, TEffectRow l'c) -> mergeEffectVar tv'a l'b l'c
    (TEffectRow l'a, TVar tv'b, TEffectRow l'c) -> mergeEffectVar tv'b l'a l'c

    (TVar tv'a, TVar tv'b, TVar tv'c)
        | let k = kindOf tv'a
        , k == kindOf tv'b
        , k == kindOf tv'c
        , k == KEffectRow || k == KDataRow ->
            pure [CRow $ ConcatRow (TVar tv'a) (TVar tv'b) (TVar tv'c)]

    (TVar tv'a, TVar tv'b, TDataRow m'c )
        | kindOf tv'a == KDataRow
        , kindOf tv'b == KDataRow ->
            pure [CRow $ ConcatRow (TVar tv'a) (TVar tv'b) (TDataRow m'c) ]

    (TVar tv'a, TDataRow m'b,  TVar tv'c)
        | kindOf tv'a == KDataRow
        , kindOf tv'c == KDataRow ->
            pure [CRow $ ConcatRow (TVar tv'a) (TDataRow m'b)  (TVar tv'c)]

    (TDataRow m'a,  TVar tv'b, TVar tv'c)
        | kindOf tv'b == KDataRow
        , kindOf tv'c == KDataRow ->
            pure [CRow $ ConcatRow (TDataRow m'a)  (TVar tv'b) (TVar tv'c)]

    (TVar tv'a, TVar tv'b, TEffectRow m'c )
        | kindOf tv'a == KEffectRow
        , kindOf tv'b == KEffectRow ->
            pure [CRow $ ConcatRow (TVar tv'a) (TVar tv'b) (TEffectRow m'c) ]

    (TVar tv'a, TEffectRow m'b,  TVar tv'c)
        | kindOf tv'a == KEffectRow
        , kindOf tv'c == KEffectRow ->
            pure [CRow $ ConcatRow (TVar tv'a) (TEffectRow m'b)  (TVar tv'c)]

    (TEffectRow m'a,  TVar tv'b, TVar tv'c)
        | kindOf tv'b == KEffectRow
        , kindOf tv'c == KEffectRow ->
            pure [CRow $ ConcatRow (TEffectRow m'a)  (TVar tv'b) (TVar tv'c)]

    _ -> fail $ "expected row types (of the same kind) for row concat, got "
        <> pretty ta <> " ⊙ " <> pretty tb <> " ~ " <> pretty tc
    where
    mergeDataVar tv'a m'b m'c =
        let (m'a, cs) = foldBy mempty (Map.toList m'c) \(k, t'c) (ma, es) ->
                case Map.lookup k m'b of
                    Just t'b -> (ma, CEqual (t'b, t'c) : es)
                    _ -> (Map.insert k t'c ma, es)
        in (CEqual (TVar tv'a, TDataRow m'a) : cs)

    mergeEffectVar tv'a l'b l'c = do
        let (cs, l'a) =
                foldBy mempty (l'c List.\\ l'b)
                \e (xs, a) -> case scanEff l'b e of
                    [] -> (xs, e : a)
                    [e'] -> (CEqual (e, e') : xs, a)
                    es' -> (CRow (SubRow (effectSingleton e) (TEffectRow es')) : xs, a)
        cs' <-
            foldByM mempty (l'b List.\\ l'c)
            \e xs -> case scanEff l'c e of
                [] -> fail $ "effect " <> pretty e <> " not found: " <> pretty l'b <> " ◂ " <> pretty l'c
                [e'] -> pure (CEqual (e, e') : xs)
                es' -> pure (CRow (SubRow (effectSingleton e) (TEffectRow es')) : xs)
        pure (CEqual (TEffectRow l'a, TVar tv'a) : cs <> cs')



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

