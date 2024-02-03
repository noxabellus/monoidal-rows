module Solve where

import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Maybe(fromMaybe)
import Data.Functor((<&>))
import Data.Bifunctor
import Control.Monad
import Control.Monad.State.Class

import Util
import Pretty
import Ast
import Ti



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