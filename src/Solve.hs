module Solve where

import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Maybe(fromMaybe)
import Data.Functor((<&>))
import Data.Foldable
import Data.Bifunctor
import Control.Monad
import Control.Monad.State.Class

import Util
import Pretty
import Ast
import Ti



solve :: Env -> [Constraint] -> Ti [Constraint]
solve env cs = solveSplit env (constraintSplit3 cs)

solveSplit :: Env -> ([EqualityConstraint], [RowConstraint], [DataConstraint]) -> Ti [Constraint]
solveSplit env (eqs, rows, datas) = do
    adlRows <- solveEqs eqs
    (eqs'1, rows') <- solveRows (rows <> adlRows)
    (eqs'2, datas') <- solveDatas env datas
    let eqs' = eqs'1 <> eqs'2
    if null eqs'
        then do
            (eqs'', rows'') <- applyM rows' >>= apMergeSubRows
            if null eqs''
                then pure (fmap CRow rows'' <> fmap CData datas')
                else solveSplit env (eqs'', rows'', datas')
        else solveSplit env (eqs', rows', datas')

solveEqs :: [EqualityConstraint] -> Ti [RowConstraint]
solveEqs eqs = concat <$> traverse (\(Equal a b) -> do
    appliedM2 apUnify a b) eqs

solveRows :: [RowConstraint] -> Ti ([EqualityConstraint], [RowConstraint])
solveRows [] = pure mempty
solveRows (x:cs') = do
    (eqs, unsolvedRows) <- constraintSplitEqRows <$> appliedM apConstrainRows x
    bimap (eqs <>) (unsolvedRows <>) <$> solveRows cs'

solveDatas :: Env -> [DataConstraint] -> Ti ([EqualityConstraint], [DataConstraint])
solveDatas _ [] = pure mempty
solveDatas env (x:cs') = do
    appliedM (apConstrainData env) x >>= \case
        CEquality c -> first (c :) <$> solveDatas env cs'
        CData c -> second (c :) <$> solveDatas env cs'
        CRow c -> error $ "unexpected row constraint " <> show c

constraintSplitEqRows :: [Constraint] -> ([EqualityConstraint], [RowConstraint])
constraintSplitEqRows = partitionWith \case
    CEquality c -> Left c
    CRow c -> Right c
    CData c -> error $ "unexpected data constraint " <> show c


constraintSplitEqDatas :: [Constraint] -> ([EqualityConstraint], [DataConstraint])
constraintSplitEqDatas = partitionWith \case
    CEquality c -> Left c
    CData c -> Right c
    CRow c -> error $ "unexpected row constraint " <> show c

constraintSplit3 :: [Constraint] -> ([EqualityConstraint], [RowConstraint], [DataConstraint])
constraintSplit3 = partitionWith3 \case
    CEquality c -> A c
    CRow c -> B c
    CData c -> C c 





apConstrainRows :: RowConstraint -> Ti [Constraint]
apConstrainRows = \case
    SubRow a b -> apSubRows a b
    ConcatRow a b c -> apConcatRows a b c

apSubRows :: Type -> Type -> Ti [Constraint]
apSubRows = curry \case
    (TDataRow m'a, TDataRow m'b) -> foldByM [] m'a (findField m'b) where
        findField m (l@(x, n), t) r =
            case exactField m l of
                Just t' -> pure $ CEqual t t' : r
                _ -> case scanField m l of
                    [] -> fail $ "field " <> pretty n <> " not found: " <> pretty m'a <> " ◁ " <> pretty m'b
                    [((x', n'), t')] -> pure $ CEqual x x' : CEqual n n' : CEqual t t' : r
                    ts -> fail $ "field " <> pretty x <> "/" <> pretty n
                        <> " in lhs of " <> pretty m'a <> " ◁ " <> pretty m'b
                        <> " cannot be unified, as it matches multiple fields in the rhs: " <> pretty ts

    (TEffectRow m'a, TEffectRow m'b) -> foldByM [] m'a (findEff m'b) where
        findEff m t r =
            if exactEff m t
                then pure r
                else case scanEff m t of
                    [] -> fail $ "effect" <> pretty t <> "not found: " <> pretty m'a <> " ◁ " <> pretty m'b
                    [t'] -> pure $ CEqual t t' : r
                    ts -> pure $ CSubRow (effectSingleton t) (TEffectRow ts) : r

    (TVar tv'a, TVar tv'b)
        | let k = kindOf tv'a
        , k == kindOf tv'b
        , k == KDataRow || k == KEffectRow ->
            pure [CSubRow (TVar tv'a) (TVar tv'b)]

    (TVar tv'a, TDataRow []) -> pure [CEqual (TVar tv'a) (TDataRow [])]
    (TDataRow [], TVar tv'b) | kindOf tv'b == KDataRow -> pure []
    
    (TVar tv'a, TEffectRow []) -> pure [CEqual (TVar tv'a) (TEffectRow [])]
    (TEffectRow [], TVar tv'b) | kindOf tv'b == KEffectRow -> pure []

    (TVar tv'a, TDataRow m'b)  | kindOf tv'a == KDataRow -> pure [CSubRow (TVar tv'a) (TDataRow m'b) ]
    (TDataRow m'a,  TVar tv'b) | kindOf tv'b == KDataRow -> pure [CSubRow (TDataRow m'a)  (TVar tv'b)]

    (TVar tv'a, TEffectRow m'b)  | kindOf tv'a == KEffectRow -> pure [CSubRow (TVar tv'a) (TEffectRow m'b) ]
    (TEffectRow m'a,  TVar tv'b) | kindOf tv'b == KEffectRow -> pure [CSubRow (TEffectRow m'a)  (TVar tv'b)]

    (a, b) -> fail $ "expected row types (of the same kind) for row sub, got " <> pretty a <> " ◁ " <> pretty b

            

apMergeSubRows :: [RowConstraint] -> Ti ([EqualityConstraint], [RowConstraint])
apMergeSubRows cs = do
    let (subs, concats) = subSplit cs
        (dataSubs, effectSubs) = kindSplit subs
        (effectSubMap, eqs2, ignore2) = mergeEffect effectSubs
        effectSubs' = Map.toList effectSubMap <&> \(b, as) -> SubRow (TEffectRow as) (TVar b)
    (dataSubMap, eqs, ignore) <- mergeData dataSubs
    let dataSubs' = Map.toList dataSubMap <&> \(b, as) -> SubRow (TDataRow as) (TVar b)
    pure (eqs <> eqs2, dataSubs' <> effectSubs' <> ignore <> ignore2 <> concats) where
    subSplit = partitionWith \case
        SubRow a b -> Left (a, b)
        c -> Right c
    kindSplit = partitionWith \case
        (a, b) | kindOf a == KDataRow || kindOf b == KDataRow -> Left (a, b)
        c -> Right c

    mergeData subs =
        foldByM mempty subs \constr (subMap, eqs, ignore) ->
        case constr of
            (TDataRow aList, TVar b) -> do
                let bList = fromMaybe mempty (Map.lookup b subMap)
                (bList', newEqs) <- joinDataMap b (bList, mempty) aList
                pure (Map.insert b bList' subMap, newEqs <> eqs, ignore)
            (a, b) -> pure (subMap, eqs, SubRow a b : ignore)
    joinDataMap b =
        foldrM \f@(l@(x, n), t) (bList, eqs) ->
            case exactField bList l of
                Just t' -> pure (bList, Equal t t' : eqs)
                _ -> case scanField bList l of
                    [] -> pure (f : bList, eqs)
                    [((x', n'), t')] -> pure (bList, Equal x x' : Equal n n' : Equal t t' : eqs)
                    ts -> fail $ "field " <> pretty x <> "/" <> pretty n
                        <> " creates ambiguous subtype constraint after constraint reduction: "
                        <> pretty bList <> " ◁ " <> pretty b
                        <> ", ambiguous fields include: " <> pretty ts

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
            if exactEff bList t
                then (bList, eqs, subs)
                else case scanEff bList t of
                    [] -> (t : bList, eqs, subs)
                    [t'] -> (bList, Equal t t' : eqs, subs)
                    ts -> (bList, eqs, SubRow (effectSingleton t) (TEffectRow ts) : subs)


apConcatRows :: Type -> Type -> Type -> Ti [Constraint]
apConcatRows ta tb tc = case (ta, tb, tc) of
    (TDataRow m'a, TDataRow m'b, t'c) -> do
        (cs, m'c) <-
            foldByM mempty (m'a <> m'b)
            \(l@(x, n), t) (cs, m) -> case exactField m l of
                Just t' -> pure (CEqual t t' : cs, m)
                _ -> case scanField m l of
                    [] -> pure (cs, (l, t) : m)
                    ts -> fail $ "field " <> pretty x <> "/" <> pretty n
                        <> " in " <> pretty m'a <> " ⊙ " <> pretty m'b
                        <> " cannot be merged, as it matches field(s) in the opposing side: " <> pretty ts
                        <> " (fields must be disjoint in a row concatenation)"
        pure (CEqual (TDataRow m'c) t'c : cs)
      

    (TVar tv'a, TDataRow m'b, TDataRow m'c) -> mergeDataVar tv'a m'b m'c
    (TDataRow m'a, TVar tv'b, TDataRow m'c) -> mergeDataVar tv'b m'a m'c

    (TDataRow [], TVar tv'b, TVar tv'c) ->
        pure [CEqual (TVar tv'b) (TVar tv'c)]
    
    (TVar tv'a, TDataRow [], TVar tv'c) ->
        pure [CEqual (TVar tv'a) (TVar tv'c)]

    (TVar tv'a, TVar tv'b, TDataRow []) ->
        pure [CEqual (TVar tv'a) (TDataRow []), CEqual (TVar tv'b) (TDataRow [])]

    (TEffectRow m'a, TEffectRow m'b, t'c) -> do
        let (cs, m'c) =
                foldBy mempty (m'a <> m'b)
                \e (xs, ts) -> if exactEff ts e
                    then (xs, ts)
                    else case scanEff ts e of
                        [] -> (xs, e : ts)
                        [e'] -> (CEqual e e' : xs, ts)
                        es' -> (CSubRow (effectSingleton e) (TEffectRow es') : xs, ts)
        pure (CEqual (TEffectRow m'c) t'c : cs)

    
    (TVar tv'a, TEffectRow l'b, TEffectRow l'c) -> mergeEffectVar tv'a l'b l'c
    (TEffectRow l'a, TVar tv'b, TEffectRow l'c) -> mergeEffectVar tv'b l'a l'c

    (TEffectRow [], TVar tv'b, TVar tv'c) ->
        pure [CEqual (TVar tv'b) (TVar tv'c)]
    
    (TVar tv'a, TEffectRow [], TVar tv'c) ->
        pure [CEqual (TVar tv'a) (TVar tv'c)]

    (TVar tv'a, TVar tv'b, TEffectRow []) ->
        pure [CEqual (TVar tv'a) (TEffectRow []), CEqual (TVar tv'b) (TEffectRow [])]

    (TVar tv'a, TVar tv'b, TVar tv'c)
        | let k = kindOf tv'a
        , k == kindOf tv'b
        , k == kindOf tv'c
        , k == KEffectRow || k == KDataRow ->
            pure [CConcatRow (TVar tv'a) (TVar tv'b) (TVar tv'c)]

    (TVar tv'a, TVar tv'b, TDataRow m'c )
        | kindOf tv'a == KDataRow
        , kindOf tv'b == KDataRow ->
            pure [CConcatRow (TVar tv'a) (TVar tv'b) (TDataRow m'c) ]

    (TVar tv'a, TDataRow m'b,  TVar tv'c)
        | kindOf tv'a == KDataRow
        , kindOf tv'c == KDataRow ->
            pure [CConcatRow (TVar tv'a) (TDataRow m'b)  (TVar tv'c)]

    (TDataRow m'a,  TVar tv'b, TVar tv'c)
        | kindOf tv'b == KDataRow
        , kindOf tv'c == KDataRow ->
            pure [CConcatRow (TDataRow m'a)  (TVar tv'b) (TVar tv'c)]

    (TVar tv'a, TVar tv'b, TEffectRow m'c )
        | kindOf tv'a == KEffectRow
        , kindOf tv'b == KEffectRow ->
            pure [CConcatRow (TVar tv'a) (TVar tv'b) (TEffectRow m'c) ]

    (TVar tv'a, TEffectRow m'b,  TVar tv'c)
        | kindOf tv'a == KEffectRow
        , kindOf tv'c == KEffectRow ->
            pure [CConcatRow (TVar tv'a) (TEffectRow m'b)  (TVar tv'c)]

    (TEffectRow m'a,  TVar tv'b, TVar tv'c)
        | kindOf tv'b == KEffectRow
        , kindOf tv'c == KEffectRow ->
            pure [CConcatRow (TEffectRow m'a)  (TVar tv'b) (TVar tv'c)]

    _ -> fail $ "expected row types (of the same kind) for row concat, got "
        <> pretty ta <> " ⊙ " <> pretty tb <> " ~ " <> pretty tc
    where
    mergeDataVar tv'a m'b m'c = do
        cs :=> m'a <- foldByM mempty m'c \(l@(x, n), t) (cs :=> m'a) ->
            case exactField m'b l of
                Just t' -> pure $ CEqual t t' : cs :=> m'a
                _ -> case scanField m'b l of
                    [] -> pure $ cs :=> (l, t) : m'a
                    [((x', n'), t')] -> pure $ CEqual x x' : CEqual n n' : CEqual t t' : cs :=> m'a
                    ts -> fail $ "field " <> pretty x <> "/" <> pretty n
                        <> " in lhs of ~ in " <> pretty tv'a <> " ⊙ " <> pretty m'b <> " ~ " <> pretty m'c
                        <> " cannot be merged, as it matches multiple fields in the rhs of ~: " <> pretty ts

        forM_ m'b \(l@(x, n), _) ->
            case exactField m'c l of
                Just _ -> pure ()
                _ -> case scanField m'c l of
                    [_] -> pure ()
                    [] -> fail $ "field " <> pretty n <> " not found: " <> pretty m'b <> " ◁ " <> pretty m'c
                    ts -> fail $ "field " <> pretty x <> "/" <> pretty n
                        <> " in lhs of inferred " <> pretty m'b <> " ◁ " <> pretty m'c
                        <> " matches multiple fields in the rhs: " <> pretty ts

        pure $ CEqual (TDataRow m'a) (TVar tv'a) : cs

    mergeEffectVar tv'a m'b m'c = do
        let (cs, m'a) =
                foldBy mempty (m'c List.\\ m'b)
                \e (xs, a) -> case scanEff m'b e of
                    [] -> (xs, e : a)
                    [e'] -> (CEqual e e' : xs, a)
                    es' -> (CSubRow (effectSingleton e) (TEffectRow es') : xs, a)
        cs' <-
            foldByM mempty (m'b List.\\ m'c)
            \e xs -> case scanEff m'c e of
                [] -> fail $ "effect " <> pretty e <> " not found: " <> pretty m'b <> " ◁ " <> pretty m'c
                [e'] -> pure (CEqual e e' : xs)
                es' -> pure (CSubRow (effectSingleton e) (TEffectRow es') : xs)
        pure (CEqual (TEffectRow m'a) (TVar tv'a) : cs <> cs')


apConstrainData :: Env -> DataConstraint -> Ti Constraint
apConstrainData env = \case
    IsProd d r -> apConstrainProd env d r
    IsSum d r -> apConstrainSum env d r

apConstrainProd :: Env -> Type -> Type -> Ti Constraint
apConstrainProd env d r =
    case splitTypeCon d of
        Just (dataName, dataArgs) ->
            dataLookup env dataName >>= instantiateWith dataArgs >>= \case
                DProd m -> pure (CEqual (TDataRow m) r)
                DSum _ -> fail $ "expected product data type, got " <> pretty d <> " (a sum data type)"
        _-> pure (CProd d r)

apConstrainSum :: Env -> Type -> Type -> Ti Constraint
apConstrainSum env d r =
    case splitTypeCon d of
        Just (dataName, dataArgs) ->
            dataLookup env dataName >>= instantiateWith dataArgs >>= \case
                DSum m -> pure (CEqual (TDataRow m) r)
                DProd _ -> fail $ "expected sum data type, got " <> pretty d <> " (a product data type)"
        _-> pure (CSum d r)



exactField :: [Field] -> Label -> Maybe Type
exactField m l = List.lookup l m

scanField :: [Field] -> Label -> [Field]
scanField m (x, n) = foldBy [] m \f@((x', n'), _) r ->
    if unifiable x x'
    && unifiable n n'
    then f : r
    else r

exactEff :: [Type] -> Type -> Bool
exactEff m t = t `elem` m

scanEff :: [Type] -> Type -> [Type]
scanEff m t = List.filter (unifiable t) m

unifiable :: Type -> Type -> Bool
unifiable = curry \case
    (TVar tv'a, TVar tv'b) -> kindOf tv'a == kindOf tv'b
    (TVar tv'a, b) -> kindOf tv'a == kindOf b
    (a, TVar tv'b) -> kindOf tv'b == kindOf a
    (TCon c'a, TCon c'b) -> c'a == c'b
    (TApp a'a b'a, TApp a'b b'b) -> unifiable a'a a'b && unifiable b'a b'b &&
        case kindOf a'a of
            KArrow k'x _ -> k'x == kindOf b'a
            _ -> False
    (TDataRow a, TDataRow b) ->
        mergeField (a List.\\ b) b && mergeField (b List.\\ a) a where
        mergeField m'a m'b = flip List.all m'a \(l, t) -> case scanField m'b l of
            [(_, t')] -> unifiable t t'
            _ -> False
    (TEffectRow a, TEffectRow b) ->
        mergeEff (a List.\\ b) b && mergeEff (b List.\\ a) a where
        mergeEff m'a m'b = flip List.all m'a \e'a -> case scanEff m'b e'a of
            [_] -> True
            _ -> False
    (TConstant a, TConstant b) -> a == b
    _ -> False



apUnify :: Type -> Type -> Ti [RowConstraint]
apUnify = curry \case
    (TVar tv'a, b) -> [] <$ apUnifyVar tv'a b
    (a, TVar tv'b) -> [] <$ apUnifyVar tv'b a

    (TCon c'a, TCon c'b) | c'a == c'b -> pure []

    (TApp x'a y'a, TApp x'b y'b) -> do
        case kindOf x'a of
            KArrow k'x _ -> unless (kindOf y'a == k'x) do
                fail $ "kind mismatch: " <> pretty y'a <> " : " <> pretty (kindOf y'a) <> " ~ " <> pretty x'a <> " : " <> pretty k'x
            _ -> fail $ "expected arrow kind, got " <> pretty x'a <> " : " <> pretty (kindOf x'a)
        liftM2 (<>) (apUnify x'a x'b) (appliedM2 apUnify y'a y'b)

    (TDataRow a, TDataRow b) ->
        liftM2 (<>) (mergeField (a List.\\ b) b) (mergeField (b List.\\ a) a) where
        mergeField m'a m'b = foldByM mempty m'a \(l@(x, n), t) cs -> case scanField m'b l of
            [] -> fail $ "label " <> pretty x <> "/" <> pretty n <> " not found: " <> pretty a <> " ~ " <> pretty b
            [((x', n'), t')] -> do
                xs <- appliedM2 apUnify x x'
                ns <- appliedM2 apUnify n n'
                ts <- appliedM2 apUnify t t'
                pure (xs <> ns <> ts <> cs)
            fs -> fail $ "label " <> pretty x <> "/" <> pretty n
                <> " in the lhs of " <> pretty a <> " ~ " <> pretty b
                <> " cannot be unified, as it matches multiple fields in the rhs: " <> pretty fs

    (TEffectRow a, TEffectRow b) ->
        liftM2 (<>) (mergeEff (a List.\\ b) b) (mergeEff (b List.\\ a) a) where
        mergeEff m'a m'b = foldByM mempty m'a \e'a cs -> case scanEff m'b e'a of
            [] -> fail $ "effect " <> pretty e'a <> " not found: " <> pretty a <> " ∪ " <> pretty b
            [e'b] -> appliedM2 apUnify e'a e'b <&> (<> cs)
            bs -> pure (SubRow (effectSingleton e'a) (TEffectRow bs) : cs)

    (TConstant a, TConstant b) | a == b -> pure []

    (a, b) -> fail $ "cannot unify " <> pretty a <> " ∪ " <> pretty b
        
apUnifyVar :: TypeVar -> Type -> Ti ()
apUnifyVar tv (TVar tv') | tv == tv' = pure ()
apUnifyVar tv t = do
    s <- gets snd
    case Map.lookup tv s of
        Just t' -> error $ "apUnifyVar: " <> pretty tv <> " already has a value " <> pretty t'
        Nothing -> pure ()
    tvs <- ftvsM t
    when (kindOf tv /= kindOf t) do
        fail $ "kind mismatch: " <> pretty tv <> " : " <> pretty (kindOf tv) <> " ∪ " <> pretty t <> " : " <> pretty (kindOf t)
    when (tv `elem` tvs) do
        fail $ "occurs check failed: " <> pretty tv <> " occurs in " <> pretty t
    modify (second (Map.insert tv t))