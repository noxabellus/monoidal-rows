module Subst where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.List qualified as List

import Ast


type Subst = Map TypeVar Type

class TVars a where
    ftvs :: (TypeVar -> Bool) -> a -> [TypeVar]
    apply :: Subst -> a -> a

instance TVars a => TVars [a] where
    ftvs f = foldr (List.union . ftvs f) []
    apply s = fmap (apply s)

instance TVars a => TVars (Map k a) where
    ftvs f = foldr (List.union . ftvs f) []
    apply s = fmap (apply s)

instance (TVars a, TVars b) => TVars (Either a b) where
    ftvs f = \case
        Left a -> ftvs f a
        Right b -> ftvs f b
    apply s = \case
        Left a -> Left (apply s a)
        Right b -> Right (apply s b)

instance TVars a => TVars (Maybe a) where
    ftvs f = \case
        Just a -> ftvs f a
        Nothing -> []
    apply s = \case
        Just a -> Just (apply s a)
        Nothing -> Nothing

instance TVars a => TVars (Quantified a) where
    ftvs f (Forall _ t) = ftvs f t
    apply s (Forall bvs t) = Forall bvs (apply s t)

instance TVars a => TVars (Qualified a) where
    ftvs f (Qualified cs t) = ftvs f cs `List.union` ftvs f t
    apply s (Qualified cs t) = Qualified (apply s cs) (apply s t)

instance {-# OVERLAPPABLE #-} (TVars a, TVars b) => TVars (a, b) where
    ftvs f (a, b) = ftvs f a `List.union` ftvs f b
    apply s (a, b) = (apply s a, apply s b)

instance (TVars a) => TVars (String, a) where
    ftvs f (_, a) = ftvs f a
    apply s (n, a) = (n, apply s a)

instance TVars Term where
    ftvs f = \case
        Var _ -> []
        Unit -> []
        Int _ -> []
        Lambda p x -> ftvs f p `List.union` ftvs f x
        App a b -> ftvs f a `List.union` ftvs f b
        Ann x t -> ftvs f x `List.union` ftvs f t
        Match x cs -> ftvs f x `List.union` ftvs f cs
        ProductConstructor fs -> ftvs f fs
        ProductConcat a b -> ftvs f a `List.union` ftvs f b
        ProductNarrow x -> ftvs f x
        ProductSelect x _ -> ftvs f x
        SumConstructor _ x -> ftvs f x
        SumExpand x -> ftvs f x
        Handler t hm r x -> ftvs f t `List.union` ftvs f hm `List.union` ftvs f r `List.union` ftvs f x

    apply s = \case
        Var v -> Var v
        Unit -> Unit
        Int i -> Int i
        Lambda p x -> Lambda (apply s p) (apply s x)
        App f x -> App (apply s f) (apply s x)
        Ann x t -> Ann (apply s x) (apply s t)
        Match x cs -> Match (apply s x) (apply s cs)
        ProductConstructor fs -> ProductConstructor (apply s fs)
        ProductConcat a b -> ProductConcat (apply s a) (apply s b)
        ProductNarrow x -> ProductNarrow (apply s x)
        ProductSelect x n -> ProductSelect (apply s x) n
        SumConstructor n x -> SumConstructor n (apply s x)
        SumExpand x -> SumExpand (apply s x)
        Handler t hm r x -> Handler (apply s t) (apply s hm) (apply s r) (apply s x)

instance TVars Patt where
    ftvs f = \case
        PVar _ -> []
        PUnit -> []
        PInt _ -> []
        PProductConstructor m -> ftvs f m
        PSumConstructor _ p -> ftvs f p
        PWildcard -> []
        PAnn p t -> ftvs f p `List.union` ftvs f t

    apply s = \case
        PVar v -> PVar v
        PUnit -> PUnit
        PInt i -> PInt i
        PProductConstructor m -> PProductConstructor (apply s m)
        PSumConstructor n p -> PSumConstructor n (apply s p)
        PWildcard -> PWildcard
        PAnn p t -> PAnn (apply s p) (apply s t)

instance TVars Type where
    ftvs f = \case
        TVar v
            | f v -> [v]
            | otherwise -> []
        TCon _ -> []
        TApp a b -> ftvs f a `List.union` ftvs f b
        TDataRow a -> ftvs f a
        TEffectRow a -> ftvs f a
        TConstant _ -> []

    apply s = \case
        TVar tv 
            | Just t <- Map.lookup tv s -> apply s t
            | otherwise -> TVar tv
        TCon c -> TCon c
        TApp a b -> TApp (apply s a) (apply s b)
        TDataRow a -> TDataRow (apply s a)
        TEffectRow a -> TEffectRow (List.nub (apply s a))
        TConstant c -> TConstant c

instance TVars Constraint where
    ftvs f = \case
        CEquality c -> ftvs f c
        CRow c -> ftvs f c
        CData c -> ftvs f c

    apply s = \case
        CEquality c -> CEquality (apply s c)
        CRow c -> CRow (apply s c)
        CData c -> CData (apply s c)

instance TVars EqualityConstraint where
    ftvs f = \case
        Equal a b -> ftvs f a `List.union` ftvs f b

    apply s = \case
        Equal a b -> Equal (apply s a) (apply s b)

instance TVars RowConstraint where
    ftvs f = \case
        SubRow a b -> ftvs f a `List.union` ftvs f b
        ConcatRow a b c -> ftvs f a `List.union` ftvs f b `List.union` ftvs f c

    apply s = \case
        SubRow a b -> SubRow (apply s a) (apply s b)
        ConcatRow a b c -> ConcatRow (apply s a) (apply s b) (apply s c)

instance TVars DataConstraint where
    ftvs f = \case
        IsProd a b -> ftvs f a `List.union` ftvs f b
        IsSum a b -> ftvs f a `List.union` ftvs f b

    apply s = \case
        IsProd a b -> IsProd (apply s a) (apply s b)
        IsSum a b -> IsSum (apply s a) (apply s b)