module Ti where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map

import Data.List qualified as List

import Data.Bifunctor
import Data.Functor

import Control.Monad.Except
import Control.Monad.State.Class

import Pretty
import Ast
import Subst

type Evidence = Type
type SubstSt = (Int, Subst)
type TypeEnv = Map Var (Scheme Type)
type EffectEnv = Map Var (Scheme (Map Name (Type, Type)))

data Env =
    Env
    { typeEnv :: TypeEnv
    , effectEnv :: EffectEnv
    }
    deriving Show

newtype Ti a
    = Ti { runTi :: Int -> SubstSt -> Either String (a, SubstSt) }
    deriving Functor


instance Semigroup Env where
    Env te1 ee1 <> Env te2 ee2 = Env (te1 <> te2) (ee1 <> ee2)

instance Monoid Env where
    mempty = Env mempty mempty

instance TVars Env where
    ftvs f (Env te ee) = ftvs f te `List.union` ftvs f ee
    apply s (Env te ee) = Env (apply s te) (apply s ee)


instance Applicative Ti where
    pure a = Ti \_ s -> Right (a, s)
    Ti f <*> Ti a = Ti \i s -> do
        (f', s') <- f (i + 1) s
        (a', s'') <- a (i + 1) s'
        return (f' a', s'')

instance Monad Ti where
    Ti a >>= f = Ti \i s -> do
        (a', s') <- a (i + 1) s
        runTi (f a') i s'

instance MonadFail Ti where
    fail msg = Ti \_ _ -> Left msg

instance MonadError String Ti where
    throwError = fail
    catchError (Ti a) f = Ti \i s -> case a i s of
        Left e -> runTi (f e) i s
        Right x -> Right x

instance MonadState SubstSt Ti where
    get = Ti \_ s -> Right (s, s)
    put s = Ti \_ _ -> Right ((), s)






ftvsM :: TVars a => a -> Ti [TypeVar]
ftvsM a = do
    s <- gets snd
    pure (ftvs (\case tv@TvMeta{} -> not (Map.member tv s); _ -> False) a)

applyM :: TVars a => a -> Ti a
applyM a = do
    s' <- gets snd
    pure (apply s' a)

appliedM :: TVars a => (a -> Ti b) -> a -> Ti b
appliedM f a = do
    a' <- applyM a
    f a'

appliedM2 :: (TVars a, TVars b) => (a -> b -> Ti c) -> a -> b -> Ti c
appliedM2 f a b = do
    a' <- applyM a
    b' <- applyM b
    f a' b'

appliedM3 :: (TVars a, TVars b, TVars c) => (a -> b -> c -> Ti d) -> a -> b -> c -> Ti d
appliedM3 f a b c = do
    a' <- applyM a
    b' <- applyM b
    c' <- applyM c
    f a' b' c'




freshVar :: Kind -> Ti TypeVar
freshVar k = do
    i <- gets fst
    TvMeta (MetaType i k) <$ modify (first (+1))

fresh :: Kind -> Ti Type
fresh k = TVar <$> freshVar k

freshN :: [Kind] -> Ti [Type]
freshN = traverse fresh

freshDataSub :: Ti RowConstraint
freshDataSub = do
    [r'a, r'b] <- freshN [KDataRow, KDataRow]
    pure (SubRow r'a r'b)

freshDataConcat :: Ti RowConstraint
freshDataConcat = do
    [r'a, r'b, r'c] <- freshN [KDataRow, KDataRow, KDataRow]
    pure (ConcatRow r'a r'b r'c)

freshEffectConcat :: Ti RowConstraint
freshEffectConcat = do
    [r'a, r'b, r'c] <- freshN [KEffectRow, KEffectRow, KEffectRow]
    pure (ConcatRow r'a r'b r'c)


effLookup :: Env -> Var -> Ti (Scheme (Map Name (Type, Type)))
effLookup env i = case Map.lookup i (effectEnv env) of
    Just sc -> pure sc
    Nothing -> fail $ "unbound effect " <> show i

envLookup :: Env -> Var -> Ti (Scheme Type)
envLookup env i = case Map.lookup i (typeEnv env) of
    Just sc -> pure sc
    Nothing -> fail $ "unbound variable " <> show i

envExt :: Env -> Var -> Type -> Env
envExt (Env te ee) i t = Env (Map.insert i ([] `Forall` [] :=> t) te) ee

envSingleton :: Var -> Type -> Env
envSingleton = envExt mempty


getId :: Ti Int
getId = Ti (curry pure)






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