module Ti where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map

import Data.Bifunctor

import Control.Monad.Except
import Control.Monad.State.Class

import Ast
import Subst

type Evidence = Type
type Env = Map Var (Scheme Type)
type SubstSt = (Int, Subst)

newtype Ti a
    = Ti { runTi :: Int -> SubstSt -> Either String (a, SubstSt) }
    deriving Functor

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




envLookup :: Env -> Var -> Ti (Scheme Type)
envLookup env i = case Map.lookup i env of
    Just sc -> pure sc
    Nothing -> fail $ "unbound variable " <> show i

envExt :: Env -> Var -> Type -> Env
envExt env i t = Map.insert i ([] `Forall` [] :=> t) env

envSingleton :: Var -> Type -> Env
envSingleton = envExt mempty


getId :: Ti Int
getId = Ti (curry pure)