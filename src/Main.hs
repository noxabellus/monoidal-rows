{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
import Data.Map.Strict (Map)
import Data.Set (Set)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.List qualified as List
import Data.Bifunctor
import Data.Functor
import Control.Monad.Except (MonadError(..))
import Control.Monad.State.Class (MonadState(..), gets, modify)
import Control.Monad
import Data.Foldable
import Data.Maybe
-- import Debug.Trace (traceM)

todo = error "nyi"

partitionWith :: (a -> Either b c) -> [a] -> ([b], [c])
partitionWith f = flip foldr mempty \a (bs, cs) ->
    case f a of
        Left b -> (b:bs, cs)
        Right c -> (bs, c:cs)


foldBy :: (Foldable t) => b -> t a -> (a -> b -> b) -> b
foldBy b a f = foldr f b a

foldByM :: (Foldable t, Monad m) => b -> t a -> (a -> b -> m b) -> m b
foldByM b a f = foldrM f b a



class Nil m where
    nil :: m
    isNil :: m -> Bool

instance Nil [a] where
    nil = []
    isNil = null

instance Nil (Map k v) where
    nil = Map.empty
    isNil = Map.null

instance Nil (Set a) where
    nil = Set.empty
    isNil = Set.null

pattern Nil :: Nil m => m
pattern Nil <- (isNil -> True)
    where Nil = nil






data Term
    = Var Var
    | Unit
    | Int Int
    | Lambda Patt Term
    | App Term Term
    | Ann Term Type
    | Match Term [(Patt, Term)]

    | ProductConstructor [(Name, Term)]
    | ProductConcat Term Term
    | ProductNarrow Term
    | ProductSelect Term Name

    | SumConstructor Name Term
    | SumExpand Term
    deriving Show
infixl 8 `Ann`
pattern UnAnn x <- Ann x _
pattern AnnOf t <- Ann _ t
type Name = String
type Var = String
type UntypedTerm = Term
type TypedTerm = Term




data Patt
    = PVar Var
    | PUnit
    | PInt Int
    | PAnn Patt Type

    | PProductConstructor (Map Name Patt)
    | PSumConstructor Name Patt

    | PWildcard
    deriving Show
pattern PAnnOf t <- PAnn _ t
infixl 8 `PAnn`
type UntypedPatt = Patt
type TypedPatt = Patt




data Kind
    = KConstant Name
    | KArrow Kind Kind
    deriving (Show, Eq, Ord)
infixr :~>
pattern KType = KConstant "Type"
pattern KEffect = KConstant "Effect"
pattern KDataRow = KConstant "DataRow"
pattern KEffectRow = KConstant "EffectRow"
pattern (:~>) a b = KArrow a b




data Type
    = TVar TypeVar
    | TCon TypeCon
    | TApp Type Type
    | TDataRow (Map Name Type)
    | TEffectRow [Type]
    deriving (Show, Eq, Ord)
type TypeCon = (String, Kind)
data BoundType = BoundType Int Kind deriving (Show, Eq, Ord)
data MetaType = MetaType Int Kind deriving (Show, Eq, Ord)
data TypeVar
    = TvBound BoundType
    | TvMeta MetaType
    deriving (Show, Eq, Ord)
pattern TFunCon = TCon ("->_in", KType :~> KType :~> KEffectRow :~> KType)
pattern TProdCon = TCon ("Π", KDataRow :~> KType)
pattern TSumCon = TCon ("Σ", KDataRow :~> KType)
pattern TInt = TCon ("Int", KType)
pattern TProd a = TApp TProdCon a
pattern TSum a = TApp TSumCon a
pattern TFun a b e = TApp (TApp (TApp TFunCon a) b) e
pattern TDataRowNil = TDataRow Nil
pattern TEffectRowNil = TEffectRow Nil
pattern TConcrete a <- a@(\case TVar _ -> False; _ -> True -> True)

dataSingleton :: Name -> Type -> Type
dataSingleton n t = TDataRow (Map.singleton n t)

effectSingleton :: Type -> Type
effectSingleton t = TEffectRow [t]




data Constraint
    = CEqual EqualityConstraint
    | CRow RowConstraint
    deriving (Show, Eq, Ord)

type EqualityConstraint = (Type, Type)

data RowConstraint
    = SubRow Type Type
    | ConcatRow Type Type Type
    deriving (Show, Eq, Ord)




data Scheme a = Forall [BoundType] (Qualified a)
    deriving (Functor, Show)
infix 0 `Forall`



data Qualified a = Qualified [Constraint] a
    deriving (Functor, Show)
infix 1 :=>
{-# COMPLETE (:=>) #-}
pattern (:=>) cs t = Qualified cs t

instance Semigroup a => Semigroup (Qualified a) where
    Qualified cs a <> Qualified cs' a' = Qualified (cs <> cs') (a <> a')

instance Monoid a => Monoid (Qualified a) where
    mempty = Qualified mempty mempty


type Evidence = Type


type Env = Map Var (Scheme Type)
type Subst = Map TypeVar Type
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




class TVars a where
    ftvs :: (TypeVar -> Bool) -> a -> [TypeVar]
    apply :: Subst -> a -> a

instance TVars a => TVars [a] where
    ftvs f = foldr (List.union . ftvs f) []
    apply s = fmap (apply s)

instance TVars a => TVars (Map k a) where
    ftvs f = foldr (List.union . ftvs f) []
    apply s = fmap (apply s)

instance TVars a => TVars (Scheme a) where
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
        TVar v | f v -> [v]
            | otherwise -> []
        TCon _ -> []
        TApp a b -> ftvs f a `List.union` ftvs f b
        TProd a -> ftvs f a
        TSum a -> ftvs f a
        TDataRow a -> ftvs f a
        TEffectRow a -> ftvs f a

    apply s = \case
        TVar tv 
            | Just t <- Map.lookup tv s -> apply s t
            | otherwise -> TVar tv
        TCon c -> TCon c
        TApp a b -> TApp (apply s a) (apply s b)
        TProd a -> TProd (apply s a)
        TSum a -> TSum (apply s a)
        TDataRow a -> TDataRow (apply s a)
        TEffectRow a -> TEffectRow (List.nub (apply s a))

instance TVars Constraint where
    ftvs f = \case
        CEqual c -> ftvs f c
        CRow c -> ftvs f c

    apply s = \case
        CEqual c -> CEqual (apply s c)
        CRow c -> CRow (apply s c)

instance TVars RowConstraint where
    ftvs f = \case
        SubRow a b -> ftvs f a `List.union` ftvs f b
        ConcatRow a b c -> ftvs f a `List.union` ftvs f b `List.union` ftvs f c

    apply s = \case
        SubRow a b -> SubRow (apply s a) (apply s b)
        ConcatRow a b c -> ConcatRow (apply s a) (apply s b) (apply s c)




class HasKind a where
    kindOf :: a -> Kind

instance HasKind (a, Type) where
    kindOf = \case
        (_, t) -> kindOf t

instance HasKind (a, Kind) where
    kindOf (_, k) = k

instance HasKind BoundType where
    kindOf (BoundType _ k) = k

instance HasKind MetaType where
    kindOf (MetaType _ k) = k

instance HasKind TypeVar where
    kindOf = \case
        TvBound (BoundType _ k) -> k
        TvMeta (MetaType _ k) -> k

instance HasKind Type where
    kindOf = \case
        TVar tv -> kindOf tv
        TCon c -> kindOf c
        TApp a _ -> case kindOf a of
            KArrow _ b -> b
            _ -> error "ice: kindOf(TApp a _) where kindOf a /= KArrow"
        TDataRow _ -> KDataRow
        TEffectRow _ -> KEffectRow





class Pretty a where
    prettyPrec :: Int -> a -> String
    pretty :: a -> String
    prettyPrec _ = pretty
    pretty = prettyPrec 0

class PrettyVar a where
    prettyVar :: Int -> a -> String
    prettyVarStrip :: a -> String

instance PrettyVar String where
    prettyVar _ = id
    prettyVarStrip = id

instance (PrettyVar a, Pretty b) => PrettyVar (a, b) where
    prettyVar p (n, t) = parensIf (p > 0) $ prettyVar 0 n <> ": " <> pretty t
    prettyVarStrip (n, _) = prettyVarStrip n

instance {-# OVERLAPPABLE #-} Show a => Pretty a where
    pretty = show

instance (Pretty a, Pretty b) => Pretty (a, b) where
    pretty (a, b) = "(" <> pretty a <> ", " <> pretty b <> ")"

instance Pretty a => Pretty [a] where
    pretty = brackets . List.intercalate ", " . fmap pretty

instance {-# OVERLAPPABLE #-} (Pretty a, Pretty b) => Pretty (Map a b) where
    pretty = braces . List.intercalate ", " . fmap (\(a, b) -> pretty a <> " = " <> pretty b) . Map.toList

instance Pretty b => Pretty (Either String b) where
    prettyPrec p = either id (prettyPrec p)

instance Pretty Term where
    prettyPrec p = \case
        Var v -> prettyVarStrip v
        Unit -> "()"
        Int i -> prettyPrec p i
        Lambda q x -> parensIf (p > 0) $ "λ" <> prettyPrec 0 q <> ". " <> prettyPrec 0 x
        App a b -> parensIf (p > 1) $ prettyPrec 1 a <> " " <> prettyPrec 2 b
        Ann x t -> parensIf (p > 0) $ prettyPrec 0 x <> " : " <> prettyPrec 0 t
        Match x cs -> parensIf (p > 0) $ "match " <> prettyPrec 0 x <> " with " <> List.intercalate " | " (prettyPrec 0 <$> cs)
        ProductConstructor fs -> braces $ List.intercalate ", " $ fs <&> \(n, x) -> n <> " = " <> pretty x
        ProductConcat a b -> parensIf (p > 2) $ prettyPrec 2 a <> " ⊙ " <> prettyPrec 3 b
        ProductNarrow x -> parensIf (p > 3) $ "narrow " <> prettyPrec 3 x
        ProductSelect x n -> parensIf (p > 6) $ prettyPrec 6 x <> " \\ " <> n
        SumConstructor n x -> angles $ n <> " = " <> pretty x
        SumExpand x -> parensIf (p > 5) $ "expand " <> prettyPrec 5 x

instance Pretty Patt where
    prettyPrec p = \case
        PVar v -> prettyVarStrip v
        PUnit -> "()"
        PInt i -> prettyPrec p i
        PAnn x t -> parensIf (p > 0) $ prettyPrec 0 x <> " : " <> prettyPrec 0 t
        PProductConstructor m -> parensIf (p > 0) $ prettyPrec 0 m
        PSumConstructor n x -> parensIf (p > 0) $ n <> " " <> prettyPrec 1 x
        PWildcard -> "_"

instance Pretty Kind where
    prettyPrec p = \case
        KConstant n -> n
        KArrow a b -> parensIf (p > 0) $ prettyPrec 1 a <> " ↠ " <> prettyPrec 0 b

instance Pretty Type where
    prettyPrec p = \case
        TVar tv -> prettyVarStrip tv
        TCon (n, _) -> n
        TFun a b e -> parensIf (p > 0) $ prettyPrec 1 a <> " → " <> prettyPrec 0 b <> " in " <> prettyPrec 0 e
        TApp a b -> parensIf (p > 1) $ prettyPrec 1 a <> " " <> prettyPrec 2 b
        TDataRow m -> braces $ Map.foldrWithKey (\k t s -> k <> " ∷ " <> pretty t <> ", " <> s) "" m
        TEffectRow m -> brackets $ List.intercalate ", " (pretty <$> m)

instance PrettyVar BoundType where
    prettyVar p (BoundType i k) = parensIf (p > 0) $ "#" <> show i <> " : " <> pretty k
    prettyVarStrip (BoundType i _) = "#" <> show i

instance PrettyVar MetaType where
    prettyVar p (MetaType i k) = parensIf (p > 0) $ "$" <> show i <> " : " <> pretty k
    prettyVarStrip (MetaType i _) = "$" <> show i

instance Pretty TypeVar where
    prettyPrec = prettyVar

instance PrettyVar TypeVar where
    prettyVar p = \case
        TvBound tv -> prettyVar p tv
        TvMeta tv -> prettyVar p tv

    prettyVarStrip = \case
        TvBound tv -> prettyVarStrip tv
        TvMeta tv -> prettyVarStrip tv

instance Pretty Constraint where
    prettyPrec p = \case
        CEqual (a, b) -> parensIf (p > 0) $ pretty a <> " ~ " <> pretty b
        CRow (SubRow a b) -> parensIf (p > 0) $ pretty a <> " ◁ " <> pretty b
        CRow (ConcatRow a b c) -> parensIf (p > 0) $ pretty a <> " ⊙ " <> pretty b <> " ~ " <> pretty c

instance Pretty a => Pretty (Scheme a) where
    prettyPrec p (Forall [] qt) = prettyPrec p qt
    prettyPrec p (Forall bvs qt) = parensIf (p > 0) $ "∀" <> List.intercalate ", " (prettyVar 0 <$> bvs) <> ". " <> prettyPrec 0 qt

instance Pretty a => Pretty (Qualified a) where
    prettyPrec p (Qualified [] t) = prettyPrec p t
    prettyPrec p (Qualified cs t) = parensIf (p > 0) $ prettyPrec 0 cs <> " ⇒ " <> prettyPrec 0 t

parensIf :: Bool -> String -> String
parensIf True = parens
parensIf False = id

parens :: String -> String
parens s = "(" <> s <> ")"

brackets :: String -> String
brackets s = "[" <> s <> "]"

braces :: String -> String
braces s = "{" <> s <> "}"

angles :: String -> String
angles s = "<" <> s <> ">"





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




envLookup :: Env -> Var -> Ti (Qualified Type)
envLookup env i = case Map.lookup i env of
    Just sc -> instantiate sc
    Nothing -> fail $ "unbound variable " <> show i

envExt :: Env -> Var -> Type -> Env
envExt env i t = Map.insert i ([] `Forall` [] :=> t) env

envSingleton :: Var -> Type -> Env
envSingleton = envExt mempty




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


getId :: Ti Int
getId = Ti (curry pure)


infer :: Env -> UntypedTerm -> Ti (Qualified (TypedTerm, Evidence))
infer env ut = do
    -- iid <- getId
    -- traceM $ replicate iid ' ' <> "inferring " <> pretty ut
    -- res <-
    case ut of
        Var v -> do
            cs :=> t <- envLookup env v
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

    (TEffectRow a, TEffectRow b) -> do
        liftM2 (<>) (mergeEff (a List.\\ b) b) (mergeEff (b List.\\ a) a)
        where
            mergeEff l'a l'b = foldByM mempty l'a \e'a cs -> case scanEff l'b e'a of
                [] -> fail $ "effect not found: " <> brackets (pretty e'a) <> " ∪ " <> pretty l'b
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

    (TEffectRow m'a, TEffectRow m'b) ->
        forM m'a (findEff m'b)

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
    where
        findEff m t =
            case exactEff m t of
                Just t' -> pure $ CEqual (t, t')
                _ -> case scanEff m t of
                    [] -> fail $ "effect not found: " <> brackets (pretty t) <> " ◁ " <> pretty m
                    [t'] -> pure $ CEqual (t, t')
                    ts -> pure $ CRow $ SubRow (effectSingleton t) (TEffectRow ts)


exactEff m t = List.find (== t) m
scanEff m t = List.filter (unifiable t) m
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
    mergeEffect subs =
        foldBy mempty subs \constr (subMap, eqs, ignore) ->
            case constr of
                (TEffectRow aList, TVar b) ->
                    let bList = fromMaybe mempty (Map.lookup b subMap)
                        (bList', newEqs) = joinEffectMap (bList, mempty) aList
                    in (Map.insert b bList' subMap, newEqs <> eqs, ignore)
                (a, b) -> (subMap, eqs, SubRow a b : ignore)
    joinDataMap =
        foldr \(k, t) (bMap, eqs) ->
            case Map.lookup k bMap of
                Just t' -> (bMap, (t, t') : eqs)
                _ -> (Map.insert k t bMap, eqs)
    joinEffectMap =
        foldr \t (bList, eqs) ->
            if t `elem` bList
                then (bList, eqs)
                else (t : bList, eqs)


apConcatRows :: Type -> Type -> Type -> Ti [Constraint]
apConcatRows a b c = case (a, b, c) of
    (TDataRow m'a, TDataRow m'b, t'c) ->
        let (m'c, eqs) =
                foldBy mempty (Map.keys m'a `List.union` Map.keys m'b) \k (m, cs) ->
                    case (Map.lookup k m'a, Map.lookup k m'b) of
                        (Just t'a, Just t'b) -> (Map.insert k t'a m, CEqual (t'a, t'b) : cs)
                        (Just t'a, _) -> (Map.insert k t'a m, cs)
                        (_, Just t'b) -> (Map.insert k t'b m, cs)
                        _ -> (m, cs)
        in pure (CEqual (TDataRow m'c, t'c) : eqs)
      
    (TVar tv'a, TDataRow m'b, TDataRow m'c) -> pure (mergeDataVar tv'a m'b m'c)
    (TDataRow m'a, TVar tv'b, TDataRow m'c) -> pure (mergeDataVar tv'b m'a m'c)

    (TEffectRow l'a, TEffectRow l'b, t'c) ->
        let l'c = l'a `List.union` l'b
        in pure [CEqual (TEffectRow l'c, t'c)]
    
    (TVar tv'a, TEffectRow l'b, TEffectRow l'c) -> pure (mergeEffectVar tv'a l'b l'c)
    (TEffectRow l'a, TVar tv'b, TEffectRow l'c) -> pure (mergeEffectVar tv'b l'a l'c)

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

    _ -> fail $ "expected row types (of the same kind) for row concat, got " <> pretty a <> " ⊙ " <> pretty b <> " ~ " <> pretty c
    where
    mergeDataVar tv'a m'b m'c =
        let (m'a, cs) = foldBy mempty (Map.toList m'c) \(k, t'c) (ma, es) ->
                case Map.lookup k m'b of
                    Just t'b -> (ma, CEqual (t'b, t'c) : es)
                    _ -> (Map.insert k t'c ma, es)
        in (CEqual (TVar tv'a, TDataRow m'a) : cs)

    mergeEffectVar tv'a l'b l'c =
        let l'a = (l'c List.\\ l'b) <> (l'b List.\\ l'c)
        in [CEqual (TVar tv'a, TEffectRow l'a)]

pattern TUnit = TCon ("()", KType)
pattern TReadCon = TCon ("Read", KType :~> KEffect)
pattern TRead a = TApp TReadCon a

pattern TWriteCon = TCon ("Write", KType :~> KEffect)
pattern TWrite a = TApp TWriteCon a

env0 :: Env
env0 = Map.fromList
    [ ( "read"
      , Forall [BoundType 0 KType] $
            [] :=> TFun
                TUnit
                (TVar (TvBound (BoundType 0 KType)))
                (TEffectRow
                    [TRead (TVar (TvBound (BoundType 0 KType)))])
      )
    , ( "write"
      , Forall [BoundType 0 KType] $
            [] :=> TFun
                (TVar (TvBound (BoundType 0 KType)))
                TUnit
                (TEffectRow
                    [TWrite (TVar (TvBound (BoundType 0 KType)))])
      )
    , ( "i_add"
      , Forall [BoundType 0 KType] $
            [] :=> TFun
                TInt
                (TFun TInt TInt (TEffectRow []))
                (TEffectRow [])
      )
    , ( "combobulate"
      , Forall [] $
            [] :=> TFun
                TUnit
                (TFun TInt TInt (TEffectRow []))
                (TEffectRow [])
      )
    ]



ti :: Env -> UntypedTerm -> Either String (Scheme (Type, TypedTerm), Subst)
ti env x = second snd <$> runTi action 0 (0, mempty) where
    action = do
        (cs :=> (x'@(AnnOf t'x), es'x)) <- infer env x
        unless (case es'x of TEffectRowNil -> True; _ -> False) do
            fail $ "unhandleable effects in top-level initializer: " <> pretty es'x
        cs' <- solve cs
        generalize env (cs' :=> (t'x, x'))

-- FIXME: ????
-- tc :: Env -> Type -> UntypedTerm -> Either String (Scheme TypedTerm)
-- tc env t x = fst <$> flip runTi (0, mempty) do
--     cs :=> x' <- check env t x
--     cs' <- solve cs
--     generalize env (cs' :=> x')








main :: IO ()
main = do putStrLn "Hi bitch"