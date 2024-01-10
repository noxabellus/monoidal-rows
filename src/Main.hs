{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
import Data.Map.Strict (Map)
import Data.Set (Set)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.List qualified as List
import Data.String qualified as String
import Data.Bifunctor
import Data.Functor
import Control.Monad.Except (MonadError(..))
import Control.Monad.State.Class (MonadState(..), gets, modify)
import Control.Applicative
import Control.Monad
import Data.Foldable
import Data.Maybe

todo = error "nyi"
unreachable = error "unreachable code reached"

partitionWith :: (a -> Either b c) -> [a] -> ([b], [c])
partitionWith f = flip foldr mempty \a (bs, cs) ->
    case f a of
        Left b -> (b:bs, cs)
        Right c -> (bs, c:cs)

compose :: (a -> b) -> (b -> c) -> (a -> c)
compose = flip (.)


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
pattern KRow = KConstant "Row"
pattern (:~>) a b = KArrow a b




data Type
    = TVar TypeVar
    | TCon TypeCon
    | TApp Type Type
    | TRow (Map Name Type)
    deriving (Show, Eq, Ord)
type TypeCon = (String, Kind)
data BoundType = BoundType Int Kind deriving (Show, Eq, Ord)
data MetaType = MetaType Int Kind deriving (Show, Eq, Ord)
data TypeVar
    = TvBound BoundType
    | TvMeta MetaType
    deriving (Show, Eq, Ord)
pattern TFunCon = TCon ("->", KType :~> KType :~> KType)
pattern TProdCon = TCon ("Π", KRow :~> KType)
pattern TSumCon = TCon ("Σ", KRow :~> KType)
pattern TInt = TCon ("Int", KType)
pattern TProd a = TApp TProdCon a
pattern TSum a = TApp TSumCon a
pattern TFun a b = TApp (TApp TFunCon a) b
infixr 9 :->
pattern (:->) a b = TFun a b

pattern TRowNil = TRow Nil
pattern TConcrete a <- a@(\case TVar _ -> False; _ -> True -> True)
rowSingleton :: Name -> Type -> Type
rowSingleton n t = TRow (Map.singleton n t)




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



type Env = Map Var (Scheme Type)
type Subst = Map TypeVar Type
type SubstSt = (Int, Subst)

newtype Ti a
    = Ti { runTi :: SubstSt -> Either String (a, SubstSt) }
    deriving Functor

instance Applicative Ti where
    pure a = Ti \s -> Right (a, s)
    Ti f <*> Ti a = Ti \s -> do
        (f', s') <- f s
        (a', s'') <- a s'
        return (f' a', s'')

instance Monad Ti where
    Ti a >>= f = Ti \s -> do
        (a', s') <- a s
        runTi (f a') s'

instance MonadFail Ti where
    fail msg = Ti \_ -> Left msg

instance MonadError String Ti where
    throwError = fail
    catchError (Ti a) f = Ti \s -> case a s of
        Left e -> runTi (f e) s
        Right x -> Right x

instance MonadState SubstSt Ti where
    get = Ti \s -> Right (s, s)
    put s = Ti \_ -> Right ((), s)




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
        PInt _ -> []
        PProductConstructor m -> ftvs f m
        PSumConstructor _ p -> ftvs f p
        PWildcard -> []
        PAnn p t -> ftvs f p `List.union` ftvs f t

    apply s = \case
        PVar v -> PVar v
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
        TRow a -> ftvs f a

    apply s = \case
        TVar tv 
            | Just t <- Map.lookup tv s -> apply s t
            | otherwise -> TVar tv
        TCon c -> TCon c
        TApp a b -> TApp (apply s a) (apply s b)
        TProd a -> TProd (apply s a)
        TSum a -> TSum (apply s a)
        TRow a -> TRow (apply s a)

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
        TRow _ -> KRow





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
    prettyPrec :: Pretty b => Int -> Either String b -> String
    prettyPrec p = either id (prettyPrec p)

instance Pretty Term where
    prettyPrec p = \case
        Var v -> prettyVarStrip v
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
        TFun a b -> parensIf (p > 0) $ prettyPrec 1 a <> " → " <> prettyPrec 0 b
        TApp a b -> parensIf (p > 1) $ prettyPrec 1 a <> " " <> prettyPrec 2 b
        TRow m -> "{" <> Map.foldrWithKey (\k t s -> k <> " ∷ " <> pretty t <> ", " <> s) "}" m

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

freshSub :: Ti RowConstraint
freshSub = do
    [r'a, r'b] <- freshN [KRow, KRow]
    pure (SubRow r'a r'b)

freshConcat :: Ti RowConstraint
freshConcat = do
    [r'a, r'b, r'c] <- freshN [KRow, KRow, KRow]
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





infer :: Env -> UntypedTerm -> Ti (Qualified TypedTerm)
infer env = \case
    Var v -> do
        cs :=> t <- envLookup env v
        pure (cs :=> Var v `Ann` t)
    
    Int i -> pure ([] :=> Int i `Ann` TInt)

    Lambda p x -> do
        (cs'p :=> p'@(PAnnOf t'p), e'p) <- inferPatt env p
        cs'x :=> x'@(AnnOf t'x) <- infer (e'p <> env) x
        pure (cs'p <> cs'x :=> Lambda p' x' `Ann` t'p :-> t'x)

    App f x -> do
        cs'x :=> x'@(AnnOf t'x) <- infer env x
        t'y <- fresh KType
        cs'f :=> f' <- check env (t'x :-> t'y) f
        pure (cs'x <> cs'f :=> App f' x' `Ann` t'y)

    Ann x t -> do
        cs :=> x' <- check env t x
        pure (cs :=> x')

    Match x cs -> do
        cs'x :=> x'@(AnnOf t'x) <- infer env x
        t'r <- fresh KType
        ccs :=> cs' <-
            foldByM mempty cs \(p, y) (ccs :=> cs') -> do
                (cs'p :=> p', e'p) <- checkPatt env t'x p
                (cs'y :=> y') <- check (e'p <> env) t'r y
                pure (cs'p <> cs'y <> ccs :=> (p', y') : cs')
        pure (cs'x <> ccs :=> Match x' cs' `Ann` t'r)

    ProductConstructor fs -> do
        cs'm :=> (r, m') <- foldByM mempty fs \(n, x) (cs'm :=> (r, m')) -> do
            (cs'x :=> x'@(AnnOf t'x)) <- infer env x
            pure (cs'x <> cs'm :=> (Map.insert n t'x r, (n, x') : m'))
        pure (cs'm :=> ProductConstructor m' `Ann` TProd (TRow r))

    ProductConcat a b -> do
        cc@(ConcatRow r'a r'b r'c) <- freshConcat
        cs'a :=> a' <- check env (TProd r'a) a
        cs'b :=> b' <- check env (TProd r'b) b
        pure (CRow cc : cs'a <> cs'b :=> ProductConcat a' b' `Ann` TProd r'c)

    ProductNarrow x -> do
        sc@(SubRow r'a r'b) <- freshSub
        cs'x :=> x' <- check env (TProd r'b) x
        pure (CRow sc : cs'x :=> ProductNarrow x' `Ann` TProd r'a)

    ProductSelect x n -> do
        t <- fresh KType
        t'r <- fresh KRow
        cs'x :=> x' <- check env (TProd t'r) x
        pure (CRow (SubRow (rowSingleton n t) t'r) : cs'x :=> ProductSelect x' n `Ann` t)

    SumConstructor n x -> do
        t'r <- fresh KRow
        cs'x :=> x'@(AnnOf t'x) <- infer env x
        pure (CRow (SubRow (rowSingleton n t'x) t'r) : cs'x :=> SumConstructor n x' `Ann` TSum t'r)

    SumExpand x -> do
        cs@(SubRow r'a r'b) <- freshSub
        cs'x :=> x' <- check env (TSum r'a) x
        pure (CRow cs : cs'x :=> SumExpand x' `Ann` TSum r'b)

check :: Env -> Type -> UntypedTerm -> Ti (Qualified TypedTerm)
check env = curry \case
    (TInt, Int i) -> pure ([] :=> Int i `Ann` TInt)

    (a :-> b, Lambda p x) -> do
        (cs'p :=> p', e'p) <- checkPatt env a p
        (cs'x :=> x') <- check (e'p <> env) b x
        pure (cs'p <> cs'x :=> Lambda p' x' `Ann` a :-> b)

    (t@(TProd (TRow r)), x@(ProductConstructor fs)) -> do
        cs'm :=> m' <- foldByM mempty fs \(n, v) (cs'm :=> m') -> do
            case Map.lookup n r of
                Just t'v -> do
                    cs'v :=> v' <- check env t'v v
                    pure (cs'v <> cs'm :=> (n, v') : m')
                _ -> fail $ "field " <> n <> " of product constructor " <> pretty x <> " not in type " <> pretty t
        pure (cs'm :=> ProductConstructor m' `Ann` t)

    (TProd r'c, ProductConcat a b) -> do
        [r'a, r'b] <- freshN [KRow, KRow]
        cs'a :=> a' <- check env (TProd r'a) a
        cs'b :=> b' <- check env (TProd r'b) b
        pure (CRow (ConcatRow r'a r'b r'c) : cs'a <> cs'b :=> ProductConcat a' b' `Ann` TProd r'c)

    (TProd r'a, ProductNarrow x) -> do
        r'b <- fresh KRow
        cs'x :=> x' <- check env (TProd r'b) x
        pure (CRow (SubRow r'a r'b) : cs'x :=> ProductNarrow x' `Ann` TProd r'a)

    (t, ProductSelect x n) -> do
        t'r <- fresh KRow
        cs'x :=> x' <- check env (TProd t'r) x
        pure (CRow (SubRow (rowSingleton n t) t'r) : cs'x :=> ProductSelect x' n `Ann` t)

    (t@(TSum r'b), SumConstructor n x)
        | TRow m <- r'b ->
            case Map.lookup n m of
                Just t'x -> do
                    cs'x :=> x' <- check env t'x x
                    pure (cs'x :=> SumConstructor n x' `Ann` TSum r'b)
                _ -> fail $ "variant " <> n <> " of sum constructor " <> pretty x <> " not in type " <> pretty t
        | otherwise -> do
            cs'x :=> x'@(AnnOf t'x) <- infer env x
            pure (CRow (SubRow (rowSingleton n t'x) r'b) : cs'x :=> SumConstructor n x' `Ann` TSum r'b)

    (TSum r'b, SumExpand x) -> do
        r'a <- fresh KRow
        cs'x :=> x' <- check env (TSum r'a) x
        pure (CRow (SubRow r'a r'b) : cs'x :=> SumExpand x' `Ann` TSum r'b)

    (t, x) -> do
        (cs'x :=> x'@(AnnOf t'x)) <- infer env x
        pure (CEqual (t, t'x) : cs'x :=> x')


inferPatt :: Env -> UntypedPatt -> Ti (Qualified TypedPatt, Env)
inferPatt env = \case
    PVar v -> do
        t'v <- fresh KType
        pure ([] :=> PVar v `PAnn` t'v, envSingleton v t'v)

    PInt i -> pure ([] :=> PInt i `PAnn` TInt, mempty)

    PProductConstructor m -> do
        r'a <- fresh KRow
        (cs'm :=> (mr'm, m', e'm)) <- foldByM mempty (Map.toList m) \(n, p) (cs'm :=> (mr'm, m', e'm)) -> do
            (cs'p :=> p'@(PAnnOf t'p), e'p) <- inferPatt env p
            pure (cs'p <> cs'm :=> (Map.insert n t'p mr'm, Map.insert n p' m', e'p <> e'm))
        pure (CRow (SubRow (TRow mr'm) r'a) : cs'm :=> PProductConstructor m' `PAnn` TProd r'a, e'm)

    PSumConstructor n p -> do
        r'a <- fresh KRow
        (cs'p :=> p'@(PAnnOf t'p), e'p) <- inferPatt env p
        pure (CRow (SubRow (rowSingleton n t'p) r'a) : cs'p :=> PSumConstructor n p' `PAnn` TSum r'a, e'p)

    PWildcard -> do
        t'w <- fresh KType
        pure ([] :=> PWildcard `PAnn` t'w, mempty)

    PAnn p t -> do
        (cs'p :=> p'@(PAnnOf t'p), e'p) <- inferPatt env p
        pure (CEqual (t, t'p) : cs'p :=> p', e'p)

checkPatt :: Env -> Type -> UntypedPatt -> Ti (Qualified TypedPatt, Env)
checkPatt env = curry \case
    (TInt, PInt i) -> pure ([] :=> PInt i `PAnn` TInt, env)

    (t, PWildcard) -> pure ([] :=> PWildcard `PAnn` t, env)

    (TProd r'a, PProductConstructor m) -> do
        cs'm :=> (mr'm, m', e'm) <- foldByM mempty (Map.toList m) \(n, p) (cs'm :=> (mr'm, m', e'm)) -> do
            (cs'p :=> p'@(PAnnOf t'p), e'p) <- inferPatt env p
            pure (cs'p <> cs'm :=> (Map.insert n t'p mr'm, Map.insert n p' m', e'p <> e'm))
        pure (CRow (SubRow (TRow mr'm) r'a) : cs'm :=> PProductConstructor m' `PAnn` TProd r'a, e'm)

    (TSum r'a, PSumConstructor n p) -> do
        (cs'p :=> p'@(PAnnOf t'p), e'p) <- inferPatt env p
        pure (CRow (SubRow (rowSingleton n t'p) r'a) : cs'p :=> PSumConstructor n p' `PAnn` TSum r'a, e'p)

    (t, p) -> do
        (cs'p :=> p'@(PAnnOf t'p), e'p) <- inferPatt env p
        pure (CEqual (t, t'p) : cs'p :=> p', e'p)



solve :: [Constraint] -> Ti [Constraint]
solve cs = fmap CRow <$> uncurry solveSplit (constraintSplit cs)

solveSplit :: [EqualityConstraint] -> [RowConstraint] -> Ti [RowConstraint]
solveSplit eqs rows = do
    solveEqs eqs
    (eqs', rows') <- solveRows rows
    if null eqs'
        then do
            (eqs'', rows'') <- apMergeSubRows <$> applyM rows'
            if null eqs''
                then pure rows''
                else solveSplit eqs'' rows''
        else solveSplit eqs' rows'

solveEqs :: [EqualityConstraint] -> Ti ()
solveEqs = traverse_ (uncurry $ appliedM2 apUnify)

solveRows :: [RowConstraint] -> Ti ([EqualityConstraint], [RowConstraint])
solveRows [] = pure mempty
solveRows (x:cs') = do
    (eqs, unsolved) <- constraintSplit <$> appliedM apConstrainRows x
    bimap (eqs <>) (unsolved <>) <$> solveRows cs'

subSplit :: [RowConstraint] -> ([(Type, Type)], [RowConstraint])
subSplit = partitionWith \case
    SubRow a b -> Left (a, b)
    c -> Right c
    
constraintSplit :: [Constraint] -> ([EqualityConstraint], [RowConstraint])
constraintSplit = partitionWith \case
    CEqual c -> Left c
    CRow c -> Right c




apUnify :: Type -> Type -> Ti ()
apUnify = curry \case
    (TVar tv'a, b) -> apUnifyVar tv'a b
    (a, TVar tv'b) -> apUnifyVar tv'b a

    (TCon c'a, TCon c'b) | c'a == c'b -> pure ()

    -- NOTE: Kind check??
    (TApp x'a y'a, TApp x'b y'b) -> apUnify x'a x'b >> apUnify y'a y'b

    (TProd a, TProd b) -> apUnify a b

    (TSum a, TSum b) -> apUnify a b

    (TRow m'a, TRow m'b) -> do
        let ks'a = Map.keys m'a
            ks'b = Map.keys m'b
        when (ks'a /= ks'b) do
            fail $ "row labels mismatch: " <> pretty m'a <> " ∪ " <> pretty m'b
        forM_ (zip (Map.elems m'a) (Map.elems m'b)) (uncurry apUnify)

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
apSubRows a b = case (a, b) of
    (TRow m'a, TRow m'b) ->
        forM (Map.toList m'a) \(k, t'a) ->
            case Map.lookup k m'b of
                Just t'b -> pure $ CEqual (t'a, t'b)
                _ -> fail $ "row label " <> pretty k <> " not found: " <> pretty m'a <> " ◁ " <> pretty m'b

    (TVar tv'a, TVar tv'b) -> pure [CRow $ SubRow (TVar tv'a) (TVar tv'b)]
    (TVar tv'a, TRow m'b)  -> pure [CRow $ SubRow (TVar tv'a) (TRow m'b) ]
    (TRow m'a,  TVar tv'b) -> pure [CRow $ SubRow (TRow m'a)  (TVar tv'b)]

    _ -> fail $ "expected row types for row sub, got " <> pretty a <> " ◁ " <> pretty b

apMergeSubRows :: [RowConstraint] -> ([EqualityConstraint], [RowConstraint])
apMergeSubRows cs =
    let (subs, concats) = subSplit cs
        (subMap, eqs, ignore) = merge subs
        subs' = Map.toList subMap <&> \(b, as) -> SubRow (TRow as) (TVar b)
    in (eqs, subs' <> ignore <> concats) where
    merge subs =
        foldBy mempty subs \constr (subMap, eqs, ignore) ->
            case constr of
                (TRow aMap, TVar b) ->
                    let bMap = fromMaybe mempty (Map.lookup b subMap)
                        (bMap', newEqs) = joinMap (bMap, mempty) (Map.toList aMap)
                    in (Map.insert b bMap' subMap, newEqs <> eqs, ignore)
                (a, b) -> (subMap, eqs, SubRow a b : ignore)
    joinMap =
        foldr \(k, t) (bMap, eqs) ->
            case Map.lookup k bMap of
                Just t' -> (bMap, (t, t') : eqs)
                _ -> (Map.insert k t bMap, eqs)


apConcatRows :: Type -> Type -> Type -> Ti [Constraint]
apConcatRows a b c = case (a, b, c) of
    (TRow m'a, TRow m'b, t'c) ->
        let (m'c, eqs) =
                foldBy mempty (Map.keys m'a `List.union` Map.keys m'b) \k (m, cs) ->
                    case (Map.lookup k m'a, Map.lookup k m'b) of
                        (Just t'a, Just t'b) -> (Map.insert k t'a m, CEqual (t'a, t'b) : cs)
                        (Just t'a, _) -> (Map.insert k t'a m, cs)
                        (_, Just t'b) -> (Map.insert k t'b m, cs)
                        _ -> (m, cs)
        in pure (CEqual (TRow m'c, t'c) : eqs)
      
    (TVar tv'a, TRow m'b,  TRow m'c) -> pure (mergeVar tv'a m'b m'c)
    (TRow m'a,  TVar tv'b, TRow m'c) -> pure (mergeVar tv'b m'a m'c)

    (TVar tv'a, TVar tv'b, TVar tv'c) -> pure [CRow $ ConcatRow (TVar tv'a) (TVar tv'b) (TVar tv'c)]
    (TVar tv'a, TVar tv'b, TRow m'c ) -> pure [CRow $ ConcatRow (TVar tv'a) (TVar tv'b) (TRow m'c) ]
    (TVar tv'a, TRow m'b,  TVar tv'c) -> pure [CRow $ ConcatRow (TVar tv'a) (TRow m'b)  (TVar tv'c)]
    (TRow m'a,  TVar tv'b, TVar tv'c) -> pure [CRow $ ConcatRow (TRow m'a)  (TVar tv'b) (TVar tv'c)]

    _ -> fail $ "expected row types for row concat, got " <> pretty a <> " ⊙ " <> pretty b <> " ~ " <> pretty c
    where
    mergeVar tv'a m'b m'c =
        let (m'a, cs) = foldBy mempty (Map.toList m'c) \(k, t'c) (ma, es) ->
                case Map.lookup k m'b of
                    Just t'b -> (ma, CEqual (t'b, t'c) : es)
                    _ -> (Map.insert k t'c ma, es)
        in (CEqual (TVar tv'a, TRow m'a) : cs)





ti :: Env -> UntypedTerm -> Either String (Scheme (Type, TypedTerm), Subst)
ti env x = second snd <$> flip runTi (0, mempty) do
    (cs :=> x'@(AnnOf t'x)) <- infer env x
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