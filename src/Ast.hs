module Ast where

import Data.Functor ((<&>))
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.List qualified as List

import Util
import Pretty

data Term
    = Var Var
    | Unit
    | Int Int
    | Lambda Patt Term
    | App Term Term
    | Ann Term Type
    | Match Term [(Patt, Term)]

    | ProductConstructor (Either [Term] [(Name, Term)])
    | ProductConcat Term Term
    | ProductNarrow Term
    | ProductSelect Term (Either Int Name)

    | SumConstructor (Either Int Name) Term
    | SumExpand Term

    | Handler Type (Map Name (Patt, Term)) (Maybe (Patt, Term)) Term
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

    | PProductConstructor (Either [Patt] [(Name, Patt)])
    | PSumConstructor (Either Int Name) Patt

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
pattern KInt = KConstant "Int"
pattern KString = KConstant "String"
pattern KType = KConstant "Type"
pattern KEffect = KConstant "Effect"
pattern KDataRow = KConstant "DataRow"
pattern KEffectRow = KConstant "EffectRow"
pattern (:~>) a b = KArrow a b




data Type
    = TVar TypeVar
    | TCon TypeCon
    | TApp Type Type
    | TDataRow [Field]
    | TEffectRow [Type]
    | TConstant Constant
    deriving (Show, Eq, Ord)
type Field = (Label, Type)
type Label = (Type, Type)
type TypeCon = (String, Kind)
data BoundType = BoundType Int Kind deriving (Show, Eq, Ord)
data MetaType = MetaType Int Kind deriving (Show, Eq, Ord)
data TypeVar
    = TvBound BoundType
    | TvMeta MetaType
    deriving (Show, Eq, Ord)
pattern TFunCon = TCon ("->_in", KType :~> KType :~> KEffectRow :~> KType)
pattern TProdCon = TCon ("Π", KType :~> KDataRow :~> KType)
pattern TSumCon = TCon ("Σ", KType :~> KDataRow :~> KType)
pattern TUnit = TCon ("()", KType)
pattern TInt = TCon ("Int", KType)
pattern TProd t r = TApp (TApp TProdCon t) r
pattern TSum t r = TApp (TApp TSumCon t) r
pattern TFun a b e = TApp (TApp (TApp TFunCon a) b) e
pattern TDataRowNil = TDataRow Nil
pattern TEffectRowNil = TEffectRow Nil
pattern TConcrete a <- a@(\case TVar _ -> False; _ -> True -> True)
pattern TVarBound i k = TVar (TvBound (BoundType i k))
pattern TVarMeta i k = TVar (TvMeta (MetaType i k))
pattern TcInt i = TConstant (CInt i)
pattern TcString s = TConstant (CString s)

dataSingleton :: Field -> Type
dataSingleton f = TDataRow [f]

effectSingleton :: Type -> Type
effectSingleton t = TEffectRow [t]


data Constant
    = CInt Int
    | CString String
    deriving (Show, Eq, Ord)

data Constraint
    = CEquality EqualityConstraint
    | CRow RowConstraint
    | CData DataConstraint
    deriving (Show, Eq, Ord)

data EqualityConstraint = Type `Equal` Type
    deriving (Show, Eq, Ord)

data DataConstraint
    = IsProd Type Type
    | IsSum Type Type
    deriving (Show, Eq, Ord)

data RowConstraint
    = SubRow Type Type
    | ConcatRow Type Type Type
    deriving (Show, Eq, Ord)

{-# COMPLETE CEqual, CSubRow, CConcatRow, CProd, CSum #-}

pattern CEqual a b = CEquality (Equal a b)

pattern CSubRow a b = CRow (SubRow a b)
pattern CConcatRow a b c = CRow (ConcatRow a b c)

pattern CProd a b = CData (IsProd a b)
pattern CSum a b = CData (IsSum a b)


type Scheme a = Quantified (Qualified a)


infixr 0 `Forall`
data Quantified a = Forall [Kind] a
    deriving (Functor, Show)

instance Semigroup a => Semigroup (Quantified a) where
    Forall vs a <> Forall vs' a' = Forall (vs <> vs') (a <> a')

instance Monoid a => Monoid (Quantified a) where
    mempty = Forall mempty mempty


data Qualified a = Qualified [Constraint] a
    deriving (Functor, Show)
infixr 0 :=>
{-# COMPLETE (:=>) #-}
pattern (:=>) cs t = Qualified cs t

instance Semigroup a => Semigroup (Qualified a) where
    Qualified cs a <> Qualified cs' a' = Qualified (cs <> cs') (a <> a')

instance Monoid a => Monoid (Qualified a) where
    mempty = Qualified mempty mempty





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
        TConstant c -> case c of
            CInt _ -> KInt
            CString _ -> KString




instance Pretty Term where
    prettyPrec p = \case
        Var v -> prettyVarStrip v
        Unit -> "()"
        Int i -> prettyPrec p i
        Lambda q x -> parensIf (p > 0) $ "λ" <> pretty q <> ". " <> pretty x
        App a b -> parensIf (p > 1) $ prettyPrec 1 a <> " " <> prettyPrec 2 b
        Ann x t -> parensIf (p > 0) $ pretty x <> " : " <> pretty t
        Match x cs -> parensIf (p > 0) $ "match " <> pretty x <> " with " <> List.intercalate " | " (pretty <$> cs)
        ProductConstructor (Right fs) -> parens $ List.intercalate ", " $ fs <&> \(n, x) -> n <> " = " <> pretty x
        ProductConstructor (Left xs) -> brackets $ List.intercalate ", " (pretty <$> xs)
        ProductConcat a b -> parensIf (p > 2) $ prettyPrec 2 a <> " ⊙ " <> prettyPrec 3 b
        ProductNarrow x -> parensIf (p > 3) $ "narrow " <> prettyPrec 3 x
        ProductSelect x (Left l) -> parensIf (p > 6) $ prettyPrec 6 x <> " \\ " <> show l
        ProductSelect x (Right n) -> parensIf (p > 6) $ prettyPrec 6 x <> " \\ " <> n
        SumConstructor (Left l) x -> angles $ show l <> " = " <> pretty x
        SumConstructor (Right n) x -> angles $ n <> " = " <> pretty x
        SumExpand x -> parensIf (p > 5) $ "expand " <> prettyPrec 5 x
        Handler t hm r b -> parensIf (p > 0) $
            "with " <> pretty t <> " handler "
                <> List.intercalate ", " do
                    Map.toList hm <&> \(n, (v, x)) ->
                        n <> " = " <> pretty v <> " => " <> pretty x
                <> maybe "" (\(v, x) -> "return " <> pretty v <> " => " <> pretty x) r
            <> " do " <> pretty b

instance Pretty Patt where
    prettyPrec p = \case
        PVar v -> prettyVarStrip v
        PUnit -> "()"
        PInt i -> prettyPrec p i
        PAnn x t -> parensIf (p > 0) $ pretty x <> " : " <> pretty t
        PProductConstructor (Left m) -> parens $ List.intercalate ", " (pretty <$> m)
        PProductConstructor (Right m) -> braces $ List.intercalate ", " $ m <&> \(n, x) -> n <> " = " <> pretty x
        PSumConstructor (Left l) x -> parensIf (p > 0) $ show l <> " " <> pretty x
        PSumConstructor (Right n) x -> parensIf (p > 0) $ n <> " " <> prettyPrec 1 x
        PWildcard -> "_"

instance Pretty Kind where
    prettyPrec p = \case
        KConstant n -> n
        KArrow a b -> parensIf (p > 0) $ prettyPrec 1 a <> " ↠ " <> pretty b

instance Pretty Type where
    prettyPrec p = \case
        TVar tv -> prettyVarStrip tv
        TCon (n, _) -> n
        TFun a b e -> parensIf (p > 0) $ prettyPrec 1 a <> " → " <> pretty b <> " in " <> pretty e
        TApp a b -> parensIf (p > 1) $ prettyPrec 1 a <> " " <> prettyPrec 2 b
        TDataRow m -> braces $ List.intercalate ", " $ m <&> (\((x, n), t) -> pretty x <> "/" <> pretty n <> " ∷ " <> pretty t)
        TEffectRow m -> brackets $ List.intercalate ", " (pretty <$> m)
        TConstant c -> pretty c

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

instance Pretty Constant where
    pretty = \case
        CInt i -> show i
        CString s -> show s

instance Pretty Constraint where
    prettyPrec p = \case
        CEqual a b -> parensIf (p > 0) $ pretty a <> " ~ " <> pretty b
        CSubRow a b -> parensIf (p > 0) $ pretty a <> " ◁ " <> pretty b
        CConcatRow a b c -> parensIf (p > 0) $ pretty a <> " ⊙ " <> pretty b <> " ~ " <> pretty c
        CProd a b -> parensIf (p > 0) $ pretty a <> " Π " <> pretty b
        CSum a b -> parensIf (p > 0) $ pretty a <> " Σ " <> pretty b

instance Pretty RowConstraint where
    prettyPrec p = \case
        SubRow a b -> parensIf (p > 0) $ pretty a <> " ◁ " <> pretty b
        ConcatRow a b c -> parensIf (p > 0) $ pretty a <> " ⊙ " <> pretty b <> " ~ " <> pretty c

instance Pretty EqualityConstraint where
    prettyPrec p (a `Equal` b) = parensIf (p > 0) $ pretty a <> " ~ " <> pretty b

instance Pretty DataConstraint where
    prettyPrec p = \case
        IsProd a b -> parensIf (p > 0) $ pretty a <> " Π " <> pretty b
        IsSum a b -> parensIf (p > 0) $ pretty a <> " Σ " <> pretty b

instance Pretty a => Pretty (Quantified a) where
    prettyPrec p (Forall [] qt) = prettyPrec p qt
    prettyPrec p (Forall bvs qt) = parensIf (p > 0) $ "∀" <> List.intercalate ", " (prettyVar 0 . uncurry BoundType <$> zip [0..] bvs) <> ". " <> pretty qt

instance Pretty a => Pretty (Qualified a) where
    prettyPrec p (Qualified [] t) = prettyPrec p t
    prettyPrec p (Qualified cs t) = parensIf (p > 0) $ pretty cs <> " ⇒ " <> pretty t



splitTypeCon :: Type -> Maybe (Var, [Type])
splitTypeCon = \case
    TApp a b -> do
        (name, args) <- splitTypeCon a
        pure (name, args <> [b])

    TCon (n, _) -> pure (n, [])

    _ -> Nothing