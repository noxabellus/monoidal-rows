import Data.Map.Strict qualified as Map


import Ast
import Ti





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







main :: IO ()
main = do putStrLn "Hi bitch"