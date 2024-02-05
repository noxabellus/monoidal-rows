import Data.Map.Strict qualified as Map

import Util
import Pretty
import Ast
import Subst
import Ti
import Infer





pattern TReadCon = TCon ("Read", KType :~> KEffect)
pattern TRead a = TApp TReadCon a

pattern TWriteCon = TCon ("Write", KType :~> KEffect)
pattern TWrite a = TApp TWriteCon a

env0 :: Env
env0 = Env
  { typeEnv = Map.fromList
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
  , effectEnv = Map.fromList
    [ ( "Read"
      , Forall [BoundType 0 KType] $
            [] :=> Map.fromList
                [ ( "read"
                  , (TUnit, TVar (TvBound (BoundType 0 KType)))
                )
            ]
      )
    , ( "Write"
      , Forall [BoundType 0 KType] $
            [] :=> Map.fromList
                [ ( "write"
                  , (TVar (TvBound (BoundType 0 KType)), TUnit)
                )
            ]
      )
    ]
  , dataEnv = Map.fromList
    [ ( "V2i"
      , Forall [] $ DProd $ Map.fromList
            [ ("x", TInt)
            , ("y", TInt)
            ]
      )
    , ( "V3"
      , Forall [BoundType 0 KType] $ DProd $ Map.fromList
            [ ("x", TVar $ TvBound (BoundType 0 KType))
            , ("y", TVar $ TvBound (BoundType 0 KType))
            , ("z", TVar $ TvBound (BoundType 0 KType))
            ]
      )
    , ( "Maybe"
      , Forall [BoundType 0 KType] $ DSum $ Map.fromList
            [ ("Just", TVar $ TvBound (BoundType 0 KType))
            , ("Nothing", TUnit)
            ]
      )
    ]
  }


test :: UntypedTerm -> IO ()
test = compose (ti env0) \case
  Left e -> putStrLn "failed:" >> putStrLn e
  Right (x, s) -> do
    putStrLn "succeeded:"
    putStrLn $ pretty x
    putStrLn $ pretty (apply s s)



main :: IO ()
main = do putStrLn "Hi bitch"