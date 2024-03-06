import Data.Map.Strict qualified as Map

import Util
import Pretty
import Ast
import Ti
import Infer





pattern TReadCon = TCon ("Read", KType :~> KEffect)
pattern TRead a = TApp TReadCon a

pattern TWriteCon = TCon ("Write", KType :~> KEffect)
pattern TWrite a = TApp TWriteCon a

pattern TMaybeCon = TCon ("Maybe", KType :~> KType)
pattern TMaybe a = TApp TMaybeCon a

pattern TFail = TCon ("Fail", KEffect)

pattern TStateCon = TCon ("State", KType :~> KEffect)
pattern TState a = TApp TStateCon a

pattern TPairCon = TCon ("Pair", KType :~> KType :~> KType)
pattern TPair a b = TApp (TApp TPairCon a) b

pattern Pair a b = ProductConstructor (Right [("fst", a), ("snd", b)])

pattern Just' a = SumConstructor (Right "Just") a
pattern Nothing' = SumConstructor (Right "Nothing") Unit

env0 :: Env
env0 = Env
  { typeEnv = Map.fromList
    [ ( "read"
      , Forall [KType] $
            [] :=>
              TFun
                  TUnit
                  (TVarBound 0 KType)
                  (TEffectRow
                      [TRead (TVarBound 0 KType)])
      )
    , ( "write"
      , Forall [KType] $
            [] :=>
              TFun
                  (TVarBound 0 KType)
                  TUnit
                  (TEffectRow
                      [TWrite (TVarBound 0 KType)])
      )
    , ( "i_add"
      , Forall [KType] $
            [] :=>
              TFun (TPair TInt TInt) TInt
                  (TEffectRow [])
      )
    , ( "combobulate"
      , Forall [] $
            [] :=>
              TFun
                  TUnit
                  (TFun TInt TInt (TEffectRow []))
                  (TEffectRow [])
      )
    , ( "pstate"
      , Forall [KType, KType, KEffectRow, KEffectRow] $
            [CConcatRow
              (TEffectRow [TState (TVarBound 0 KType)])
              (TVarBound 2 KEffectRow)
              (TVarBound 3 KEffectRow)] :=>
                TFun
                  (TPair
                      (TVarBound 0 KType)
                      (TFun TUnit (TVarBound 1 KType)
                          (TVarBound 3 KEffectRow)))
                  (TPair
                    (TVarBound 1 KType)
                    (TVarBound 0 KType))
                  (TVarBound 2 KEffectRow)
      )
    , ( "maybeFail"
      , Forall [KType, KEffectRow, KEffectRow] $
            [CConcatRow
              (TEffectRow [TFail])
              (TVarBound 1 KEffectRow)
              (TVarBound 2 KEffectRow)] :=>
                TFun
                  (TFun TUnit (TVarBound 0 KType) (TVarBound 2 KEffectRow))
                  (TMaybe
                      (TVarBound 0 KType))
                  (TVarBound 1 KEffectRow)
      )
    ]
  , effectEnv = Map.fromList
    [ ( "Read"
      , Forall [KType] $
            [] :=> Map.fromList
                [ ( "read"
                  , (TUnit, Forall [] $ TVarBound 0 KType)
                )
            ]
      )
    , ( "Write"
      , Forall [KType] $
            [] :=> Map.fromList $
                [ ( "write"
                  , (TVarBound 0 KType, Forall [] TUnit)
                )
            ]
      )
    , ( "State"
      , Forall [KType] $
            [] :=> Map.fromList
                [ ( "get"
                  , (TUnit, Forall [] $ TVarBound 0 KType)
                )
                , ( "put"
                  , (TVarBound 0 KType, Forall [] TUnit)
                )
            ]
      )
    , ( "Fail"
      , Forall [] $
            [] :=> Map.fromList
                [ ( "fail"
                  , (TUnit, Forall [KType] $ TVarBound 0 KType)
                )
            ]
      )
    ]
  , dataEnv = Map.fromList
    [ ( "V2i"
      , Forall [] $ DProd
            [ ((TcInt 0, TcString "x"), TInt)
            , ((TcInt 1, TcString "y"), TInt)
            ]
      )
    , ( "V3"
      , Forall [KType] $ DProd
            [ ((TcInt 0, TcString "x"), TVarBound 0 KType)
            , ((TcInt 1, TcString "y"), TVarBound 0 KType)
            , ((TcInt 2, TcString "z"), TVarBound 0 KType)
            ]
      )
    , ( "Maybe"
      , Forall [KType] $ DSum
            [ ((TcInt 0, TcString "Just"), TVarBound 0 KType)
            , ((TcInt 1, TcString "Nothing"), TUnit)
            ]
      )
    , ( "Pair"
      , Forall [KType, KType] $ DProd
            [ ((TcInt 0, TcString "fst"), TVarBound 0 KType)
            , ((TcInt 1, TcString "snd"), TVarBound 1 KType)
            ]
      )
    ]
  }


test :: UntypedTerm -> IO ()
test = compose (ti env0) \case
  Left e -> putStrLn "failed:" >> putStrLn e
  Right (x, _) -> do
    putStrLn "succeeded:"
    putStrLn $ pretty x

testPoly :: Scheme UntypedTerm -> IO ()
testPoly = compose (tiPoly env0) \case
  Left e -> putStrLn "failed:" >> putStrLn e
  Right (x, _) -> do
    putStrLn "succeeded:"
    putStrLn $ pretty x


main :: IO ()
main = do
  putStrLn "Hi bitch"

  test $
    Lambda (PVar "x") $
      Handler (TRead TInt) (Map.fromList [("read", (PUnit, App (Var "continue") (Int 1)))]) Nothing $
        App (Var "i_add") (Pair (App (Var "read") Unit) (Var "x"))

  test $
    Lambda (PAnn (PVar "action") (TFun TUnit TInt (TEffectRow [TFail, TState TInt]))) $
      App (Var "maybeFail") (Lambda PUnit $ App (Var "pstate") (Pair (Int 0) (Var "action")))

  test $
    Lambda (PAnn (PVar "action") (TFun TUnit TInt (TEffectRow [TFail, TState TInt]))) $
      App (Var "pstate") (Pair (Int 0) (Lambda PUnit $ App (Var "maybeFail") (Var "action")))

  testPoly $ Forall [KType] $ [] :=>
    Lambda (PVar "action") $
      Handler TFail
        (Map.fromList [("fail", (PUnit, Nothing'))])
        (Just (PVar "x", Just' (Var "x")))
        (App (Var "action") Unit)
      `Ann` TMaybe (TVarBound 0 KType)