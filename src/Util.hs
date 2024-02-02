
module Util where

import Data.Map.Strict (Map)
import Data.Set (Set)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set

import Data.Foldable

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

compose :: (a -> b) -> (b -> c) -> (a -> c)
compose = flip (.)

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



