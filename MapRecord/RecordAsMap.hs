{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}


module RecordAsMap where

import Data.Kind
import qualified Data.Map as Map
import qualified Data.List as List

data R1 = R1 {a :: Int, b :: String, c :: Bool}

-- We need a pair of types

data Field = A Int | B String | C Bool
  deriving Show

data Key t where
  A' :: Key Int
  B' :: Key String
  C' :: Key Bool

-- We need 4 simple functions

rank :: Key t -> Int
rank A' = 0
rank B' = 1
rank C' = 2

match :: Key t -> Field -> Maybe t
match A' (A x) = Just x
match B' (B x) = Just x
match C' (C x) = Just x
match _ _ = Nothing

make :: Key t -> t -> Field
make A' n = A n
make B' n = B n
make C' n = C n

initial :: Key t -> t
initial A' = 0
initial B' = "OK"
initial C' = False

-- We need some reusable machinery

data Update (t :: Type -> Type) where
  Update :: t x -> x -> Update t

data Some (t :: Type -> Type) where
  Some:: t index -> Some t

newtype R key = R (Map.Map (Some key) Field)

get :: Key i -> R Key -> i
get k (R m) = case Map.lookup (Some k) m of
  Nothing -> initial k
  Just field -> case match k field of
                   Nothing -> initial k
                   Just n -> n

put :: R Key -> Update Key -> R Key
put (R m) (Update key v) = R(Map.insert (Some key) (make key v) m)

applyUpdates :: R Key -> [Update Key] -> R Key
applyUpdates r xs = List.foldl' put r xs

us = [Update A' 33, Update C' True]

-- instances

instance Show (Some Key) where
  show (Some A') = "A'"
  show (Some B') = "B'"
  show (Some C') = "C'"

instance Show (Key i)  where
  show A' = "A'"
  show B' = "B'"
  show C' = "C'"

instance Eq (Some Key) where
  (Some x) == (Some y) = (rank x) == (rank y)

instance Ord (Some Key) where
  compare (Some x) (Some y) = compare (rank x) (rank y)

deriving instance Show(Some key) => Show (R key)