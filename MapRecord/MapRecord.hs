{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables #-}

module MapRecord where

import Data.Kind
import qualified Data.Map as Map
import qualified Data.List as List

class Key (key :: Type -> Type) where
   rank :: key t -> Int
   initial :: key t -> t
   showkey :: key t -> String

class Key key => Haskey field (key :: Type -> Type) | field -> key where
   match :: key t -> field -> Maybe t
   make :: key t -> t -> field

data Update (t :: Type -> Type) where
  Update :: t x -> x -> Update t

data Some (t :: Type -> Type) where
  Some:: t index -> Some t

newtype Record key field = Record (Map.Map (Some key) field)

get:: forall field (key::Type -> Type) i.
  Haskey field key =>
  key i -> Record key field -> i
get k (Record m) = case Map.lookup (Some k) m of
  Nothing -> initial @key k
  Just field -> case match k field of
                   Nothing -> initial @key k
                   Just n -> n

put :: Haskey field key => Record key field -> key i -> i -> Record key field
put (Record m) key v = Record(Map.insert (Some key) (make key v) m)

applyUpdates :: Haskey field key => Record key field -> [Update key] -> Record key field
applyUpdates record xs = List.foldl' (\ r (Update k v) -> put r k v) record xs

initialRecord = Record (Map.empty)

-- Instances

instance Key key => Eq (Some key) where
  (Some x) == (Some y) = rank x == rank y

instance Key key => Ord (Some key) where
  compare (Some x) (Some y) = compare (rank x) (rank y)

instance Key k => Show(Some k) where
  show (Some x) = showkey x

instance (Key k, Show field) => Show (Record k field) where
  show (Record m) = show m

-- ========================================================
-- A simple example, isomorphic to: data Record = Record {a :: Int, b :: String, c :: Bool}

-- We need a pair of types

data Field = A Int | B String | C Bool
  deriving Show

data Label t where
  A' :: Label Int
  B' :: Label String
  C' :: Label Bool

-- We need 5 simple functions to fill in the Key and Haskey constraints

instance Key Label where
  rank A' = 0
  rank B' = 1
  rank C' = 2
  initial A' = 0
  initial B' = "OK"
  initial C' = False
  showkey A' = "A'"
  showkey B' = "B'"
  showkey C' = "C'"

instance Haskey Field Label where
  match A' (A x) = Just x
  match B' (B x) = Just x
  match C' (C x) = Just x
  match _ _ = Nothing
  make A' n = A n
  make B' n = B n
  make C' n = C n
