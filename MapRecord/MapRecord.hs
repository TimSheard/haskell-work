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
import Cardano.Binary(ToCBOR(..),FromCBOR(..))
import Data.Typeable(Typeable)

-- ================================================

class Key (key :: Type -> Type) where
   rank :: key t -> Int
   initial :: key t -> t
   showkey :: key t -> String

class Key key => Haskey field (key :: Type -> Type) | field -> key where
   match :: key t -> field -> Maybe t
   make :: key t -> t -> field
   makeUpdate :: field -> Update key

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

putUpdate :: Haskey field key => Record key field -> Update key -> Record key field
putUpdate rec (Update key i) = put rec key i

putField :: Haskey field key => Record key field -> field -> Record key field
putField rec f = putUpdate rec (makeUpdate f)

applyUpdates :: Haskey field key => Record key field -> [Update key] -> Record key field
applyUpdates record xs = List.foldl' putUpdate record xs

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

instance (Typeable key, ToCBOR field) => ToCBOR (Record key field) where
  toCBOR (Record m) = toCBOR (Map.elems m)

instance (Typeable key, Haskey field key, FromCBOR field) => FromCBOR (Record key field) where
  fromCBOR = lift <$> fromCBOR
     where lift :: [field] -> Record key field
           lift xs = applyUpdates initialRecord (map makeUpdate xs)

-- ========================================================
-- A simple example, isomorphic to:
-- data Record = Record {a :: Int, b :: String, c :: Bool}
-- Instead we define (HasKey Field Label) and (Key Label) instances and then
-- We get he type (Record Field Label) type for free, with a full set of operations.

-- We need a pair of types Field and Label

data Field = A Int | B String | C Bool
  deriving Show

data Label t where
  A' :: Label Int
  B' :: Label String
  C' :: Label Bool

-- We need 6 simple functions to fill in the Key and Haskey constraints
-- All but 'initial' could be derived Generically

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
  makeUpdate (A x) = Update A' x
  makeUpdate (B x) = Update B' x
  makeUpdate (C x) = Update C' x
