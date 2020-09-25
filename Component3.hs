{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE RecordWildCards        #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE UndecidableSuperClasses #-}



module Component3 where

import qualified Data.Map as Map
import Data.Map(Map)
import Data.Word(Word32,Word64)
-- import Data.Registry
-- import Data.Typeable
import Type.Reflection(TypeRep(..),typeOf)
import Data.Type.Equality(testEquality)
import Data.Constraint(Constraint,Dict(..),withDict)
import Data.Proxy
import Data.Kind

proxy :: forall a. Proxy a
proxy = Proxy :: Proxy a

-- These are inscope classes

class Crypt t where

-- Some dimensions are over a closed set of Era instances. We need to know what those are where
-- we define the Era class.

data Byron
data Shelley
data Goguen

data BodyRep t where
     ShelleyB :: BodyRep Shelley
     GoguenB:: BodyRep Goguen
     ByronB:: BodyRep Byron

data ValRep v where
   ShelleyV :: ValRep Shelley
   GoguenV :: ValRep Goguen

-- ======================================================

class ( Crypt (Crypto e),
        ValC e (Value e)
      ) => Era e where

  type Crypto e :: Type               -- in-scope

  type Value e = t | t -> e           -- out-of-scope and injective. No duplicates on RHS
  type ValC e :: Type -> Constraint   -- Arbitrary operations supported
  valRep :: ValRep e                  -- limited to where (ValRep e) is inhabited

  data TxBody e :: Type               -- out-of-scope and data (injective). Every instance is a new type.
  bodyRep :: BodyRep e                -- limited to where (BodyRep e) is inhabited


-- ===============================================
-- This is an outofscope class

class Eq t => Val t where
  plus :: t -> t -> t
  zero :: t

-- =================================================

data C
instance Crypt c where

instance Val [Int] where
  plus x y = x ++ y
  zero = []

instance Era Shelley where
   type Crypto Shelley = C

   type Value Shelley = [Int]
   type ValC Shelley = Val
   valRep = ShelleyV

   newtype TxBody Shelley = BodyS String
   bodyRep = ShelleyB

-- ========================================

instance Era Goguen where
   type Crypto Goguen = C

   type Value Goguen = Int
   type ValC Goguen = Num
   valRep = GoguenV

   newtype TxBody Goguen = BodyG Bool
   bodyRep = GoguenB

instance Val Int where
  plus x y = x + y
  zero = 0

foo :: Era e => BodyRep e -> TxBody e -> Int
foo ShelleyB (BodyS string) = length string
foo GoguenB (BodyG bool) = if bool then 99 else 100
foo ByronB _ = error "Unreachable"

foo2 :: forall e. Era e => TxBody e -> Int
foo2 body = (foo (bodyRep @e) body)

-- Note how each clause uses operations from a different class.

bar:: forall e t. Era e => ValRep e -> Value e -> Value e
bar ShelleyV v = plus v zero   -- Here we use the Val class
bar GoguenV v = v + v          -- Here we use the Num class


baz :: forall e. Era e => Value e -> Value e
baz v = case (valRep @e) of
           ShelleyV -> plus v zero
           GoguenV -> v + v



deriving instance Eq(TxBody Goguen)

instance Val (TxBody Goguen) where
   zero = BodyG False
   plus (BodyG x) (BodyG y) = BodyG(x || y)

deriving instance Show (BodyRep t)
deriving instance Show (ValRep t)