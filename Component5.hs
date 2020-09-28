
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
{-# LANGUAGE UndecidableSuperClasses    #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingVia                #-}

-- ==============================================================

module Component5 where

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
import Data.Coerce

-- ========================================================
-- Some mock types to manipulate in the examples

proxy :: forall a. Proxy a
proxy = Proxy :: Proxy a


class Eq t => Val t where
  plus :: t -> t -> t
  zero :: t

instance Val [Int] where
  plus x y = x ++ y
  zero = []

instance Val Int where
  plus x y = x + y
  zero = 0

instance Val Bool where
  plus x y = x || y
  zero = False

newtype Coin = Coin Int
  deriving (Eq,Val,Show)

data Value = Value Coin (Map.Map String Int)
  deriving (Show,Eq)

instance Val Value where
  zero = Value (Coin 0) Map.empty
  plus (Value c1 m1) (Value c2 m2) = Value (plus c1 c2) (Map.unionWith (+) m1 m2)

-- =================================================

class Crypto t where

data C
instance Crypto C where

data M
instance Crypto M where

data K
instance Crypto K where

-- ==============================================================================
-- Dimensions of variation, and the range of the variation for each dimension
-- ==============================================================================

-- =============================
-- Dimension Tokens

data Token = Ada | MultiAsset          -- Range of variation
  deriving Show

data TokenRep(a:: Token) v where       -- Each point in the range is assigned an asscociated type
  AdaR :: TokenRep 'Ada Coin
  MultiAssetR ::
     TokenRep 'MultiAsset Value

deriving instance Show (TokenRep t v)
                                        -- This class ensure that TokenRep choices are the only ones allowed

class ChooseV (c::Token) t | c -> t where vrep:: TokenRep c t
instance ChooseV Ada Coin           where vrep = AdaR
instance ChooseV MultiAsset Value   where vrep = MultiAssetR

-- ==================================
-- Dimension Transactions

data Tx = Normal | Forging  | Plutus deriving Show  -- Range of variation

data TxRep (a:: Tx)  v where
  NormalR :: TxRep 'Normal Bool
  ForgingR :: TxRep 'Forging [Int]
  PlutusR :: Era e => TxRep 'Plutus (TxT e)   -- Here I don't know what this is in the current scope
                                              -- The idea is that in the scope where I make the Era instance,
                                              -- I can also make the ChooseT instance.

deriving instance Show (TxRep t v)

class ChooseT (c::Tx) t | c -> t where trep:: TxRep c t
instance ChooseT Normal Bool     where trep = NormalR
instance ChooseT Forging [Int]   where trep = ForgingR
-- instance ChooseT Plutus <to be defined>        where trep = PlutusR

-- =========================================
-- Dimension Crypto Alg

data Crypt = Mock | Concrete | Kes | New deriving Show

data CryptRep (a:: Crypt) v  where         -- Range of variation
  MockR :: CryptRep 'Mock M
  ConcreteR :: CryptRep 'Concrete C
  KesR :: CryptRep 'Kes K


deriving instance Show (CryptRep t v)

class ChooseC (c::Crypt) t | t -> c where crep:: CryptRep c t
instance ChooseC Concrete C where crep = ConcreteR
instance ChooseC Mock M     where crep = MockR
instance ChooseC Kes K      where crep = KesR

-- ================================================================
-- An Era assembles a type in each dimension of variation
-- Checks that each of these meets it requirements, and is a legal
-- point in that dimensions range.
-- ================================================================

class ( ChooseC (CryptIndex e) (CryptT e),  -- Legal points
        ChooseT (TxIndex e) (TxT e),
        ChooseV (TokenIndex e) (TokenT e),
        Val (TokenT e),                     -- Meet requirements
        Crypto (CryptT e),
        Show (TxT e)
      ) =>

  Era (e::Type) where                       -- Class magic to make things automatic

  type CryptT e = t | t -> e
  type CryptIndex e = (t::Crypt) | t -> e
  cryptRep :: CryptRep (CryptIndex e) (CryptT e)
  cryptRep = crep @(CryptIndex e)

  type TokenT e = t | t -> e
  type TokenIndex e = (t::Token) | t -> e
  tokenRep :: TokenRep (TokenIndex e) (TokenT e)
  tokenRep = vrep @(TokenIndex e)

  type TxT e = t | t -> e
  type TxIndex e = (t::Tx) | t -> e
  txRep :: TxRep (TxIndex e) (TxT e)
  txRep = trep @(TxIndex e)



-- ========================================================================
-- Now some instances. Just choose legal points in each dimensions range

data G

instance Era G where
  type CryptT G = C
  type CryptIndex G = Concrete
  type TokenT G = Coin
  type TokenIndex G = Ada
  type TxT G = Bool
  type TxIndex G = Normal


-- Illustrate we can add new type inscope away from where Era is defined

data PTx = PTx Int Bool [Int] deriving Show
instance ChooseT Plutus PTx where trep = PlutusR

data H

instance Era H where
  type CryptT H = M
  type CryptIndex H = Mock
  type TokenT H = Value
  type TokenIndex H = MultiAsset
  type TxT H = PTx
  type TxIndex H = Plutus

-- ==============================================
-- Now some example programs


test60 :: Era e => TokenT e -> TokenT e
test60 v = plus v v


test61 :: Era e => TokenRep rep (TokenT e) -> TokenT e -> Int
test61 AdaR (Coin 5) = 1
test61 MultiAssetR (Value (Coin n) _) = n+3

test62 :: forall e. Era e => TokenT e -> Int
test62 t = case (tokenRep @e, t) of
            (AdaR, Coin 5) -> 1
            (MultiAssetR, Value (Coin n) _) -> n+3


generalizeToken :: forall e a. Era e => (forall rep. Era e => TokenRep rep (TokenT e) -> a) -> a
generalizeToken f = f (tokenRep @e)

generalizeCrypt :: forall e a. Era e => (forall rep. Era e => CryptRep rep (CryptT e) -> a) -> a
generalizeCrypt f = f (cryptRep @e)

generalizeTx :: forall e a. Era e => (forall rep. Era e => TxRep rep (TxT e) -> a) -> a
generalizeTx f = f (txRep @e)
