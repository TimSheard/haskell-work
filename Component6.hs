
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
{-# LANGUAGE DataKinds                  #-}

-- ==============================================================

module Component6 where

import qualified Data.Map as Map
import Data.Map(Map)
import Data.Set(Set,size)
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
  getcoin :: t -> Coin

instance Val [Int] where
  plus x y = x ++ y
  zero = []
  getcoin xs = Coin(length xs)

instance Val Int where
  plus x y = x + y
  zero = 0
  getcoin n = Coin n

instance Val Bool where
  plus x y = x || y
  zero = False
  getcoin b = Coin 0

newtype Coin = Coin Int
  deriving (Eq,Show)

instance Val Coin where
  plus (Coin x) (Coin y) = Coin(x +y)
  zero = Coin 0
  getcoin c = c

data Value = Value Coin (Map.Map String Int)
  deriving (Show,Eq)

instance Val Value where
  zero = Value (Coin 0) Map.empty
  plus (Value c1 m1) (Value c2 m2) = Value (plus c1 c2) (Map.unionWith (+) m1 m2)
  getcoin (Value c m) = c

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

-- ============================================
-- Dimension Asset
-- A closed dimension. We know in advance all the choices, and all the types we need are in scope.

data Asset = Ada | MultiAsset          -- Range of variation
  deriving Show

-- Each dimension and era has class (IsAsset) with an associated type.
-- We use the ALLCAPS version(ASSET) of the dimension as the assocated
-- type's name. Some dimensions have a superclass that tells what what
--  operations the associated type must support (Val)

class Val (ASSET t e) => IsAsset (t::Asset) e  where
  type ASSET t e = x | x -> e t

-- Instances provide an un-inhabited type (Foo) and an Asset tag (Ada)

data Foo
instance IsAsset Ada Foo where
   type ASSET Ada Foo = Coin

data Bar
instance IsAsset MultiAsset Bar where
   type ASSET MultiAsset Bar = Value

-- =============================================
-- A closed reflective instance

-- Each point in the range has a GADT constructor idexed by the
-- Asset tag, and its associated type

data AssetRep(a:: Asset) v where
  AdaR ::        AssetRep 'Ada Coin
  MultiAssetR :: AssetRep 'MultiAsset Value

deriving instance Show (AssetRep t v)

-- AssetC class witness the assocated type choice with one of the AssetRep constructors.

class AssetC (c::Asset) t | c -> t  where assetC:: AssetRep c t
instance AssetC Ada Coin            where assetC = AdaR
instance AssetC MultiAsset Value    where assetC = MultiAssetR


class ReflectAsset (t::Asset) (e::Type) where  assetRep:: AssetRep t (ASSET t e)

instance  (AssetC t (ASSET t e), IsAsset t e) => ReflectAsset t e
  where assetRep = assetC @t @(ASSET t e)

-- =================================================
-- Examples

bar :: IsAsset t e => ASSET t e -> ASSET t e
bar x = plus x x


foo :: forall t e. ReflectAsset t e => ASSET t e -> Coin
foo c = case (assetRep @t @e) of
          (AdaR) -> c
          (MultiAssetR) -> getcoin c


-- =============================
-- A closed dimension using GADTs
-- We know in advance all the choices, and all the types we need are in scope.

data ASSETA (a:: Asset) where       -- Each associated type is a GADT constructor with an Asset index, use the ALLCAPS convention
  CoinA:: Int -> ASSETA Ada
  ValueA :: (ASSETA Ada) -> Map.Map String Int -> ASSETA MultiAsset

deriving instance Eq (ASSETA a)
deriving instance Show (ASSETA a)

instance Val (ASSETA Ada) where
  plus (CoinA x) (CoinA y) = CoinA (x+y)
  zero = CoinA 0
  getcoin (CoinA n) = Coin n

instance Val (ASSETA MultiAsset) where
  plus (ValueA c m1) (ValueA d m2) = ValueA (plus c d) (Map.unionWith (+) m1 m2)
  zero = ValueA (CoinA 0) Map.empty
  getcoin (ValueA (CoinA x) _) = Coin x

data Baz
instance IsAsset Ada Baz where
   type ASSET Ada Baz = ASSETA Ada

data Bong
instance IsAsset MultiAsset Bong where
   type ASSET MultiAsset Bong = ASSETA MultiAsset


-- ==============================================================
-- A closed dimension where important types are not in scope

data TxBody = Normal | Forging  | Plutus deriving Show

class TxBodyC t e (TXBODY t e)  => IsTxBody (t::TxBody) e where
   type TXBODY t e = x | x -> t e
   type TxBodyC t e :: Type -> Constraint
   -- Since some types are not in scope we can put off what operations
   -- work on (TXBODY t e) until the place we make TxBodyC instances.

data TxIn = TxIn
data TxOut = TxOut
data Cert = Cert
data Slot

data NormBody = NormBody
  { norminputs :: Set TxIn,
    normoutputs :: Set TxOut,
    normslot :: Slot
  }

data ForgeBody = ForgeBody
  { forgeinputs :: Set TxIn,
    forgeoutputs :: Set TxOut,
    forgeslot :: Slot,
    forge :: Value
  }

class Body t where
  inputs :: t -> Set TxIn
  outputs :: t -> Set TxOut
  slot :: t -> Slot

instance Body NormBody where
  inputs = norminputs
  outputs = normoutputs
  slot = normslot

instance Body ForgeBody where
  inputs = forgeinputs
  outputs = forgeoutputs
  slot = forgeslot

class Body t => Both t where
  forges :: t -> Value

instance Both ForgeBody where
  forges x = forge x

class None t where
instance None t where

data Shelley
instance IsTxBody Normal Shelley where
   type TXBODY Normal Shelley = NormBody
   type TxBodyC Normal Shelley = Body

data ShelleyMA
instance IsTxBody Forging ShelleyMA where
   type TXBODY Forging ShelleyMA = ForgeBody
   type TxBodyC Forging ShelleyMA = Body


-- We can almost make a refective version of this. We get stuck on the Plutus


data TxBodyRep (t:: TxBody)  v where
  NormalR :: TxBodyRep 'Normal NormBody
  ForgingR :: TxBodyRep 'Forging ForgeBody
  PlutusR :: TxBodyC t e (TXBODY t e) => TxBodyRep 'Plutus (TXBODY t e)
       -- Here I don't know what (TXBODY or TxBodyC) are in the current scope
       -- The idea is that in the scope where I make the TxBodyC instance,
       -- I can also make the TxBodyR instance. This avoids the mutual import problem

class TxBodyR (c::TxBody) t | c -> t  where bodyRep:: TxBodyRep c t
instance TxBodyR Normal NormBody      where bodyRep = NormalR
instance TxBodyR Forging ForgeBody    where bodyRep = ForgingR


class ReflectTxBody (c::TxBody) (t::Type) | c -> t where  txbodyRep:: TxBodyRep c (TXBODY c t)

instance  (TxBodyR t (TXBODY t e), IsTxBody t e) => ReflectTxBody t e
  where txbodyRep = bodyRep @t @(TXBODY t e)

-- ================
-- Now imagine we are in a file with a different scope.

data Plut
instance IsTxBody Plutus Plut where
   type TXBODY Plutus Plut = Int
   type TxBodyC Plutus Plut = Num

instance TxBodyR Plutus Int where
   bodyRep = PlutusR


getInSize :: forall t e. ReflectTxBody t e => TXBODY t e -> Int
getInSize body = case txbodyRep @t @e of
                   NormalR -> size(outputs body)
                   ForgingR -> size(inputs body)
                   -- PlutusR -> body + 3


-- ====================================

data Crypt = Mock | Concrete | Kes | New deriving Show

class Crypto (CRYPT c e) => IsCrypt (c::Crypt) e where
   type CRYPT c e = x | x -> c e


data CryptRep (a:: Crypt) v  where         -- Range of variation
  MockR :: CryptRep 'Mock M
  ConcreteR :: CryptRep 'Concrete C
  KesR :: CryptRep 'Kes K

class RepCrypt (c::Crypt) t | c -> t where crep:: CryptRep c t
instance RepCrypt Concrete C where crep = ConcreteR
instance RepCrypt Mock M     where crep = MockR
instance RepCrypt Kes K      where crep = KesR

class ReflectCrypt (c::Crypt) (e::Type) | c -> e
  where  cryptRep:: CryptRep c (CRYPT c e)

instance  (RepCrypt c (CRYPT c e), IsCrypt c e) => ReflectCrypt c e
  where cryptRep = crep @c @(CRYPT c e)

-- ==========================================================

class NewType new old | new -> old where
  into :: old -> new
  from :: new -> old

instance NewType Coin Int where
  into = Coin
  from (Coin x) = x

data Test

{-
instance IsAsset Ada Test where
  data ASSET Ada Test = TT Coin


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
        Show (TxT e),
        Constr e (TxT e)
      ) =>

  Era (e::Type) where                       -- Class magic to make things automatic

  type CryptT e = t | t -> e
  type CryptIndex e = (t::Crypt) | t -> e
  cryptRep :: CryptRep (CryptIndex e) (CryptT e)
  cryptRep = crep @(CryptIndex e)

  type Constr e = (t :: Type -> Constraint) | t -> e -- Another way to avoid the mutual import problem

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
  type Constr G = Show


-- Illustrate we can add new type inscope away from where Era is defined

data PTx = PTx Int Bool [Int] deriving (Show,Ord,Eq)
instance ChooseT Plutus PTx where trep = PlutusR

data H

instance Era H where
  type CryptT H = M
  type CryptIndex H = Mock
  type TokenT H = Value
  type TokenIndex H = MultiAsset
  type TxT H = PTx
  type TxIndex H = Plutus
  type Constr H = Always

class Always t where
instance Always t where

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


generalizeToken :: forall e a . (Era e) => (forall rep. TokenRep rep (TokenT e) -> a) -> a
generalizeToken f = f (tokenRep @e)


generalizeCrypt :: forall e a. Era e => (forall rep. CryptRep rep (CryptT e) -> a) -> a
generalizeCrypt f = f (cryptRep @e)

generalizeTx :: forall e a. Era e => (forall rep. TxRep rep (TxT e) -> a) -> a
generalizeTx f = f (txRep @e)

-- ===============================================================
-- Independant, but nestable classes with Chained examples
-- ===============================================================


class ( ChooseC (CryptI e) (CryptType e),
        Crypto (CryptType e)
      ) =>

  CryptoEra (e::Type) where

  type CryptType e = t | t -> e
  type CryptI e = (t::Crypt) | t -> e
  cryptR :: CryptRep (CryptI e) (CryptType e)
  cryptR = crep @(CryptI e)

-- ===============

class ( ChooseV (TokenI e) (TokenType e),
        Val (TokenType e)
      ) =>

  TokenEra (e::Type) where

  type TokenType e = t | t -> e
  type TokenI e = (t::Token) | t -> e
  tokenR :: TokenRep (TokenI e) (TokenType e)
  tokenR = vrep @(TokenI e)


-- ======================================

class ( ChooseT (TxI e) (TxType e),
        Show (TxType e),
        Constr e (TxType e)
      ) =>

  TxEra (e::Type) where

  type Constrain e = (t :: Type -> Constraint) | t -> e
  type TxType e = t | t -> e
  type TxI e = (t::Tx) | t -> e
  txR :: TxRep (TxI e) (TxType e)
  txR = trep @(TxI e)

-- Nested instances

instance CryptoEra H where
  type CryptType H = M
  type CryptI H = Mock

instance CryptoEra H => TokenEra H where
  type TokenType H = Value
  type TokenI H = MultiAsset

instance TokenEra H => TxEra H where
  type TxType H = PTx
  type TxI H = Plutus
  type Constrain H = Always


test60b :: TokenEra e => TokenType e -> TokenType e
test60b v = plus v v

{- -- This doesn't type since CryptoEra does not have enough constraints
test60c :: CryptoEra e => TokenType e -> TokenType e
test60c v = plus v v
-}


test61b :: TokenEra e => TokenRep rep (TokenType e) -> TokenType e -> Int
test61b AdaR (Coin 5) = 1
test61b MultiAssetR (Value (Coin n) _) = n+3

-}