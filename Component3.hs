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
import Data.Coerce

proxy :: forall a. Proxy a
proxy = Proxy :: Proxy a

-- These are inscope classes



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
{-
class ( Crypt (Crypto e),
        ValC e (Value e)
      ) => Era e where

  type Crypto e :: Type               -- in-scope

  type Value e = t | t -> e           -- out-of-scope and injective. No duplicates on RHS
  type ValC e :: Type -> Constraint   -- Arbitrary operations supported
  valRep :: ValRep e                  -- limited to where (ValRep e) is inhabited

  data TxBody e :: Type               -- out-of-scope and data (injective). Every instance is a new type.
  bodyRep :: BodyRep e                -- limited to where (BodyRep e) is inhabited
-}

-- ===============================================
-- This is an outofscope class

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
  deriving (Eq,Val)

data Value = Value Coin (Map.Map String Int)
  deriving Eq

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

-- =============================

{-
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
-}

-- =====================================

class Triple t where
   type One t :: Type
   type Two t :: Type
   type Three t :: Type

instance Triple (a,b,c) where
  type One (a,b,c) = a
  type Two (a,b,c) = b
  type Three (a,b,c) = c

-- ======================================

data Rng1 = A | B | C
data Rng2 = Mx | N
data Rng3 = X | Y | Z

data Dim1 (a:: Rng1)  where
  A1 :: Dim1 'A
  B1 :: Dim1 'B
  C1 :: Dim1 'C

data Dim2 (a:: Rng2)  where
  M2 :: Dim2 'Mx
  N2 :: Dim2 'N

data Dim3 (a:: Rng3)  where
  X3 :: Dim3 'X
  Y3 :: Dim3 'Y
  Z3 :: Dim3 'Z

{-
class Trip t where
   type Onex t :: Rng1
   type Twox t :: Rng2
   type Threex t :: Rng3

instance Trip (Dim1 a,Dim2 b,Dim3 c) where
  type Onex  (Dim1 a,Dim2 b,Dim3 c) = a
  type Twox  (Dim1 a,Dim2 b,Dim3 c) = b
  type Threex  (Dim1 a,Dim2 b,Dim3 c) = c
-}

-- =====================================================

class Triple t => Test a t | a -> t where
  one :: a -> One t
  two :: a -> Two t
  type T1 t :: Type

instance Test Int (Int,Bool,String) where
  one n = n+4
  two n = n==99
  type T1 (Int,Bool,String) = String

-- =====================================================

class ( Triple t,
        Crypto (Cr a),
        Val (Vl a)
       ) => E a t | a -> t where
  prox :: Proxy a
  type Cr a :: Type
  data Vl a :: Type

  type D1 t :: Type
  dim1Rep :: Proxy a -> One t

  type D2 t :: Type
  dim2Rep :: Proxy a -> Two t


-- =======================================
-- The Q instance

data Q
type QT = (Dim1 A, Dim2 Mx, Dim3 Z)

instance E Q QT where
   prox = Proxy
   type Cr Q = C
   newtype Vl Q = Vlq Int

   type D1 QT = Bool
   dim1Rep _ = A1

   type D2 QT = [String]
   dim2Rep _ = M2

deriving instance Val (Vl Q)
deriving instance Eq (Vl Q)

-- =======================================
-- The Z instance

data R
type RT = (Dim1 B, Dim2 N, Dim3 Z)

instance E R RT where
   prox = Proxy
   type Cr R = C
   newtype Vl R = Vlr Bool

   type D1 RT = [Int]
   dim1Rep _ = B1

   type D2 RT = Int
   dim2Rep _ = N2

deriving instance Val (Vl R)
deriving instance Eq (Vl R)

test01 :: forall e ds. E e ds => Vl e -> Vl e
test01 x = plus x zero

{-
test21 :: forall e ds. E e ds => Vl e -> D1 ds -> Int
test21 val z =
     case dim1Rep (proxy @e) of
        A1 -> 3
        B1 -> 5
        C1 -> 6
-}

----------------------------------------------------------

data List1 ts where
  Nil1  :: List1 '[]
  Cons1 :: x -> List1 xs -> List1 (x ': xs)


-- Build List1 using infix: (Int # Bool # String # Nil1) :: List1 Rep (Int, (Bool, (String, ())))
infixr 5 #
y # ys = Cons1 y ys


-- ======================================================
{-
class Types t where
  data CryptoType t :: Type
  data ValType t :: Type
  data TxType t :: Type

instance (Crypto a, Val b, Show c) => Types (a,b,c) where
  newtype CryptoType (a,b,c) = Cr a
  newtype ValType (a,b,c) = V b
  newtype TxType (a,b,c) = T { unT :: c }

deriving instance (Types (a,b,c),Crypto a) => Crypto (CryptoType (a,b,c))
deriving instance (Types (a,b,c),Eq b) => Eq (ValType (a,b,c))
deriving instance (Types (a,b,c),Val b) => Val (ValType (a,b,c))

instance (Types (a,b,c),Show c) => Show (TxType (a,b,c)) where
  show (T x) = show x
instance (Types (a,b,c),Show b) => Show (ValType (a,b,c)) where
  show (V x) = show x
instance (Types (a,b,c),Show a) => Show (CryptoType (a,b,c)) where
  show (Cr x) = show x


class ( Types ts,
        Crypto (CryptoType ts),
        Val (ValType ts),
        Show (TxType ts)
       ) => EEra e ts | e -> ts , ts -> e where


data V
type VT = (C,Int,String)
instance EEra V VT where


test45 :: forall e ts. (EEra e ts) => ValType ts -> TxType ts -> String
test45 v t = if v==v then show t else "NO"

-}
-- ============================================================
{-
type family CryptoType t = s | s -> t where
  CryptoType (c,v,t) = c
type family ValType t = s | s -> t where
  ValType (c,v,t) = v
type family TxType t = s | s -> t where
  TxType (c,v,t) = t
-}

-- === Tokens ======

data Token = Ada | MultiAsset
  deriving Show

data TokenRep(a:: Token)  where
  AdaR :: TokenRep 'Ada
  MultiAssetR :: TokenRep 'MultiAsset

deriving instance Show (TokenRep t)


class Val (TokenT rep) => TokenC (rep:: Token) where
  type TokenT rep = ty | ty -> rep
  tokenRep :: TokenRep rep

instance TokenC Ada where
   type TokenT Ada = Coin
   tokenRep = AdaR

instance TokenC MultiAsset where
   type TokenT MultiAsset = Value
   tokenRep = MultiAssetR

-- === Transactions ======

data Tx = Normal | Forging  deriving Show

data TxRep (a:: Tx)  where
  NormalR :: TxRep 'Normal
  ForgingR :: TxRep 'Forging

deriving instance Show (TxRep t)


class Show (TxT rep) => TxC (rep:: Tx) where
  type TxT rep = ty | ty -> rep
  txRep :: TxRep rep

instance TxC Normal where
  type TxT Normal = Bool
  txRep = NormalR

instance TxC Forging where
  type TxT Forging = [Int]
  txRep = ForgingR

-- === Crypto Alg ========

data Crypt = Mock | Concrete | Kes deriving Show

data CryptRep (a:: Crypt)  where
  MockR :: CryptRep 'Mock
  ConcreteR :: CryptRep 'Concrete
  KesR :: CryptRep 'Kes

deriving instance Show (CryptRep t)


class Crypto (CryptT rep) => CryptC (rep:: Crypt) where
  type CryptT rep = ty | ty -> rep
  cryptRep :: CryptRep rep

instance CryptC Mock where
  type CryptT Mock = M
  cryptRep = MockR

instance CryptC Concrete  where
  type CryptT Concrete = C
  cryptRep = ConcreteR

instance CryptC Kes where
  type CryptT Kes = K
  cryptRep = KesR




-- =============================================================

data Dims (c::Crypt) (v::Token) (t::Tx) = Dims (CryptRep c) (TokenRep v) (TxRep t)
  deriving Show

data Ex f where
   Ex:: (f t) -> Ex f

class Dimensional

class Era (e::Type) (ds:: Type) | e -> ds, ds -> e where
  data CryptoType e :: Type
  data ValType e :: Type
  data TxType e :: Type
  zzrep :: Proxy e -> Ex TokenRep

data G
type GD = Dims Concrete Ada Normal

class (CryptC c, TokenC v, TxC t) => Foo c v t where

{-
instance (CryptC Concrete, TokenC Ada, TxC Normal) => Era G (Dims Concrete Ada Normal) where
  newtype CryptoType G = Cr C
     deriving Crypto
  newtype ValType G = V Coin
     deriving (Eq,Val)
  newtype TxType G = T { unT :: Bool}
     deriving Show
  zzrep _ = Ex AdaR
-}

-- instance Era G GD where

{-
class Dimensional t where
  data CryptoType t :: Type
  data ValType t :: Type
  data TxType t :: Type

instance Dimensional (Dims c v t) where
  newtype CryptoType (Dims c v t) = Cr (CryptT c)
  newtype ValType (Dims c v t) = V (TokenT v)
  newtype TxType (Dims c v t) = T { unT :: (TxT t)}




deriving instance (Dimensional (Dims c v t),Crypto (CryptT c)) => Crypto (CryptoType (Dims c v t))

deriving instance (Dimensional (Dims c v t),Eq v) => Eq (ValType (Dims c v t))
deriving instance (Types (a,b,c),Val b) => Val (ValType (a,b,c))

instance (Types (a,b,c),Show c) => Show (TxType (a,b,c)) where
  show (T x) = show x
instance (Types (a,b,c),Show b) => Show (ValType (a,b,c)) where
  show (V x) = show x
instance (Types (a,b,c),Show a) => Show (CryptoType (a,b,c)) where
  show (Cr x) = show x




class Dimensional ds where

instance  (CryptC c, TokenC v, TxC t) => Dimensional (Dims c v t) where

class Dimensional ds => Era e ds | e -> ds, ds -> e where



data G
type GD = Dims Concrete Ada Normal


-}
