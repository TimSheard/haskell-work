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

module Component2 where

import qualified Data.Map as Map
import Data.Map(Map)
import Data.Word(Word32,Word64)
import Data.Registry
-- import Data.Typeable
import Type.Reflection(TypeRep(..),typeOf)
import Data.Type.Equality(testEquality)
import Data.Constraint(Constraint,Dict(..),withDict)

-- ======================================================
-- The Name class associates a unique name to a type and
-- to a unique Module with that type.

class Name n t | n -> t where
   open :: Nm n -> t
   encap:: Nm n -> Module t
   encap nm = Module nm (open nm)


-- ======================================================
-- The Reify class associates a unique name 'n' to a
-- type 't', which can have an arbitrary class constraint 'c'
-- This allows us to lift a class to piece of data which
-- encodes the same information. There are two ways one might
-- use this:
-- 1) the data can be 'Dict' from Data.Constraint. (easy to do)
-- 2) the data can be a record structure. (better for type inference)

class Reify n c t | n -> c, n -> t where
   reify :: c => Nm n -> t


-- =============================================
-- Component Names (Uninhabited Types)
-- The idea is to build a class Name instance indexed by each of these uninhabited types.
-- Since these types are unique, there can only be one instance at that type.
-- That instance can be thought of as naming a Type with a unique name.
-- Usually the type is a record structure with a bunch of functions and values
-- that can be thought of as a Module.

data LongHash
data ShortHash
data Mock
data JustAda
data MultiAsset
data Shelley
data Goguen

-- A singleton type, one value constructor for each component name. Thus a value
-- (Nm t) like ShortHash or MultiAsset uniquely identifies an instance, and is a
-- first class value, that can be passed around to identitfy Modules.

data Nm t where
    LongHash  :: Nm LongHash
    ShortHash :: Nm ShortHash
    Mock :: Nm Mock
    JustAda :: Nm JustAda
    MultiAsset :: Nm MultiAsset
    Shelley :: Nm Shelley
    Goguen :: Nm Goguen

deriving instance Show (Nm t)

-- ===============================================================================
-- A Module encapsulate both a Name and its Type (usually a Record of operations)
-- This is a first class value, that can be passed around, returned for functions
-- and 'open'ed to extract the operations of the Module.

data Module t where
   Module:: Name n t => Nm n -> t -> Module t

-- ========================================
-- What can be signed?

class Signable a where

instance Signable Word32 where
instance Signable Coin where
instance Signable Word64 where
instance Signable Value where

-- ===================
-- Crypto Modules

data Crypto publickey secretkey signature = Crypto
  { sign:: forall a . Signable a => a -> secretkey -> signature
  , verify:: forall a . Signable a => publickey -> a -> signature -> Either String ()
  , keysize :: Int
  , makepair :: IO (publickey,secretkey)
  }

-- We can create a concrete value of type (Crypto a b c)

longHash :: Crypto Word64 Word64 Word64
longHash = Crypto
  { sign = \ x secret -> undefined
  , verify = \ public a signature -> undefined
  , keysize = 64
  , makepair = pure (undefined,undefined)
  }

-- Assign a unigue name to this value

instance Name LongHash (Crypto Word64 Word64 Word64) where
   open LongHash = longHash

-- We can also assign a unique name to an anonymous value, but now its not really anonymous
-- since we can 'open' the name to get the value back!

instance Name ShortHash (Crypto Word32 Word32 Word32) where
   open ShortHash = Crypto
     { sign = \ x secret -> undefined
     , verify = \ public a signature -> undefined
     , keysize = 32
     , makepair = pure (undefined,undefined)
     }

-- We can 'open' a Crypto module and use its contents. The type shown can be infered

-- foo:: (Name n (Crypto t t2 t1), Signable a) => Nm n -> a -> (Int, t2 -> t1)
foo mod y = (keysize + 18, sign y)
  where Crypto{..} = open mod

-- ==================================
-- Concrete Asset types

newtype Coin = Coin Int deriving Show
data Value = Value Coin (Map String Integer)

-- ==================================
-- MultiAsset Modules

data Asset value = Asset
  { zero :: value
  , plus :: value -> value -> value
  , comment :: String
  }

instance Name JustAda (Asset Coin) where
   open JustAda =
     Asset { zero = Coin 0
           , plus = \ (Coin x) (Coin y) -> Coin(x+y)
           , comment = "Coin assets"
           }

instance Name MultiAsset (Asset Value) where
   open MultiAsset = Asset zero plus comment
      where zero = Value (Coin 0) Map.empty
            plus (Value (Coin x) xs) (Value (Coin y) ys) = Value (Coin (x+y)) (Map.unionWith (+) xs ys)
            comment = "Multi assets"

-- =======================================================================
-- Era Modules. An Era specifies a Crypto and Asset choice of operations

data Era t1 t2 t3 v = Era
   { crypto :: Crypto t1 t2 t3
   , asset :: Asset v
   }

-- Lets Name a couple of Era's

instance Name Shelley (Era Word32 Word32 Word32 Coin) where
   open Shelley = Era (open ShortHash) (open JustAda)

instance Name Goguen (Era Word64 Word64 Word64 Value) where
   open Goguen = Era (open LongHash) (open MultiAsset)

-- We can make an IO(), a main function, from an Era

makeMain:: forall x y z a . Signable a => Crypto x y z -> Asset a -> IO ()
makeMain c v = do
      (public,secret) <- makepair
      let foo = sign zero secret
      pure ()
  where Crypto{..} = c
        Asset{..} = v

makeMain2 c v = do
      (public,secret) <- makepair
      let foo = sign zero secret
      pure ()
  where Crypto{..} = open c
        Asset{..} = open v

main1 = makeMain crypto asset where Era{..} = open Shelley
main2 = makeMain crypto asset where Era{..} = open Goguen

-- ==========================================================
-- What is really cool is that this is completely compatible
-- with Data.Registry

registry =
    val (encap LongHash)
 +: val (open ShortHash)
 +: val (open JustAda)
 +: val (encap MultiAsset)
 +: val (encap Shelley)
 +: val (encap Goguen)
 +: fun (makeMain @Word32 @Word32 @Word32 @Coin)
 +: end

main3 = make @(IO ()) registry

-- ===========================================
-- Show instances

instance Show (Crypto a b c) where
  show Crypto{..} = "Crypto "++show keysize

instance Show (Asset v) where
   show Asset{..} = comment

instance Show (Era t1 t2 t3 v) where
   show Era{..} = "Era: "++show crypto++", "++show asset

instance Show (Module t) where
   show (Module nm x) = "Module "++show nm

-------------------------------------------------------------

data Exists f where
  Hide:: TypeRep a -> f a -> Exists f

-- =============================================

class MAsset value where
  mzero :: value
  mplus :: value -> value -> value
  mcomment :: forall proxy . proxy value -> String

instance (MAsset Coin) where
   mzero = Coin 0
   mplus = \ (Coin x) (Coin y) -> Coin(x+y)
   mcomment _ = "Coin assets"

instance Reify Mock (MAsset Coin) (Asset Coin) where
   reify Mock = Asset mzero mplus (mcomment ([]::[Coin]))

instance Reify JustAda (MAsset Coin) (Dict (MAsset Coin)) where
   reify JustAda = Dict



-- bar :: (c, Reify n c (Asset value)) => Nm n -> value
bar m = plus zero zero
   where Asset{..} = reify m

-- =============================================
-- Example with Associated Type Classes

class MultAsset t where
   data Ass t :: *
   nzero :: Ass t
   nplus :: Ass t -> Ass t -> Ass t
   ncomment :: Nm t -> String

instance (MultAsset Shelley) where
   newtype Ass Shelley = C Coin deriving Show
   nzero = C (Coin 0)
   nplus = \ (C (Coin x)) (C (Coin y)) -> C(Coin(x+y))
   ncomment Shelley = "Coin assets"

instance Reify Shelley (MultAsset Shelley) (Asset (Ass Shelley)) where
   reify Shelley = Asset nzero nplus (ncomment Shelley)

unC (C x) = x

-- =============================================
-- 2nd Example with Associated Type Classes using 'type' instead of 'data'

class MultAsset2 t where
   type Ass2 t :: *
   nzero2 :: Nm t -> Ass2 t
   nplus2 :: Nm t -> Ass2 t -> Ass2 t -> Ass2 t
   ncomment2 :: Nm t -> String

instance (MultAsset2 Goguen) where
   type Ass2 Goguen = Coin
   nzero2 Goguen = Coin 0
   nplus2 Goguen (Coin x) (Coin y) = Coin(x+y)
   ncomment2 Goguen = "Coin assets"

instance Reify Goguen (MultAsset2 Goguen) (Asset Coin) where
   reify Goguen = Asset (nzero2 Goguen) (nplus2 Goguen) (ncomment2 Goguen)
