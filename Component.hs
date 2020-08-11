{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE FlexibleContexts       #-}


module Component where

import qualified Data.Map as Map
import Data.Map(Map)
import Data.Word(Word32,Word64)

-- =============================================
-- Component Names (Uninhabited Types)
-- The idea is to build class instances indexed by each of these uninhabited types
-- Since these types are unique, there can only be one instance at that type.
-- That instance can be thought of as a Module with the unique type as its name.
-- Different instances can have the same Component Name. (Foo Mock) and (Bar Mock) each
-- name a unique module, but (Foo Mock) has a different set of operations than (Bar Mock).

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


-- ========================================
-- A Signable Module

class Signable name a where

instance Signable ShortHash Word32 where
instance Signable ShortHash Coin where

instance Signable LongHash Word64 where
instance Signable LongHash Value where
instance Signable LongHash Coin where

-- =============================================
-- Crypto Modules

-- An closed version (where the types (PublicKey n), (SecretKey n), and (Signature n) are hidden)
class Crypto n where
  type PublicKey n :: *
  type SecretKey n :: *
  type Signature n :: *
  sign:: (Signable n a) => Nm n -> a -> SecretKey n -> Signature n
  verify:: (Signable n a)=> PublicKey n -> a -> Signature n -> Either String ()
  keysize :: Nm n -> Int
  makepair :: Nm n -> IO (PublicKey n,SecretKey n)

-- An open version (where the types public, secret, and signature escape. Note the functional dependency)
class Crypto2 n public secret signature | n -> public, n -> secret, n -> signature where
  sign2:: (Signable n a) => Nm n -> a -> secret-> signature
  verify2:: (Signable n a)=> Nm n -> public -> a -> signature -> Either String ()
  keysize2 :: Nm n -> Int
  makepair2 :: Nm n -> IO (public,secret)

instance Crypto LongHash where
  type PublicKey LongHash = Word64
  type SecretKey LongHash = Word64
  type Signature LongHash = Word64
  sign _ x secret = undefined
  verify public a signature = undefined
  keysize LongHash = 64
  makepair LongHash = undefined

instance Crypto ShortHash where
  type PublicKey ShortHash = Word32
  type SecretKey ShortHash = Word32
  type Signature ShortHash = Word32
  sign _ x secret = undefined
  verify public a signature = undefined
  keysize ShortHash = 32
  makepair ShortHash = undefined

instance Crypto2 LongHash Word64 Word64 Word64 where
  sign2 _ x secret = undefined
  verify2 _ public a signature = undefined
  keysize2 LongHash = 64
  makepair2 LongHash = undefined

instance Crypto2 ShortHash Word32 Word32 Word32 where
  sign2 _ x secret = undefined
  verify2 _ public a signature = undefined
  keysize2 ShortHash = 32
  makepair2 ShortHash = undefined


-- ================================================
-- Asset Modules

-- An open version (where the type value escapes. Note the functional dependency)
class Asset n value | n -> value where
   zero :: Nm n -> value
   plus :: Nm n -> value -> value -> value
   comment :: Nm n -> String

-- A closed version (where the type (Val n) is hidden)
class Asset2 n where
   type Val n :: *
   zero2 :: Nm n -> Val n
   plus2 :: Nm n -> Val n -> Val n -> Val n
   comment2 :: Nm n -> String

-- Concrete Asset types

newtype Coin = Coin Int
data Value = Value Coin (Map String Integer)

-- Module instances

instance Asset JustAda Coin where
   zero _ = Coin 0
   plus _ (Coin x) (Coin y) = Coin(x+y)
   comment JustAda = "Shelley style assets"

instance Asset MultiAsset Value where
   zero _ = Value (Coin 0) Map.empty
   plus _ (Value (Coin x) xs) (Value (Coin y) ys) = Value (Coin (x+y)) (Map.unionWith (+) xs ys)
   comment MultiAsset = "Goguen style multi assets"

instance Asset2 JustAda where
   type Val JustAda = Coin
   zero2 _ = Coin 0
   plus2 _ (Coin x) (Coin y) = Coin(x+y)
   comment2 JustAda = "Shelley style assets"

instance Asset2 MultiAsset where
   type Val MultiAsset = Value
   zero2 _ = Value (Coin 0) Map.empty
   plus2 _ (Value (Coin x) xs) (Value (Coin y) ys) = Value (Coin (x+y)) (Map.unionWith (+) xs ys)
   comment2 MultiAsset = "Goguen style multi assets"

-- ===================================================
-- Modules for an Era

class Era n where
   make:: (Crypto c, Signable c a, Asset m a) => Nm n -> Nm m -> Nm c -> IO ()

instance Era Shelley where
   make Shelley (v) (c) = do
      (public,secret) <- makepair c
      let foo = sign c (zero v) secret
      pure ()

instance Era Goguen where
   make Goguen (v) (c) = do
      (public,secret) <- makepair c
      let foo = sign c (zero v) secret
      pure ()


foo v c = do
      (public,secret) <- makepair c
      let foo = sign c (zero v) secret
      pure ()
{-
bar v c = undefined
  where Crypto{sign,makepair} = open c
        Asset{zero,plus} = open v
-}

shelley :: IO ()
shelley = make Shelley JustAda ShortHash

goguen :: IO ()
goguen = make Goguen MultiAsset LongHash

main :: IO ()
main = shelley