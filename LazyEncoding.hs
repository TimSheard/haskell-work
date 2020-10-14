{-# OPTIONS_GHC  -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}


{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances   #-}
{-# LANGUAGE GeneralizedNewtypeDeriving  #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE UndecidableInstances #-}

module LazyEncoding
   ( Foo(..,Foo),
     Lazy(..),
     FooFlat(..),
   ) where

import Prelude hiding (span)
import Control.Monad (unless)

import Data.ByteString(ByteString)
import Data.ByteString.Short(ShortByteString, fromShort, toShort)
import Data.ByteString.Lazy(toStrict)
import Data.String(fromString)
import Data.Text
import Data.Typeable

import Codec.CBOR.Decoding ( Decoder, decodeWord8, decodeWord64, decodeInteger, decodeWithByteSpan )
import Codec.CBOR.Encoding ( Encoding(..), encodeWord8, encodeWord64, encodeInteger, encodeString, encodeBytes, encodePreEncoded)
import Codec.CBOR.Read( deserialiseFromBytesWithSize )
import Codec.CBOR.Write( toLazyByteString, toStrictByteString )
import Codec.CBOR.Read( deserialiseFromBytes )

import Cardano.Binary
   ( ToCBOR(toCBOR), FromCBOR(fromCBOR), encodeListLen,
     decodeBreakOr, decodeListLenOrIndef,  matchSize,
     Annotated(..), fromCBORAnnotated, reAnnotate, serialize', Annotator(..),slice, FullByteString(..), annotatedDecoder,ByteSpan
   )


-- fromCBOR :: FromCBOR a => Decoder s a
-- toCBOR ∷ ToCBOR a => a → Encoding
-- encodeBytes :: ByteString -> Encoding
-- encodeString :: Text -> Encoding
-- decodeString :: Decoder s Text
-- decodeWithByteSpan :: Decoder s a -> Decoder s (a, ByteOffset, ByteOffset)
-- decodeInteger :: Decoder s Integer
-- decodeWord64 :: Decoder s Word64
-- decodeWord8 :: Decoder s Word8
-- deserialiseFromBytes :: (forall s. Decoder s a) -> ByteString -> Either DeserialiseFailure (ByteString, a)
-- deserialiseFromBytesWithSize :: (forall s. Decoder s a) -> ByteString -> Either DeserialiseFailure (ByteString, ByteOffset, a)
-- toLazyByteString:: Encoding -> ByteString

-- A route to get a ByteString for testing
source :: ByteString
source = fromString "abc23"


-- ===========================================================
-- Intoduce a normal type, and make CBOR instances for it

data FooFlat = FooFlat Integer Text
  deriving (Show,Typeable)

instance ToCBOR FooFlat where
  toCBOR (FooFlat n s) = encodeListLen 2 <> toCBOR n <> toCBOR s

instance FromCBOR FooFlat where
  fromCBOR = decodeRecordNamed (fromString "Foo") (const 2) $ do
     n <- fromCBOR
     s <- fromCBOR
     pure $ FooFlat n s

pattern Foo x y <- FooLazy (Lazy _ (FooFlat x y)) where
  Foo x y =  FooLazy (Lazy (serialize' t) t) where t = FooFlat x y

newtype Foo = FooLazy (Lazy FooFlat)
  deriving (ToCBOR,FromCBOR)


-- ===========================================================
-- We can wrap any indexed type in a Lazy, And we need only
-- one instance each for ToCBOR and FromCBOR of Lazy

data Lazy f = Lazy ByteString f
  deriving Show

instance (Typeable f) => ToCBOR (Lazy f) where
  toCBOR (Lazy bytes f) = encodePreEncoded bytes

instance (Typeable f,ToCBOR f,FromCBOR f) => FromCBOR (Lazy f) where
  fromCBOR = do
     (Annotated fe bytes) <- fmap reAnnotate fromCBORAnnotated
     pure (Lazy bytes fe)


-- ========================================================================

data MemoBytes t = Memo !t
                        {-# UNPACK #-} !ShortByteString

instance (Typeable t) => ToCBOR (MemoBytes t) where
  toCBOR (Memo t bytes) = encodePreEncoded (fromShort bytes)

instance (Typeable t, FromCBOR (Annotator t)) => FromCBOR (Annotator (MemoBytes t)) where
  fromCBOR = do
     (Annotated (Annotator getT) span) <- fromCBORAnnotated
     pure (Annotator (\ fullbytes -> Memo (getT fullbytes) (extractShort fullbytes span)))

instance Eq t => Eq (MemoBytes t) where (Memo x _) == (Memo y _) = x==y

instance Show t => Show (MemoBytes t) where show (Memo y _) = show y

instance Ord t => Ord (MemoBytes t) where compare (Memo x _) (Memo y _) = compare x y


extractShort:: FullByteString -> ByteSpan -> ShortByteString
extractShort (Full lazybytes) span = toShort(toStrict(slice lazybytes span))

-- =========================================================================

decodeRecordNamed :: Text -> (a -> Int) -> Decoder s a -> Decoder s a
decodeRecordNamed name getRecordSize decode = do
  lenOrIndef <- decodeListLenOrIndef
  x <- decode
  case lenOrIndef of
    Just n -> matchSize name (getRecordSize x) n
    Nothing -> do
      isBreak <- decodeBreakOr
      unless isBreak $ error ("decodng "++ show name ++ "Excess terms in array")
  pure x