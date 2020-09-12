{-# OPTIONS_GHC  -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}


{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances   #-}
{-# LANGUAGE GeneralizedNewtypeDeriving  #-}

module LazyEncoding where

import Control.Monad (unless)

import Data.ByteString(ByteString)
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

data Foo e = Foo Integer Text

instance Typeable e => ToCBOR (Foo e) where
  toCBOR (Foo n s) = encodeListLen 2 <> toCBOR n <> toCBOR s

instance Typeable e => FromCBOR (Foo e) where
  fromCBOR = decodeRecordNamed (fromString "Foo") (const 2) $ do
     n <- fromCBOR
     s <- fromCBOR
     pure $ Foo n s

-- ===========================================================
-- We can wrap any indexed type in a Lazy, And we need only
-- one instance each for ToCBOR and FromCBOR of Lazy

data Lazy f e = Lazy ByteString (f e)

instance (Typeable f,Typeable e) => ToCBOR (Lazy f e) where
  toCBOR (Lazy bytes f) = encodePreEncoded bytes

instance (Typeable f,Typeable e,ToCBOR (f e),FromCBOR(f e)) => FromCBOR (Lazy f e) where
  fromCBOR = do
     fe <- fromCBOR
     let encoding = toCBOR fe                  -- we do this just once at construction time
         bytes = toStrictByteString encoding
     pure (Lazy bytes fe)

-- ========================================================
-- Wrap anything in a newtype can be derived automatically

newtype Bar e = Bar (Lazy Foo e)
  deriving (ToCBOR,FromCBOR)

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