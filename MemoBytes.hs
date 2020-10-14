{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}

-- | MemoBytes is an abstration for a datetype that encodes its own seriialization.
--   The idea is to use a newtype around a MemoBytes non-memoizing version.
--   For example:   newtype Foo = Foo(MemoBytes NonMemoizingFoo)
--   This way all the instances for Foo (Eq,Show,Ord,ToCBOR,FromCBOR,NoThunks,Generic)
--   can be derived for free.
module Shelley.Spec.Ledger.MemoBytes
  ( MemoBytes (..),
    Encode(..),
    Decode(..),
    (!>),
    (<!),
    Mem,
    encode,
    decode,
    memoBytes,
    shorten,
    decodeList,
    decodeSeq,
    decodeStrictSeq,
    decodeSet,
    encodeList,
    encodeSeq,
    encodeStrictSeq,
    encodeSet,
    showMemo,
    printMemo,
  )
where

import Cardano.Binary
  ( Annotator (..),
    FromCBOR (fromCBOR),
    ToCBOR (toCBOR),
    encodeListLen,
    encodePreEncoded,
    encodeWord,
    withSlice,
  )
import Codec.CBOR.Encoding (Encoding)
import Codec.CBOR.Write (toLazyByteString)
import Data.ByteString.Lazy (toStrict)
import qualified Data.ByteString.Lazy as Lazy
import Data.ByteString.Short (ShortByteString, fromShort, toShort)
import Data.Sequence (Seq)
import Data.Sequence.Strict (StrictSeq)
import Data.Set (Set)
import Data.Typeable
import GHC.Generics (Generic)
import NoThunks.Class (AllowThunksIn (..), NoThunks (..))
import Shelley.Spec.Ledger.Serialization
  ( decodeList,
    decodeSeq,
    decodeSet,
    decodeStrictSeq,
    encodeFoldable,
    decodeRecordSum,
  )
import Prelude hiding (span)
import Codec.CBOR.Decoding(Decoder)
import Shelley.Spec.Ledger.BaseTypes (invalidKey)

-- ========================================================================

data MemoBytes t = Memo {memotype :: !t, memobytes :: {-# UNPACK #-} !ShortByteString}
  deriving (NoThunks) via AllowThunksIn '["memobytes"] (MemoBytes t)

deriving instance Generic (MemoBytes t)

instance (Typeable t) => ToCBOR (MemoBytes t) where
  toCBOR (Memo _ bytes) = encodePreEncoded (fromShort bytes)

instance (Typeable t, FromCBOR (Annotator t)) => FromCBOR (Annotator (MemoBytes t)) where
  fromCBOR = do
    (Annotator getT, Annotator getBytes) <- withSlice fromCBOR
    pure (Annotator (\fullbytes -> Memo (getT fullbytes) (toShort (toStrict (getBytes fullbytes)))))

instance Eq t => Eq (MemoBytes t) where (Memo x _) == (Memo y _) = x == y

instance Show t => Show (MemoBytes t) where show (Memo y _) = show y

instance Ord t => Ord (MemoBytes t) where compare (Memo x _) (Memo y _) = compare x y

shorten :: Lazy.ByteString -> ShortByteString
shorten x = toShort (toStrict x)

-- | Useful when deriving FromCBOR(Annotator T)
-- deriving via (Mem T) instance (Era era) => FromCBOR (Annotator T)
type Mem t = Annotator (MemoBytes t)

showMemo :: Show t => MemoBytes t -> String
showMemo (Memo t b) = "(Memo " ++ show t ++ "  " ++ show b ++ ")"

printMemo :: Show t => MemoBytes t -> IO ()
printMemo x = putStrLn (showMemo x)

-- ===============================================================================
-- Encode and Decode are typed data structures which specify encoders and decoders.
-- The types keep one from making mistakes, and count the correct number fields
-- in an encoding and decoding. They are somewhat dual, and are designed that visual
-- inspection of a Encode and its dual Decode can help the user conclude that the
-- two are self-consistent. They are also reusable abstractions that can be defined
-- once, and then used many places.
--
-- (Encode t) is a data structure from which 3 things can be recovered
-- Given:    x :: Encode t
-- 1) get a value of type t
-- 2) get an Encoding for that value, which correctly encodes the number of "fields"
--    written to the ByteString. Care must still be taken that the tags are correct.
-- 3) get a (MemoBytes t)
-- The advantage of using Encode with a MemoBytes, is we don't have to make a ToCBOR
-- instance. Instead the "instance" is spread amongst the pattern constuctors by using
-- (memoBytes encoding) in the where clause of the pattern contructor.
-- See some examples in the EXAMPLE Section below.
--
-- (Decode t) is dual to (Encode t). A decoder can be extracted from it. And it will
-- consistently decode it's dual.
-- ========================================================

data Encode t where
  Sum:: t -> Word -> Encode t
  Rec:: t -> Encode t
  ApplyE:: Encode(a -> t) -> Encode a -> Encode t
  To:: ToCBOR a => a -> Encode a
  E:: (t -> Encoding) -> t -> Encode t

infixl 4 !>
(!>) :: Encode(a -> t) -> Encode a -> Encode t
x !> y = ApplyE x y

runE :: Encode t -> t
runE (Sum c _) = c
runE (Rec c) = c
runE (ApplyE f x) = runE f (runE x)
runE (To x) = x
runE (E _ x) = x

gsize:: Encode t -> Word
gsize (Sum _ _) = 0
gsize (Rec _) = 0
gsize (To _) = 1
gsize (E _ _) = 1
gsize (ApplyE f x) = gsize f + gsize x

encode :: Encode t -> Encoding
encode sym = encodeHelp 0 sym  where
   encodeHelp :: Word -> Encode t -> Encoding
   encodeHelp n (Sum constr tag) = encodeListLen (n+1) <> encodeWord tag
   encodeHelp n (Rec constr) = encodeListLen n
   encodeHelp n (To x) = toCBOR x
   encodeHelp n (E encode x) = encode x
   encodeHelp n (ApplyE f x) = encodeHelp (n + gsize x) f <> encodeGroup x

   encodeGroup :: Encode t -> Encoding
   encodeGroup (Sum _ _) = error ("Never use a Sum type in a group")
   encodeGroup (Rec _) = mempty
   encodeGroup (To x) = toCBOR x
   encodeGroup (E encode x) = encode x
   encodeGroup (ApplyE f x) = encodeGroup f <> encodeGroup x

memoBytes :: Encode t -> MemoBytes t
memoBytes t = Memo (runE t) (shorten (toLazyByteString (encode t)))


-- =====================

data Decode t where
  SumD :: t -> Decode t
  RecD :: t -> Decode t
  From :: FromCBOR t => Decode t
  D :: (forall s . Decoder s t) -> Decode t
  ApplyD::  Decode (a -> t) -> Decode a -> Decode t
  Invalid:: Word -> Decode t

infixl 4 <!
(<!) :: Decode(a -> t) -> Decode a -> Decode t
x <! y = ApplyD x y

decode :: Decode t -> Decoder s (Int,t)
decode (SumD c) = pure (2,c)
decode (RecD c) = pure (1,c)
decode From = do { x <- fromCBOR; pure(1,x)}
decode (D decoder) = do { x <- decoder; pure(1,x)}
decode (ApplyD c group) = do { (n,f) <- decode c; (m,y) <- decode group; pure(n+m,f y)}
decode (Invalid k) = invalidKey k


-- ===========================================================================================
-- These functions are the dual analogs to
-- Shelley.Spec.Ledger.Serialization(decodeList, decodeSeq, decodeStrictSeq, decodeSet)
-- It is not well documented how to use encodeFoldable.
-- They are provided here as compatible pairs for use with the (E x) and (D x) constructors
-- of the Encode and Decode types. (E encodeList xs) and (D (decodeList fromCBOR)) should be duals.

encodeList :: ToCBOR a => [a] -> Encoding
encodeList = encodeFoldable

encodeStrictSeq :: ToCBOR a => StrictSeq a -> Encoding
encodeStrictSeq = encodeFoldable

encodeSeq :: ToCBOR a => Seq a -> Encoding
encodeSeq = encodeFoldable

encodeSet :: ToCBOR a => Set a -> Encoding
encodeSet = encodeFoldable

-- ===========================================
-- For a worked out EXAMPLE see the testfile:
-- cardano-ledger-specs/shelley/chain-and-ledger/shelley-spec-ledger-test/test/Test/Shelley/Spec/Ledger/MemoBytes.hs

-- ===================================
-- Examples

data Two = Two Int Bool

decTwo :: Decode Two
encTwo :: Two -> Encode Two

decTwo           = (RecD Two <! From <! From)
encTwo (Two a b) = (Rec Two  !> To a !> To b)

instance ToCBOR Two where
  toCBOR two = encode $ encTwo two

instance FromCBOR Two where
  fromCBOR = fmap snd (decode decTwo)

-- ============

data Test = Test Int Two Integer

decTestWithGroupForTwo :: Decode Test
encTestWithGroupForTwo :: Test -> Encode Test

decTestWithGroupForTwo =              (RecD Test <! From <! decTwo   <! From)
encTestWithGroupForTwo (Test a b c) = (Rec Test  !> To a !> encTwo b !> To c)

instance ToCBOR Test where
  toCBOR = encode . encTestWithGroupForTwo

instance FromCBOR Test where
  fromCBOR = fmap snd (decode decTestWithGroupForTwo)

-- ===========

data Three = A Int | B Bool Integer | F Two

decThree :: Word -> Decoder s (Int, Three)
decThree 0 = decode (SumD A <! From)
decThree 1 = decode (SumD B <! From <! From)
decThree 2 = decode (SumD F <! decTwo)
decThree k = decode $ Invalid k

encThree :: Three -> Encode Three
encThree (A x)   = (Sum A 0) !> To x
encThree (B b i) = (Sum B 1) !> To b !> To i
encThree (F t)   = (Sum F 2) !> encTwo t

instance FromCBOR Three where
   fromCBOR = decodeRecordSum "Three" decThree

instance ToCBOR Three where
   toCBOR x = encode (encThree x)