{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE FlexibleInstances          #-}

module MultiAsset where

import Data.Map.Strict(Map)
import qualified Data.Map as Map
import Data.Map.Internal(Map(..),balanceL,balanceR,singleton,link,splitLookup,link2)

data Op = Gt | Lt | Gteq | Lteq | Neq | Equal

class Val t where
  vzero :: t                    -- This is an identity of vplus
  vplus :: t -> t -> t          -- This must be associative and commutative
  vnegate:: t -> t              -- vplus x (vnegate x) == vzero
  vscale:: Integer -> t -> t    --
  voper:: Op -> t -> t -> Bool  -- This will define a PARTIAL order using pointwise comparisons (If all the keys don't match returns False)
  visZero:: t -> Bool           -- is the argument vzero?

vminus x y = vplus x (vnegate y)

class Default f t where
  apply:: Ord k => f k t -> k -> t

instance Val Integer where
  vzero = 0
  vplus x y = x+y
  vnegate x = -x
  vscale n x = n * x
  voper Gt x y = x>y
  voper Lt x y = x<y
  voper Gteq x y = x >= y
  voper Lteq x y = x <= y
  voper Neq x y = not(x==y)
  voper Equal x y = x==y
  visZero x = x==0

instance Val t => Default Map t where
   apply map k = case Map.lookup k map of { Just t -> t; Nothing -> vzero }

instance (Ord k,Val t) => Val (Map k t) where
  vzero = Map.empty
  vplus x y = unionWithV vplus x y  -- There is an assumption that if the range is vzero, it is not stored in the Map
  vnegate x = mapV vnegate x        -- We enforce this by using our own versions of map and union: unionWithV and mapV
  vscale n x = mapV (vscale n) x
  voper op x y = pointWise (voper op) x y
  visZero x = Map.null x

newtype Quantity = Quantity {unInt :: Integer} deriving (Show,Eq,Ord,Val)

data PolicyID crypto = PolicyID String deriving (Show,Eq,Ord)
data AssetID = AssetID String deriving (Show,Eq,Ord)

newtype Value crypto = Value { val :: Map  (PolicyID crypto) (Map AssetID Quantity) }
  deriving (Show,Val)

vinsert:: PolicyID c -> AssetID -> Quantity -> Value c -> Value c
vinsert pid aid q old = vplus old (Value (Map.singleton pid (Map.singleton aid q)))

-- ====================================================================

pointWise:: Ord k => (v -> v -> Bool) -> Map k v -> Map k v -> Bool
pointWise p Tip Tip = True
pointWise p Tip (Bin _ k _ ls rs) = False
pointWise p (Bin _ k _ ls rs) Tip = False
pointWise p m (Bin _ k v2 ls rs) =
   case Map.splitLookup k m of
      (lm,Just v1,rm) -> p v1 v2 && pointWise p ls lm && pointWise p rs rm
      other -> False

-- The following functions enforce the invariant that vzero is never stored in a Map

insertWithV :: (Ord k,Val a) => (a -> a -> a) -> k -> a -> Map k a -> Map k a
insertWithV = go
  where
    go :: (Ord k,Val a) => (a -> a -> a) -> k -> a -> Map k a -> Map k a
    go _ !kx x Tip = if visZero x then Tip else singleton kx x
    go f !kx x (Bin sy ky y l r) =
        case compare kx ky of
            LT -> balanceL ky y (go f kx x l) r
            GT -> balanceR ky y l (go f kx x r)
            EQ -> if visZero new then link2 l r else Bin sy kx new l r
               where new = f x y
{-# INLINABLE insertWithV #-}

unionWithV :: (Ord k,Val a) => (a -> a -> a) -> Map k a -> Map k a -> Map k a
unionWithV _f t1 Tip = t1
unionWithV f t1 (Bin _ k x Tip Tip) = insertWithV f k x t1
unionWithV f (Bin _ k x Tip Tip) t2 = insertWithV f k x t2
unionWithV _f Tip t2 = t2
unionWithV f (Bin _ k1 x1 l1 r1) t2 = case splitLookup k1 t2 of
  (l2, mb, r2) -> case mb of
      Nothing -> if visZero x1 then link2 l1l2 r1r2 else link k1 x1 l1l2 r1r2
      Just x2 -> if visZero new then link2 l1l2 r1r2 else link k1 new l1l2 r1r2
        where new = (f x1 x2)
    where !l1l2 = unionWithV f l1 l2
          !r1r2 = unionWithV f r1 r2
{-# INLINABLE unionWithV #-}

mapV:: (Ord k,Val a) => (a -> a) -> Map k a -> Map k a
mapV f m = Map.foldrWithKey accum Map.empty m
   where accum k v ans = if visZero new then ans else Map.insert k new ans
            where new = f v
{-# INLINABLE mapV #-}