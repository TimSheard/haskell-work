{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ConstrainedClassMethods  #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module IncrementalMap where

import Data.Kind(Type)
import Data.Map(Map)
import Data.Map.Internal (Map (..))
import qualified Data.Map as Map
import Data.Set(Set)
import qualified Data.Set as Set

import Test.Tasty
import Test.Tasty.QuickCheck
import Debug.Trace
import Cardano.Binary(ToCBOR,fromCBOR)
import Shelley.Spec.Ledger.Serialization()

-- =======================================

-- | A type t has an incremental lambda calulus instance
class ILC t where
  type D t :: Type
  plus :: t -> D t -> t
  extend:: D t -> D t -> D t
  zero :: D t
  propZero:: (Show t,Eq t) => t -> Property
  propZero x = (plus @t) x (zero @t) === x
  propExtend :: (Show t,Eq t) => t -> D t -> D t -> Property
  propExtend x dx2 dx1 = (plus @t) x (extend @t dx2 dx1) === plus (x `plus` dx1) dx2
  plusUnary :: (ILC a, ILC b, Eq b, Show b) =>
           (a -> b) ->
           (a -> D a -> D b) ->
           a ->
           D a ->
           Property
  plusUnary f f' a da = f (plus a da) === plus (f a) (f' a da)
  plusBinary :: (ILC a, ILC b, ILC c, Eq c, Show c) =>
           (a -> b -> c) ->
           (a -> D a -> b -> D b -> D c) ->
           a ->
           D a ->
           b ->
           D b ->
           Property
  plusBinary f f' a da b db = f (plus a da) (plus b db) === plus (f a b) (f' a da b db)

-- ======================================

data VChange v = Omit | Edit v
  deriving (Show,Eq)

-- Composition, apply the operator on the right first
extendVChange :: VChange t -> VChange t -> VChange t
extendVChange Omit Omit = Omit
extendVChange Omit (Edit y) = Omit
extendVChange (Edit x) Omit  = Edit x
extendVChange (Edit x) (Edit y) = Edit x

plusVChange :: Ord k => Map k v -> k -> VChange v -> Map k v
plusVChange m k (Edit v) = Map.insert k v m
plusVChange m k Omit = Map.delete k m

plusMap :: Ord k => Map k v -> Map k (VChange v) -> Map k v
plusMap x dx = Map.foldlWithKey' plusVChange x dx

type Delta k v = Map k (VChange v)

instance (Show t, Show k,Ord k) =>
  ILC (Map k t)
  where
  type D(Map k t) = Map k (VChange t)
  plus x dx = plusMap x dx
  zero = Map.empty
  extend x y = (Map.unionWith extendVChange x y)

-- ======================================
-- insert on Maps with combining function

insert :: forall k v. Ord k => (v -> v -> v) -> k -> v -> Map k v -> Map k v
insert comb k v m = Map.insertWith comb k v m

insert' :: (Ord k) => (v -> v -> v) -> k -> v -> Map k v -> Delta k v -> Delta k v
insert' (|+|) k v1 m dm =
   case (Map.lookup k dm) of
      Just Omit -> (Map.insert k (Edit v1) dm)
      Just (Edit v3) -> (Map.insert k (Edit (v1 |+| v3)) dm)
      Nothing -> case Map.lookup k m of
                   Nothing -> (Map.insert k (Edit v1) dm)
                   Just v2 -> (Map.insert k (Edit (v1 |+| v2)) dm)

propI :: forall k v.
         (Show v, Eq v,Ord k, Show k) =>
         (v -> v -> v) -> k -> v -> Map k v -> Delta k v -> Property
propI comb k v = (plusUnary @(Map k v) (insert comb k v) (insert' comb k v))

-- =======================================
-- delete on maps

delete :: forall k v. Ord k => k -> Map k v -> Map k v
delete k m = Map.delete k m

delete' :: (Ord k) => k -> Map k v -> Delta k v -> Delta k v
delete' k m dm =
 case (Map.lookup k dm) of
     Just (Edit v2) -> (Map.insert k Omit dm)
     Just Omit -> dm
     Nothing ->
       case Map.lookup k m of
         Nothing -> dm
         Just v1 -> (Map.insert k Omit dm)

propD :: forall k v.
         (Show v, Eq v,Ord k, Show k) =>
          k -> Map k v -> Delta k v -> Property
propD k = (plusUnary @(Map k v) (delete k) (delete' k))

-- ==============================================
-- union on Map

-- Given (union M N) The effect of a change on M

changeOnM :: (Ord k) =>
     (v -> v -> v) -> Map k v -> Map k v -> Map k (VChange v) -> k -> VChange v -> Map k (VChange v)
changeOnM (|+|) m n ans k change=
   case (change,Map.lookup k m, Map.lookup k n) of
    (Omit   ,Nothing,Nothing) -> ans
    (Omit   ,Just v1,Nothing) -> Map.insert k Omit ans
    (Omit   ,Nothing,Just v2) -> ans
    (Omit   ,Just v1,Just v2) -> Map.insert k (Edit v2) ans

    (Edit v,Nothing,Nothing) -> Map.insert k (Edit v) ans
    (Edit v,Just v1,Nothing) -> Map.insert k (Edit v) ans
    (Edit v,Nothing,Just v2) -> Map.insert k (Edit (v |+| v2)) ans
    (Edit v,Just v1,Just v2) -> Map.insert k (Edit (v |+| v2)) ans


-- Given (union M N) The effect of a change on N in a monoidal interpretation

changeOnN :: (Ord k) =>
     (v -> v -> v) -> Map k v -> Map k v -> Map k (VChange v) -> k -> VChange v -> Map k (VChange v)
changeOnN (|+|) m n ans k change=
   case (change,Map.lookup k m, Map.lookup k n) of
    (Omit   ,Nothing,Nothing) -> ans
    (Omit   ,Just v1,Nothing) -> ans
    (Omit   ,Nothing,Just v2) -> Map.insert k Omit ans
    (Omit   ,Just v1,Just v2) -> Map.insert k (Edit v1) ans

    (Edit v,Nothing,Nothing) -> Map.insert k (Edit v) ans
    (Edit v,Just v1,Nothing) -> Map.insert k (Edit (v1 |+| v)) ans
    (Edit v,Nothing,Just v2) -> Map.insert k (Edit v) ans
    (Edit v,Just v1,Just v2) -> Map.insert k (Edit (v1 |+| v)) ans

-- Given (union M N) The effect of a change caused by interacting dm and dn

changeOnTwo :: (Ord k) =>
     (v -> v -> v) ->
     Map k v -> Map k v -> Map k (VChange v) ->
     k -> (VChange v,VChange v) -> Map k (VChange v)
changeOnTwo (|+|) m n ans k (ch1,ch2) =
  case (ch1,ch2) of
     (Omit, Omit)      -> Map.insert k Omit ans
     (Omit,Edit v2)    -> Map.insert k (Edit v2) ans
     (Edit v1,Omit)    -> Map.insert k (Edit v1) ans
     (Edit v1,Edit v2) -> Map.insert k (Edit (v1 |+| v2)) ans

-- To get union' we combine all three

union' :: Ord k => (v -> v -> v) ->
     Map k v -> Delta k v ->
     Map k v -> Delta k v ->
     Delta k v
union' (|+|) m dm n dn =
   inter3B (Map.empty) dm dn
          (changeOnM (|+|) m n)
          (changeOnTwo (|+|) m n)
          (changeOnN (|+|) m n)

propU :: forall k v.
         (Show v, Eq v,Ord k, Show k) =>
         (v -> v -> v) -> Map k v -> Delta k v -> Map k v -> Delta k v -> Property
propU comb = (plusBinary @(Map k v) (Map.unionWith comb) (union' comb))

-- ================================================
-- Map intersection

-- ==========================
-- Given (intersect M N) The effect of changes on both M and N

changeInterDm :: (Ord k) =>
     Map k v -> Map k u -> Map k (VChange v) -> k -> VChange v -> Map k (VChange v)
changeInterDm m n ans k change =
   case (change,Map.lookup k m, Map.lookup k n) of
    (Omit   ,Nothing,Nothing) -> ans
    (Omit   ,Just v1,Nothing) -> ans
    (Omit   ,Nothing,Just v3) -> ans
    (Omit   ,Just v2,Just v3) -> Map.insert k Omit ans

    (Edit v1,Nothing,Nothing) -> ans
    (Edit v1,Just v2,Nothing) -> ans
    (Edit v1,Nothing,Just v3) -> Map.insert k (Edit v1) ans
    (Edit v1,Just v2,Just v3) -> Map.insert k (Edit v1) ans

-- Note because of the way intersection (Map k V -> Map k U -> Mapk V)
-- We have to transform individual changes on U, into changes on V
changeInterDn :: (Ord k) =>
   Map k v -> Map k u -> Map k (VChange v) -> k -> VChange u -> Map k (VChange v)
changeInterDn m n ans k change =
   case (change,Map.lookup k m, Map.lookup k n) of
    (Omit   ,Nothing,Nothing) -> ans
    (Omit   ,Just v1,Nothing) -> ans
    (Omit   ,Nothing,Just v3) -> ans
    (Omit   ,Just v2,Just v3) -> Map.insert k Omit ans

    (Edit v1,Nothing,Nothing) -> ans
    (Edit v1,Just v2,Nothing) -> Map.insert k (Edit v2) ans
    (Edit v1,Nothing,Just v3) -> ans
    (Edit v1,Just v2,Just v3) -> ans

changeInterDmDn :: Ord k =>
   Map k v -> Map k u -> Map k (VChange v) -> k -> (VChange v, VChange u) -> Map k (VChange v)
changeInterDmDn m n ans k (ch1,ch2) =
   case (ch1,ch2,Map.lookup k m, Map.lookup k n) of
     (Omit,_,_,_) -> Map.insert k Omit ans

     (Edit v1,Omit,Just _,_) -> Map.insert k Omit ans
     (Edit v1,Omit,Nothing,_) -> ans
     (Edit v1,Edit _,_,_) -> Map.insert k (Edit v1) ans

intersect' :: Ord k => Map k v -> Delta k v -> Map k u -> Delta k u -> Delta k v
intersect' m dm n dn =
   inter3B Map.empty dm dn (changeInterDm m n) (changeInterDmDn m n) (changeInterDn m n)

propInter :: forall k v.
         (Show v, Eq v,Ord k, Show k) =>
          Map k v -> Map k v -> Delta k v -> Delta k v -> Property
propInter m n dm dn = (plusBinary @(Map k v) Map.intersection intersect') m dm n dn


-- ==============================================

tests = testGroup "Incremental lambda caculus"
    [ testGroup "Helper functions are correct" [testProperty "inter3 is correct" splitprop]
    , testGroup "Operations on (Map k t)"
       [ testProperty "propZero Map" (propZero @(Map Int Int))
       , testProperty "propExtend Map" (propExtend @(Map Int Int))
       , testProperty "insert (+)" (propI @Int @Int (+))
       , testProperty "insert (\\ l r -> l)" (propI @Int @Int (\ l r -> l))
       , testProperty "insert (++)" (propI @Int @[Int] (++))
       , testProperty "delete" (propD @Int @Int)
       , testProperty "union (+)" (propU @Int @Int (+))
       , testProperty "union (\\ l r -> l)" (propU @Int @Int (\ l r -> l))
       , testProperty "union (\\ l r -> r)" (propU @Int @Int (\ l r -> r))
       , testProperty "union (++)" (propU @Int @[Int] (++))
       , testProperty "intersection" (propInter @Int @Int)
       ]
    ]

test = defaultMain tests




-- =======================================
-- helpful functions

plistf :: (a -> String) -> String -> [a] -> String -> String -> String
plistf f open xs sep close = open ++ help xs ++ close
  where help [] = ""
        help [x] = f x
        help (x:xs) = f x ++ sep ++ help xs

pair :: (Show a1, Show a2) => (a1, a2) -> [Char]
pair (x,y) = "("++show x++","++show y++")"

showmap :: (Show a1, Show a2) => String -> Map a1 a2 -> String
showmap x xs = plistf pair  ("("++x++"[") (Map.toList xs) "," "])"

showset :: Show a => String -> Set a -> String
showset x xs = plistf show  ("("++x++"[") (Set.toList xs) "," "])"

fromList :: Ord k => [(k,v)] -> Map.Map k v
fromList = Map.fromList
-- =======================================
-- Break 2 Maps: M and N, into 3 parts (a,b,c)
-- a has the keys only in M.
-- b has keys common to M and N.
-- c has keys ony in N.

-- ========================================

inter3 :: Ord k =>
     (a,b,c) -> Map k u -> Map k v -> (a -> k -> u -> a) ->
     (b -> k -> (u,v) -> b) -> (c -> k -> v -> c) -> (a,b,c)
inter3 triple m n c1 c2 c3 = go triple m n
  where go triple Tip Tip = triple
        go (a1,a2,a3) m Tip = (Map.foldlWithKey' c1 a1 m,a2,a3)
        go (a1,a2,a3) Tip n = (a1,a2,Map.foldlWithKey' c3 a3 n)
        go (a1,a2,a3) (Bin _ kx x l r) n = case Map.splitLookup kx n of
           (ln,Nothing,rn) -> go (go (c1 a1 kx x,a2,a3) l ln) r rn
           (ln,Just y,rn) -> go (go (a1,c2 a2 kx (x,y),a3) l ln) r rn

inter3B :: Ord k =>
     a -> Map k u -> Map k v ->
     (a -> k -> u -> a) ->
     (a -> k -> (u,v) -> a) ->
     (a -> k -> v -> a) -> a
inter3B ans m n c1 c2 c3 = go ans m n
  where go ans Tip Tip = ans
        go ans m Tip = (Map.foldlWithKey' c1 ans m)
        go ans Tip n = (Map.foldlWithKey' c3 ans n)
        go ans (Bin _ kx x l r) n = case Map.splitLookup kx n of
           (ln,Nothing,rn) -> go (go (c1 ans kx x) l ln) r rn
           (ln,Just y,rn) -> go (go (c2 ans kx (x,y)) l ln) r rn


splitprop :: Map Int Int -> Map Int Int -> Bool
splitprop m n =
   let (aset,bset,cset) = inter3B (Map.empty,Map.empty,Map.empty) m n cons1 cons2 cons3
       insert k v ans = Map.insert k v ans
       cons1 (a,b,c) k v = (insert k v a,b,c)
       cons2 (a,b,c) k v = (a, insert k v b,c)
       cons3 (a,b,c) k v = (a,b,insert k v c)
   in Set.unions [Map.keysSet aset,Map.keysSet bset,Map.keysSet cset] ==
        Set.union (Map.keysSet m) (Map.keysSet n) &&
      Map.union aset (Map.map fst bset) == m &&
      Map.union  cset (Map.map snd bset) == n &&
      Map.disjoint aset bset &&
      Map.disjoint aset cset &&
      Map.disjoint bset cset


splitp = defaultMain (testProperty "inter3 is correct" splitprop)


-- ===================================================
-- Arbitrary instances

instance Arbitrary v => Arbitrary (VChange v) where
  arbitrary = frequency [(1, Edit <$> arbitrary),
                         (1,pure Omit)
                         ]
  shrink Omit = []
  shrink (Edit x) = [ Edit i | i <- shrink x ]

{-
instance (Ord k,Arbitrary k, Arbitrary v) => Arbitrary (Delta k v) where
  arbitrary = Delta <$> arbitrary
  shrink (Delta m) = [ Delta i | i <- shrink m ]
-}