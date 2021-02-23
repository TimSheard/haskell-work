{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE BangPatterns #-}

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
  type Extra t :: Type
  plus :: Extra t -> t -> D t -> t
  zero :: t -> D t

instance (Show t, Show k,Ord k) => ILC (Map k t) where
  type D(Map k t) = Delta k t
  type Extra(Map k t) = ()
  -- we assume the (Delta m) is much smaller than 'x'
  plus () x dx = plusMap x dx
  zero t = Delta Map.empty

-- ====================================================
-- Here is an interpretation of a single VChange as a
-- change on a Map. Add applies only if the key is not there.
-- Edit applies only if the key is there. We can implement
-- this efficiently using the function Map.alter
-- alter :: Ord k => (Maybe a -> Maybe a) -> k -> Map k a -> Map k a

data VChange v = Add v | Omit | Edit v
  deriving (Show,Eq)

delta :: Ord k => [(k,VChange t)] -> Delta k t
delta xs = Delta (Map.fromList xs)

plusVChange :: Ord k => Map k v -> k -> VChange v -> Map k v
plusVChange m k change = Map.alter (f change) k m
  where f Omit _ = Nothing                 -- Always Omit (delete) this key
        f (Add v) (Just v2) = Just v2      -- Add v only if it is NOT there
        f (Add v) Nothing = Just v         -- otherwise its the identity
        f (Edit v) Nothing = Nothing       -- Edit using the new v only if it IS there
        f (Edit v) (Just _) = Just v       -- otherwise it is the identity

-- | A Delta is just a Map of VChange, Tells how the value at each key can change.
newtype Delta k v = Delta {uD :: Map k (VChange v) }
  deriving (Eq)

instance (Show k, Show t) => Show (Delta k t) where
   show (Delta m) = showmap "delta" m

-- |  Plus for maps with (left) monoid (<>)
plusMap :: Ord k => Map k v -> Delta k v -> Map k v
plusMap x (Delta dx) = Map.foldlWithKey' plusVChange x dx

-- ================================================================================
-- Given a Map M, the effect of a single insertion (in an intrepretation (|+|) )

insert' :: (Monoid v,Ord k) => k -> v -> Map k v -> Delta k v -> Delta k v
insert' k v1 m delta = insertPrime (<>) k v1 m delta

insertPrime :: (Ord k) => (v -> v -> v) -> k -> v -> Map k v -> Delta k v -> Delta k v
insertPrime (|+|) k v1 m (Delta dm) =
   case (Map.lookup k m,Map.lookup k dm) of
     (Nothing,Nothing) -> Delta(Map.insert k (Add v1) dm)
     (Just v2,Nothing) -> Delta(Map.insert k (Edit (v1 |+| v2)) dm)

     (Nothing,Just Omit)      -> Delta(Map.insert k (Add v1) dm)
     (Nothing,Just (Edit v3)) -> Delta(Map.insert k (Add v1) dm)
     (Nothing,Just (Add v3))  -> Delta(Map.insert k (Add (v1 |+| v3)) dm)

     (Just v2,Just Omit)      -> Delta(Map.insert k (Edit v1) dm)
     (Just v2,Just (Edit v3)) -> Delta(Map.insert k (Edit (v1 |+| v3)) dm)
     (Just v2,Just (Add v3))  -> Delta(Map.insert k (Edit (v1 |+| v2)) dm)


prop3 :: forall k v. (Monoid v,Show v, Show k,Eq v,Ord k) => k -> v -> Map k v -> Delta k v -> Property
prop3 k v m dm = counterexample (show3 (<>) k v m dm) $
                 Map.insertWith (<>) k v (plusMap m dm) ===
                 plusMap m (insert' k v m dm)


propPlus :: forall k v. (Show v, Show k,Eq v,Ord k) => (v -> v -> v) -> k -> v -> Map k v -> Delta k v -> Property
propPlus plus k v m dm = counterexample (show3 plus k v m dm) $
                 Map.insertWith plus k v (plusMap m dm) ===
                 plusMap m (insertPrime plus k v m dm)


show3 :: forall k v. (Show v, Show k,Eq v,Ord k) => (v -> v -> v) -> k -> v -> Map k v -> Delta k v -> String
show3 (|+|) k v m dm =  unlines
  ["k = "++show k
  ,"v = "++show v
  ,"m = "++show m
  ,"dm = "++show dm
  ,"plusMap m dm =\n   "++show(plusMap m dm)
  ,"Map.lookup k m = "++show(Map.lookup k m)
  ,"Map.lookup k dm = "++show(Map.lookup k (uD dm))
  ,"Map.insertWith (|+|) k v (plusMap m dm) =\n   "++show(Map.insertWith (|+|) k v (plusMap m dm))
  ,"NEED TO "++show m++"  ==>  "++show(Map.insertWith (|+|) k v (plusMap m dm))
  ,"insertPrime (|+|) k v m dm =\n   "++show(insertPrime (|+|) k v m dm)
  , show $ Map.insertWith (|+|) k v (plusMap m dm) == plusMap m (insertPrime (|+|) k v m dm)
  ]

fix3 = putStrLn $ show3 (<>) k v m dm where
   k = -4
   v = [1]
   m = fromList []
   dm = (delta[(-4,Add [3])])

-- ================================================================================
-- Given a Map M, the effect of a single delete (in a monoidal intrepretation)

delete' :: (Monoid v,Ord k) => k -> Map k v -> Delta k v -> Delta k v
delete' k m (Delta dm) =
   case (Map.lookup k m,Map.lookup k dm) of
     (Nothing,Nothing) -> Delta(dm)
     (Just v1,Nothing) -> Delta(Map.insert k Omit dm)

     (Nothing,Just Omit)      -> Delta(dm)
     (Nothing,Just (Edit v2)) -> Delta(dm)
     (Nothing,Just (Add v2))  -> Delta(Map.insert k Omit dm)

     (Just v1,Just Omit)      -> Delta(dm)
     (Just v1,Just (Edit v2)) -> Delta(Map.insert k Omit dm)
     (Just v1,Just (Add v2))  -> Delta(Map.insert k Omit dm)

prop4 :: forall k v. (Monoid v,Show v, Show k,Eq v,Ord k) => k -> Map k v -> Delta k v -> Property
prop4 k m dm = counterexample (show4 k m dm) $
                 Map.delete k (plusMap m dm) ===
                 plusMap m (delete' k m dm)


show4 :: forall k v. (Monoid v,Show v, Show k,Eq v,Ord k) => k -> Map k v -> Delta k v -> String
show4 k m dm =  unlines
  ["k = "++show k
  ,"m = "++show m
  ,"dm = "++show dm
  ,"plusMap m dm =\n   "++show(plusMap m dm)
  ,"Map.lookup k m = "++show(Map.lookup k m)
  ,"Map.lookup k dm = "++show(Map.lookup k (uD dm))
  ,"Map.delete k (plusMap m dm) =\n   "++show(Map.delete k (plusMap m dm))
  ,"NEED TO "++show m++"  ==>  "++show(Map.delete k (plusMap m dm))
  ,"delete' k m dm =\n   "++show(delete' k m dm)
  , show $ Map.delete k (plusMap m dm) == plusMap m (delete' k m dm)
  ]

fix4 = putStrLn $ show4 k m dm where
   k = 3
   m = fromList ([]::[(Int,[Int])])
   dm = (delta[(3,Edit [2])])



-- ==============
-- Given (union M N) The effect of a change on M in a monoidal interpretation

changeOnM :: (Ord k) =>
     (v -> v -> v) -> Map k v -> Map k v -> Map k (VChange v) -> k -> VChange v -> Map k (VChange v)
changeOnM (|+|) m n ans k change=
   case (change,Map.lookup k m, Map.lookup k n) of
    (Omit   ,Nothing,Nothing) -> ans
    (Omit   ,Just v1,Nothing) -> Map.insert k Omit ans
    (Omit   ,Nothing,Just v2) -> ans
    (Omit   ,Just v1,Just v2) -> Map.insert k (Edit v2) ans

    (Add v ,Nothing,Nothing) -> Map.insert k (Add v) ans
    (Add v ,Just v1,Nothing) -> ans
    (Add v ,Nothing,Just v2) -> Map.insert k (Edit (v |+| v2)) ans
    (Add v ,Just v1,Just v2) -> ans

    (Edit v,Nothing,Nothing) -> Map.insert k (Edit v) ans
    (Edit v,Just v1,Nothing) -> Map.insert k (Edit v) ans
    (Edit v,Nothing,Just v2) -> ans
    (Edit v,Just v1,Just v2) -> Map.insert k (Edit (v |+| v2)) ans

-- ==============
-- Given (union M N) The effect of a change on N in a monoidal interpretation

changeOnN :: (Ord k) =>
     (v -> v -> v) -> Map k v -> Map k v -> Map k (VChange v) -> k -> VChange v -> Map k (VChange v)
changeOnN (|+|) m n ans k change=
   case (change,Map.lookup k m, Map.lookup k n) of
    (Omit   ,Nothing,Nothing) -> ans
    (Omit   ,Just v1,Nothing) -> ans
    (Omit   ,Nothing,Just v2) -> Map.insert k Omit ans
    (Omit   ,Just v1,Just v2) -> Map.insert k (Edit v1) ans

    (Add v ,Nothing,Nothing) -> Map.insert k (Add v) ans
    (Add v ,Just v1,Nothing) -> Map.insert k (Edit (v1 |+| v)) ans  -- Note switched from (v <> v1) changeOnM
    (Add v ,Nothing,Just v2) -> ans
    (Add v ,Just v1,Just v2) -> ans

    (Edit v,Nothing,Nothing) -> Map.insert k (Edit v) ans
    (Edit v,Just v1,Nothing) -> ans
    (Edit v,Nothing,Just v2) -> Map.insert k (Edit v) ans
    (Edit v,Just v1,Just v2) -> Map.insert k (Edit (v1 |+| v)) ans


-- ==============
-- Given (union M N) The effect of a change caused by interacting dm and dn

changeOnTwo :: (Ord k) =>
     (v -> v -> v) -> Map k v -> Map k v -> Map k (VChange v) -> k -> (VChange v,VChange v) -> Map k (VChange v)
changeOnTwo (|+|) m n ans k (ch1,ch2) =
   case (ch1,ch2,Map.lookup k m, Map.lookup k n) of
     (Omit, Omit, _, _) -> Map.insert k Omit ans

     (Omit,Add v2,Nothing,Nothing) -> Map.insert k (Add v2) ans
     (Omit,Add v2,Just v3,Nothing) -> Map.insert k (Edit v2) ans
     (Omit,Add v2,Nothing,Just v4) -> Map.insert k (Add v2) ans
     (Omit,Add v2,Just v3,Just v4) -> Map.insert k (Edit v4) ans

     (Omit,Edit v2,Nothing,Nothing) -> ans
     (Omit,Edit v2,Just v3,Nothing) -> Map.insert k Omit ans -- Map.insert k (Edit v2) ans
     (Omit,Edit v2,Nothing,Just v4) -> Map.insert k (Edit v2) ans
     (Omit,Edit v2,Just v3,Just v4) -> Map.insert k (Edit v2) ans

     (Add v1,Omit,Nothing,Nothing) -> Map.insert k (Add v1) ans
     (Add v1,Omit,Just v3,Nothing) -> Map.insert k (Edit v3) ans
     (Add v1,Omit,Nothing,Just v4) -> Map.insert k (Edit v1) ans
     (Add v1,Omit,Just v3,Just v4) -> Map.insert k (Edit v3) ans

     (Add v1,Edit v2,Nothing,Nothing) -> Map.insert k (Add v1) ans
     (Add v1,Edit v2,Just v3,Nothing) -> ans
     (Add v1,Edit v2,Nothing,Just v4) -> Map.insert k (Edit (v1 |+| v2)) ans
     (Add v1,Edit v2,Just v3,Just v4) -> Map.insert k (Edit (v3 |+| v2)) ans


     (Add v1,Add v2,Nothing,Nothing) -> Map.insert k (Add (v1 |+| v2)) ans
     (Add v1,Add v2,Just v3,Nothing) -> Map.insert k (Edit (v3 |+| v2)) ans
     (Add v1,Add v2,Nothing,Just v3) -> Map.insert k (Edit (v1 |+| v3)) ans
     (Add v1,Add v2,Just v3,Just v4) -> ans

     (Edit v1,Add v2,Nothing,Nothing) -> Map.insert k (Add v2) ans
     (Edit v1,Add v2,Just v3,Nothing) -> Map.insert k (Edit (v1 |+| v2)) ans
     (Edit v1,Add v2,Nothing,Just v4) -> ans
     (Edit v1,Add v2,Just v3,Just v4) -> Map.insert k (Edit (v1 |+| v4)) ans

     (Edit v1,Omit,Nothing,Nothing) -> ans
     (Edit v1,Omit,Just v3,Nothing) -> Map.insert k (Edit v1) ans
     (Edit v1,Omit,Nothing,Just v4) -> Map.insert k Omit ans
     (Edit v1,Omit,Just v3,Just v4) -> Map.insert k (Edit v1) ans

     (Edit v1,Edit v2,Nothing,Nothing) -> Map.insert k (Edit v2) ans
     (Edit v1,Edit v2,Just v3,Nothing) -> Map.insert k (Edit v1) ans
     (Edit v1,Edit v2,Nothing,Just v4) -> Map.insert k (Edit v2) ans
     (Edit v1,Edit v2,Just v3,Just v4) -> Map.insert k (Edit (v1 |+| v2)) ans

unionTrip
  :: (Ord k) =>
     (v -> v -> v)
     -> Map k v
     -> Map k v
     -> Delta k v
     -> Delta k v
     -> (Map k (VChange v), Map k (VChange v), Map k (VChange v))

unionTrip (|+|) m n (Delta dm) (Delta dn) =
   inter3 (Map.empty,Map.empty,Map.empty) dm dn
          (changeOnM (|+|) m n)
          (changeOnTwo (|+|) m n)
          (changeOnN (|+|) m n)

union' :: (Ord k, Semigroup v) =>
          Map k v -> Delta k v -> Map k v -> Delta k v -> Delta k v
union' m dm n dn = unionPrime (<>) m dm n dn

unionPrime
  :: Ord k =>
     (v -> v -> v)
     -> Map k v -> Delta k v -> Map k v -> Delta k v -> Delta k v
unionPrime plus m dm n dn = Delta (Map.unions [a,b,c])
   where (a,b,c) = unionTrip plus m n dm dn

foo7 :: forall k v. (Ord k,Show k,Show v,Eq v,Monoid v) => Map k v -> Map k v -> Delta k v -> Delta k v -> Property
foo7 m n dm dn = counterexample (show7 m n dm dn) $
    (Map.unionWith (<>) (plusMap m dm) (plusMap n dn)) ===
    (plusMap (Map.unionWith (<>) m n) (union' m dm n dn))

unionPlus :: (Show k, Show v, Ord k, Eq v) => (v -> v -> v) ->
             Map k v -> Map k v -> Delta k v -> Delta k v -> Property
unionPlus plus m n dm dn =
    (Map.unionWith plus (plusMap m dm) (plusMap n dn)) ===
    (plusMap (Map.unionWith plus m n) (unionPrime plus m dm n dn))

show7:: (Show k, Show v, Ord k, Monoid v, Eq v) =>
        Map k v -> Map k v -> Delta k v -> Delta k v -> String
show7 m n dm dn = unlines
  ["m = "++show m
  ,"n = "++show n
  ,"dm = "++show dm
  ,"dn = "++show dn
  ,"deltaTrip m n dm dn =\n   "++show(unionTrip (<>) m n dm dn)
  ,"Map.unionWith (<>) m n =\n   "++show(Map.unionWith (<>) m n)
  ,"plusMap m dm =\n   "++show(plusMap m dm)
  ,"plusMap n dn =\n   "++show(plusMap n dn)
  ,"Map.unionWith (<>) (plusMap m dm) (plusMap n dn) =\n   "++show(Map.unionWith (<>) (plusMap m dm) (plusMap n dn))
  ,"NEEDED "++show(Map.unionWith (<>) m n)++"  ==>  "++show(Map.unionWith (<>) (plusMap m dm) (plusMap n dn))
  ,"union' m dm n dn =\n   "++show(union' m dm n dn)
  ,"plusMap (Map.unionWith (<>) m n) (union' m dm n dn) =\n   "++show(plusMap (Map.unionWith (<>) m n) (union' m dm n dn))
  ,show(plusMap (Map.unionWith (<>) m n) (union' m dm n dn) == Map.unionWith (<>) (plusMap m dm) (plusMap n dn))
  ]


-- ==========================
-- Given (intersect M N) The effect of changes on both M and N

changeInterDm :: (Ord k) =>
     Map k v -> Map k u -> Map k (VChange v) -> k -> VChange v -> Map k (VChange v)
changeInterDm m n ans k change =
   case (change,Map.lookup k m, Map.lookup k n) of
    (Omit   ,Nothing,Nothing) -> ans
    (Omit   ,Just v1,Nothing) -> ans --ok
    (Omit   ,Nothing,Just v3) -> ans
    (Omit   ,Just v2,Just v3) -> Map.insert k Omit ans

    (Add v1 ,Nothing,Nothing) -> ans
    (Add v1 ,Just v2,Nothing) -> ans
    (Add v1 ,Nothing,Just v3) -> Map.insert k (Add v1) ans
    (Add v1 ,Just v2,Just v3) -> ans

    (Edit v1,Nothing,Nothing) -> ans
    (Edit v1,Just v2,Nothing) -> ans
    (Edit v1,Nothing,Just v3) -> ans
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

    (Add v1 ,Nothing,Nothing) -> ans
    (Add v1 ,Just v2,Nothing) -> Map.insert k (Add v2) ans
    (Add v1 ,Nothing,Just v3) -> ans
    (Add v1 ,Just v2,Just v3) -> ans

    (Edit v1,Nothing,Nothing) -> ans  --Since in intersection we only look at the key in (Map k u)
    (Edit v1,Just v2,Nothing) -> ans  -- Its not surprising (Edit u) has no effect
    (Edit v1,Nothing,Just v3) -> ans
    (Edit v1,Just v2,Just v3) -> ans

changeInterDmDn :: Ord k =>
   Map k v -> Map k u -> Map k (VChange v) -> k -> (VChange v, VChange u) -> Map k (VChange v)
changeInterDmDn m n ans k (ch1,ch2) =
   case (ch1,ch2,Map.lookup k m, Map.lookup k n) of
     (Omit,_,_,_) -> Map.insert k Omit ans

     (Add v1,Omit,Just _,_) -> Map.insert k Omit ans
     (Add v1,Omit,Nothing,_) -> ans
     (Add v1,Add v2,Nothing,_) -> Map.insert k (Add v1) ans
     (Add v1,Add v2,Just v3,_) -> Map.insert k (Add v3) ans
     (Add v1,Edit v2,Just v3,_) -> ans
     (Add v1,Edit v2,Nothing,Just v4) -> Map.insert k (Add v1) ans
     (Add v1,Edit v2,Nothing,Nothing) -> ans

     (Edit v1,Omit,Just _,_) -> Map.insert k Omit ans
     (Edit v1,Omit,Nothing,_) -> ans
     (Edit v1,Add _,Just v3,Just _) -> Map.insert k (Edit v1) ans
     (Edit v1,Add _,Just v3,Nothing) -> Map.insert k (Add v1) ans
     (Edit v1,Add _,Nothing,_) -> ans
     (Edit v1,Edit _,_,_) -> Map.insert k (Edit v1) ans

intersect' :: Ord k => Map k v -> Delta k v -> Map k u -> Delta k u -> Delta k v
intersect' m (Delta dm) n (Delta dn) = Delta $
   inter3B Map.empty dm dn (changeInterDm m n) (changeInterDmDn m n) (changeInterDn m n)

prop10 :: forall k v u. (Show k, Show v, Show u, Ord k, Eq v) =>
     Map k v -> Map k u -> Delta k v -> Delta k u -> Property
prop10 m n dm dn = counterexample (show10 m n dm dn) $
                     Map.intersection (plusMap m dm) (plusMap n dn) ===
                     plusMap (Map.intersection m n) (intersect' m dm n dn)

go10 = defaultMain  (testProperty "prop10" (prop10 @Int @Int @Int))

fix = putStrLn $ show10 m n dm dn where
  m,n :: Map Int Int
  dm, dn :: Delta Int Int
  m = fromList [(-43,3)]
  n = fromList [(-43,4)]
  dm = (delta[(-43,Edit 1)])
  dn = (delta[(-43,Edit 2)])

show10:: (Show k, Show v, Show u, Ord k, Eq v) =>
        Map k v -> Map k u -> Delta k v -> Delta k u -> String
show10 m n dm dn = unlines
  ["m = "++show m
  ,"n = "++show n
  ,"dm = "++show dm
  ,"dn = "++show dn
  ,"Map.intersection m n =\n   "++show(Map.intersection m n)
  ,"plusMap m dm =\n   "++show(plusMap m dm)
  ,"plusMap n dn =\n   "++show(plusMap n dn)
  ,"Map.intersection (plusMap m dm) (plusMap n dn) =\n   "++show(Map.intersection (plusMap m dm) (plusMap n dn))
  ,"NEEDED "++show(Map.intersection m n)++"  ==>  "++show(Map.intersection (plusMap m dm) (plusMap n dn))
  ,"intersect' m dm n dn =\n   "++show(intersect' m dm n dn)
  ,"plusMap (Map.intersection m n) (intersect' m dm n dn) =\n   "++show(plusMap (Map.intersection m n) (intersect' m dm n dn))
  ,show(Map.intersection (plusMap m dm) (plusMap n dn) == plusMap (Map.intersection m n) (intersect' m dm n dn))
  ]


-- ========================================

-- filter' :: forall k v. (Show v,Show k,Ord k) => (v -> Bool) -> Map k v -> Delta k v -> Delta k v
filter' p m (Delta dm) = Delta (Map.foldlWithKey' accum Map.empty dm)
  where accum ans k v =
          case (v,Map.lookup k m) of
            (Add v1,Just v2) -> ans
            (Add v1,Nothing) -> if p v1 then Map.insert k (Add v1) ans else ans
            (Edit v1,Just v2) -> if p v1
                                    then (if p v2 then Map.insert k (Edit v1) ans else Map.insert k (Add v1) ans)
                                    else Map.insert k Omit ans
            (Edit v1,Nothing) -> ans
            (Omit,Just v2) -> Map.insert k Omit ans
            (Omit,Nothing) -> ans

prop11 :: (Show k, Show v, Ord k, Eq v) =>
       (v -> Bool) -> Map k v -> Delta k v -> Property
prop11 p m dm = counterexample (show11 p m dm) $
                Map.filter p (plusMap m dm) ===
                plusMap (Map.filter p m) (filter' p m dm)

show11 :: (Show k, Show v, Ord k,Eq v) =>
          (v -> Bool) -> Map k v -> Delta k v -> String
show11 p m dm = unlines
  ["m = "++show m
  ,"dm = "++show dm
  ,"plusMap m dm = "++show(plusMap m dm)
  ,"Map.filter p (plusMap m dm) = "++show(Map.filter p (plusMap m dm) )
  ,"NEED "++show(Map.filter p m)++"  =>  "++show(Map.filter p (plusMap m dm))
  ,"filter' p m dm = "++show(filter' p m dm)
  ,show(Map.filter p (plusMap m dm) == plusMap (Map.filter p m) (filter' p m dm))
  ]

fix11 = putStrLn (show11 even m dm) where
    m:: Map Int Int
    dm:: Delta Int Int
    m = fromList[(2,7)]
    dm = (delta[(2,Edit 0)])


go11 :: IO ()
go11 = defaultMain (testProperty "filter'" (prop11 @Int @Int even))

-- ========================================
tests :: TestTree
tests = testGroup "incremental calculus tests"
    [ testGroup "incremental Map tests"
        [ testProperty "inter3 is correct" splitprop
        , testProperty "insert' is derivative" (prop3 @Int @[Int])
        , testProperty "insertPrime (+) is derivative" (propPlus @Int @Int (+))
        , testProperty "insertPrime (\\ x y -> x) is derivative" (propPlus @Int @Int (\ x y -> x))
        , testProperty "insertPrime (\\ x y -> y) is derivative" (propPlus @Int @Int (\ x y -> y))
        , testProperty "insertPrime (\\ x y -> x <> y) is derivative" (propPlus @Int @[Int] (\ x y -> x <> y) )
        , testProperty "insertPrime (\\ x y -> y <> x) is derivative" (propPlus @Int @[Int] (\ x y -> y <> x) )
        , testProperty "delete' is derivative" (prop4 @Int @[Int])
        , testProperty "union' is derivative" (foo7 @Int @[Int])
        , testProperty "unionPrime (+) is derivative" (unionPlus @Int @Int (+))
        , testProperty "unionPrime (\\ x y -> x) is derivative" (unionPlus @Int @Int (\ x y -> x))
        , testProperty "unionPrime (\\ x y -> y) is derivative" (unionPlus @Int @Int (\ x y -> y))
        , testProperty "unionPrime (\\ x y -> x <> y) is derivative" (unionPlus @Int @[Int] (\ x y -> x <> y) )
        , testProperty "unionPrime (\\ x y -> y <> x) is derivative" (unionPlus @Int @[Int] (\ x y -> y <> x) )
        , testProperty "intersect' is derivative" (prop10 @Int @Int @Int)
        , testProperty "(filter' even) is derivative" (prop11 @Int @Int even)
        ]
    ]

test :: IO ()
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
   let (a,b,c) = inter3 ([],[],[]) m n cons cons cons
       keys xs = Set.fromList(map fst xs)
       aset = (Map.fromList a)
       bset = (Map.fromList b)
       cset = (Map.fromList c)
       cons ans k v = (k,v) : ans
   in Set.unions [keys a,keys b,keys c] == Set.union (Map.keysSet m) (Map.keysSet n) &&
      Map.union aset (Map.map fst bset) == m &&
      Map.union  cset (Map.map snd bset) == n &&
      Map.disjoint aset bset &&
      Map.disjoint aset cset &&
      Map.disjoint bset cset

splitp = defaultMain (testProperty "inter3 is correct" splitprop)

-- ===================================================
-- Arbitrary instances

instance Arbitrary v => Arbitrary (VChange v) where
  arbitrary = frequency [(1,Add <$> arbitrary),
                         (1, Edit <$> arbitrary),
                         (1,pure Omit)
                         ]
  shrink (Add x) = [ Add i | i <- shrink x ]
  shrink Omit = []
  shrink (Edit x) = [ Edit i | i <- shrink x ]

instance (Ord k,Arbitrary k, Arbitrary v) => Arbitrary (Delta k v) where
  arbitrary = Delta <$> arbitrary
  shrink (Delta m) = [ Delta i | i <- shrink m ]
