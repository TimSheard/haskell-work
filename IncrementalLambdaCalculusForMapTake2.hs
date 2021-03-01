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
{-# LANGUAGE FlexibleContexts #-}
-- {-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

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
import Control.Monad.State(State,modify,get,put,runState)
import Data.Semigroup
import Data.Monoid

-- =======================================

-- | A type t has an incremental lambda calulus instance
class ILC t where
  data Diff t :: Type
  applyDiff :: t -> Diff t -> t
  extend:: Diff t -> Diff t -> Diff t
  zero :: Diff t
  propZero:: (Show t,Eq t) => t -> Property
  propZero x = (applyDiff @t) x (zero @t) === x
  propExtend :: (Show t,Eq t) => t -> Diff t -> Diff t -> Property
  propExtend x dx2 dx1 = (applyDiff @t) x (extend @t dx2 dx1) === applyDiff (x `applyDiff` dx1) dx2
  plusUnary :: (ILC a, ILC b, Eq b, Show b) =>
           (a -> b) ->
           (a -> Diff a -> Diff b) ->
           a ->
           Diff a ->
           Property
  plusUnary f f' a da = f (applyDiff a da) === applyDiff (f a) (f' a da)
  plusBinary :: forall a b c. (ILC a, ILC b, ILC c, Eq c, Show c) =>
           (a -> b -> c) ->
           (a -> Diff a -> b -> Diff b -> Diff c) ->
           a ->
           Diff a ->
           b ->
           Diff b ->
           Property
  plusBinary f f' a da b db = f (applyDiff a da) (applyDiff b db) === applyDiff (f a b) (f' a da b db)

-- It is much better to add the Monoid instance, rather than requiring it as a
-- precondition to ILC, because we only need to write one instance here, and
-- never again.

-- | Every (Diff t) is a Semigroup
instance ILC t => Semigroup (Diff t)
  where x <> y = extend x y

-- | Every (Diff t) is a Monoid
instance ILC t => Monoid (Diff t)
  where mempty = zero

-- ========================================================
-- We construct a (Diff (Map k t)) from (Map k (MChange t))

type Delta k v = Diff(Map k v)

data MChange v = Omit | Edit v
  deriving (Show,Eq)

-- Composition, apply the operator on the right first
extendMChange :: MChange t -> MChange t -> MChange t
extendMChange Omit Omit = Omit
extendMChange Omit (Edit y) = Omit
extendMChange (Edit x) Omit  = Edit x
extendMChange (Edit x) (Edit y) = Edit x

plusMChange :: Ord k => Map k v -> k -> MChange v -> Map k v
plusMChange m k (Edit v) = Map.insert k v m
plusMChange m k Omit = Map.delete k m

plusMap :: Ord k => Map k v -> Delta k v -> Map k v
plusMap x (DM dx) = Map.foldlWithKey' plusMChange x dx

instance (Show t, Show k,Ord k) =>
  ILC (Map k t)
  where
  newtype Diff(Map k t) = DM (Map k (MChange t)) deriving Show
  applyDiff x dx = plusMap x dx
  zero = DM Map.empty
  extend (DM x) (DM y) = DM (Map.unionWith extendMChange x y)

-- ======================================
-- insert on Maps with combining function

insert :: forall k v. Ord k => (v -> v -> v) -> k -> v -> Map k v -> Map k v
insert comb k v m = Map.insertWith comb k v m

insert' :: (Ord k) => (v -> v -> v) -> k -> v -> Map k v -> Delta k v -> Delta k v
insert' (|+|) k v1 m (DM dm) = DM $
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
delete' k m (DM dm) = DM $
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
     (v -> v -> v) -> Map k v -> Map k v -> Map k (MChange v) -> k -> MChange v -> Map k (MChange v)
changeOnM (|+|) m n ans k Omit =
   case Map.lookup k m of
     Nothing -> ans
     Just v1 ->
       case Map.lookup k n of
         Nothing -> Map.insert k Omit ans
         Just v2 -> Map.insert k (Edit v2) ans
changeOnM (|+|) m n ans k (Edit v) =
   case Map.lookup k n of
      Nothing -> Map.insert k (Edit v) ans
      Just v2 -> Map.insert k (Edit (v |+| v2)) ans

-- Given (union M N) The effect of a change on N

changeOnN :: (Ord k) =>
     (v -> v -> v) -> Map k v -> Map k v -> Map k (MChange v) -> k -> MChange v -> Map k (MChange v)
changeOnN (|+|) m n ans k Omit =
  case Map.lookup k n of
    Nothing -> ans
    Just v2 ->
      case Map.lookup k m of
        Nothing -> Map.insert k Omit ans
        Just v1 -> Map.insert k (Edit v1) ans
changeOnN (|+|) m n ans k (Edit v) =
  case Map.lookup k m of
    Nothing -> Map.insert k (Edit v) ans
    Just v1 -> Map.insert k (Edit (v1 |+| v)) ans

-- Given (union M N) The effect of a change caused by interacting dm and dn

changeOnTwo :: (Ord k) =>
     (v -> v -> v) ->
     Map k v -> Map k v -> Map k (MChange v) ->
     k -> (MChange v,MChange v) -> Map k (MChange v)
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
union' (|+|) m (DM dm) n (DM dn) = DM $
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
     Map k v -> Map k u -> Map k (MChange v) -> k -> MChange v -> Map k (MChange v)
changeInterDm m n ans k Omit =
   case Map.lookup k n of
     Nothing -> ans
     Just v3 -> Map.insert k Omit ans
changeInterDm m n ans k (Edit v1) =
   case Map.lookup k n of
      Nothing -> ans
      Just v3 -> Map.insert k (Edit v1) ans


-- Note because of the way intersection (Map k V -> Map k U -> Mapk V)
-- We have to transform individual changes on U, into changes on V
changeInterDn :: (Ord k) =>
   Map k v -> Map k u -> Map k (MChange v) -> k -> MChange u -> Map k (MChange v)
changeInterDn m n ans k Omit =
  case Map.lookup k n of
    Nothing ->  ans
    Just v3 -> case Map.lookup k m of {Nothing -> ans; Just v2 -> Map.insert k Omit ans}
changeInterDn m n ans k (Edit v1) =
  case Map.lookup k m of
    Nothing -> ans
    Just v2 -> case Map.lookup k n of {Nothing -> Map.insert k (Edit v2) ans; Just _ -> ans}

changeInterDmDn :: Ord k =>
   Map k v -> Map k u -> Map k (MChange v) -> k -> (MChange v, MChange u) -> Map k (MChange v)
changeInterDmDn m n ans k (ch1,ch2) =
   case (ch1,ch2) of
     (Omit,_) -> Map.insert k Omit ans
     (_,Omit) -> Map.insert k Omit ans
     (Edit v1,Edit v2) -> Map.insert k (Edit v1) ans


intersect' :: Ord k => Map k v -> Delta k v -> Map k u -> Delta k u -> Delta k v
intersect' m (DM dm) n (DM dn) = DM $
   inter3B Map.empty dm dn (changeInterDm m n) (changeInterDmDn m n) (changeInterDn m n)

propInter :: forall k v.
         (Show v, Eq v,Ord k, Show k) =>
          Map k v -> Map k v -> Delta k v -> Delta k v -> Property
propInter m n dm dn = (plusBinary @(Map k v) Map.intersection intersect') m dm n dn


-- ==========================================
-- intersection with combining function
-- The effect of changes on both M and N

changeInterWDm :: (Ord k) => (v -> u -> w) ->
     Map k v -> Map k u -> Map k (MChange w) -> k -> MChange v -> Map k (MChange w)
changeInterWDm (|+|) m n ans k Omit =
   case Map.lookup k n of
     Nothing -> ans
     Just v3 -> Map.insert k Omit ans
changeInterWDm (|+|) m n ans k (Edit v1) =
   case Map.lookup k n of
      Nothing -> ans
      Just v3 -> Map.insert k (Edit (v1 |+| v3)) ans

changeInterWDn :: (Ord k) =>  (v -> u -> w) ->
   Map k v -> Map k u -> Map k (MChange w) -> k -> MChange u -> Map k (MChange w)
changeInterWDn (|+|) m n ans k change =
   case Map.lookup k m of
     Nothing -> ans
     Just v2 ->
       case change of
         Edit v1 -> Map.insert k (Edit (v2 |+| v1)) ans
         Omit ->
            case Map.lookup k n of
              Nothing -> ans
              Just v3 -> Map.insert k Omit ans

changeInterWDmDn :: Ord k => (v -> u -> w) ->
   Map k v -> Map k u -> Map k (MChange w) -> k -> (MChange v, MChange u) -> Map k (MChange w)
changeInterWDmDn (|+|) m n ans k (ch1,ch2) =
   case (ch1,ch2,Map.lookup k m, Map.lookup k n) of
     (Omit,_,_,_) -> Map.insert k Omit ans
     (Edit v1,Edit v2,_,_) -> Map.insert k (Edit (v1 |+| v2)) ans
     (Edit v1,Omit,Just _,_) -> Map.insert k Omit ans
     (Edit v1,Omit,Nothing,_) -> ans

intersectWith' :: forall v u w k. Ord k =>
    (v -> u -> w) -> Map k v -> Delta k v -> Map k u -> Delta k u -> Delta k w
intersectWith' f m (DM dm) n (DM dn) = DM $
   inter3B Map.empty dm dn (changeInterWDm f m n) (changeInterWDmDn f m n) (changeInterWDn f m n)

propInterW
  :: forall k a b w. (Ord k,Show k,Show a, Show b, Show w, Eq w) =>
     (a -> b -> w)
     -> Map k a
     -> Map k b
     -> Diff (Map k a)
     -> Diff (Map k b)
     -> Property
propInterW f m n dm dn =
    (plusBinary @(Map k w) @(Map k a) @(Map k b)
                (Map.intersectionWith f) (intersectWith' f)) m dm n dn

-- =========================================
-- Map filter with key

mfilter' :: Ord k => (k -> v -> Bool) -> Map k v -> Delta k v -> Delta k v
mfilter' p m (DM dm) = DM (Map.foldlWithKey' accum Map.empty dm)
  where accum ans k v =
          case (v,Map.lookup k m) of
            (Edit v1,Just v2) ->
               if p k v1
                  then Map.insert k (Edit v1) ans
                  else Map.insert k Omit ans
            (Edit v1,Nothing) -> if p k v1 then Map.insert k (Edit v1) ans else ans
            (Omit,Just v2) -> Map.insert k Omit ans
            (Omit,Nothing) -> ans

mfilter :: (k -> a -> Bool) -> Map k a -> Map k a
mfilter = Map.filterWithKey

propF :: forall k v. (Show v, Eq v, Show k, Ord k) => (k -> v -> Bool) -> Map k v -> Delta k v -> Property
propF f = (plusUnary @(Map k v) (mfilter f) (mfilter' f))


-- ==============================================
-- mapWithKey

mmap' :: Ord k => (k -> a -> b) -> Map k a -> Delta k a -> Delta k b
mmap' p m (DM dm) = DM (Map.foldlWithKey' accum Map.empty dm)
  where accum ans k (Edit v1) =  Map.insert k (Edit (p k v1)) ans
        accum ans k Omit =
          case Map.lookup k m of
            (Just v2) -> Map.insert k Omit ans
            (Nothing) -> ans

mmap :: (k -> a -> b) -> Map k a -> Map k b
mmap = Map.mapWithKey

propM :: forall k v u.
  (Show v, Show u, Eq u, Show k, Ord k)
  =>
  (k -> v -> u) -> Map k v -> Delta k v -> Property
propM f = (plusUnary @(Map k v) (mmap f) (mmap' f))

-- ========================================

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
       , testProperty "intersectionWith (+)" (propInterW @Int @Int @Int (+))
       , testProperty "intersectionWith (++)" (propInterW @[Int] @[Int] @[Int] (++))
       , testProperty "intersectionWith (max)" (propInterW @[Int] @[Int] @[Int] (max))
       , testProperty "intersectionWith (\\ x y -> if x then y else 99)"
                      (propInterW @Int @Bool @Int (\ x y -> if x then y else 99))
       , testProperty "filterWithKey (==)" (propF @Int @Int (\ k v -> k==v))
       , testProperty "filterWithKey (\\ k v -> True)" (propF @Int @Int (\ k v -> True))
       , testProperty "filterWithKey (\\ k v -> False)" (propF @Int @Int (\ k v -> False))
       , testProperty "filterWithKey (const even)" (propF @Int @Int (const even))
       , testProperty "mapWithKey (+)" (propM @Int @Int (+))
       , testProperty "mapWithKey (==)" (propM @Int @Int (==))
       , testProperty "mapWithKey (\\ k v -> v+3)" (propM @Int @Int (\ k v -> v+3))
       ]
    , testGroup "Incremental Models"
       [ testProperty "action1 computes the same value as action2" propActionValue
       , testProperty "action1 computes the same state as action2" propActionState
       , testProperty "action1 computes the same value as action3" propActionValue3
       , testProperty "action1 computes the same state as action3" propActionState3
       ]
    ]

test = defaultMain tests

-- ========================================================
-- State helper function

asks :: (state -> a) -> State state a
asks f = do { st <- get; pure(f st) }

-- ======================================
-- A simple Model of the Ledger state

data NonInc a b = NonInc { a:: a, b:: b }
type Store1 = NonInc (Map Int Int) (Map Int Int)

modifyA :: (a -> a) -> State (NonInc a b) ()
modifyA f = modify(\ (NonInc a b) -> NonInc (f a) b)

getA :: State (NonInc a b) a
getA = asks a

modifyB :: (b -> b) -> State (NonInc a b) ()
modifyB f = modify(\ (NonInc a b) -> NonInc a (f b))

getB :: State (NonInc a b) b
getB = asks b

getview :: (a -> b -> c) -> State (NonInc a b) c
getview f = do (NonInc a b) <- get; pure(f a b)

left l r = l

-- ============================================
-- A corresponding Incremental Model of the Ledger State

data Inc view a b = (ILC view,ILC a,ILC b) =>
     Inc { view :: view
         , ai :: a
         , da :: (Diff a)
         , bi :: b
         , db :: (Diff b) }

initialize :: forall a b view. (ILC view, ILC a, ILC b) => (a -> b -> view) -> a -> b -> Inc view a b
initialize f a b = Inc (f a b) a (zero @a) b (zero @b)

increment:: forall a b view. (a -> Diff a -> b -> Diff b -> Diff view) -> Inc view a b -> Inc view a b
increment f' (Inc view a da b db) =
   (Inc (applyDiff view (f' a da b db)) (applyDiff a da) (zero @a) (applyDiff b db) (zero @b))

modifyAi :: (a -> Diff a -> Diff a) -> State (Inc view a b) ()
modifyAi f' = modify(\ (Inc view a da b db) -> Inc view a (f' a da) b db)

getAi :: State (Inc view a b) a
getAi = do (Inc _ a da _ _) <- get;  pure (applyDiff a da)

modifyBi :: (b -> Diff b -> Diff b) -> State (Inc view a b) ()
modifyBi f' = modify(\ (Inc view a da b db) -> Inc view a da b (f' b db))

getBi :: State (Inc view a b) b
getBi = do (Inc _ _ _ b db) <- get;  pure (applyDiff b db)

getviewi :: (a -> Diff a -> b -> Diff b -> Diff view) -> State (Inc view a b) view
getviewi f' = do modify (increment f'); asks view

-- ========================================================================
-- A third model where every update cause an immediate recalculation of the view.

data IM view a b = (ILC view,ILC a,ILC b) =>
     IM { viewj :: view
         , aj :: a
         , bj :: b }

-- we assume the view is the intersection

modifyAj :: (Ord k) =>
            (Map k t -> Delta k t -> Delta k t) -> State (IM (Map k t) (Map k t) (Map k s)) ()
modifyAj f' = modify (\ (IM v aa bb) ->
                        let  da = f' aa zero
                        in IM (applyDiff v (intersect' aa da bb zero))
                              (applyDiff aa da) bb)

modifyBj :: (Ord k) =>
            (Map k s -> Delta k s -> Delta k s) -> State (IM (Map k t) (Map k t) (Map k s)) ()
modifyBj f' = modify (\ (IM v aa bb) ->
                        let  db  = f' bb zero
                        in IM (applyDiff v (intersect' aa zero bb db))
                              aa (applyDiff bb db))

getAj = asks aj
getBj = asks bj
getviewj = asks viewj

-- ==============================================
-- Tests of the models


action1 :: State Store1 (Map Int Int)
action1 = do
  modifyA (insert left 3 20)
  modifyA (delete 2)
  modifyB (insert left 3 8)
  getview (Map.intersection)

type Store2 = Inc (Map Int Int) (Map Int Int) (Map Int Int)

action2:: State Store2 (Map Int Int)
action2 = do
  modifyAi (insert' left 3 20)
  modifyAi (delete' 2)
  modifyBi (insert' left 3 8)
  getviewi intersect'

type Store3  = (IM (Map Int Int) (Map Int Int) (Map Int Int))

action3:: State Store3 (Map Int Int)
action3 = do
  modifyAj (insert' left 3 20)
  modifyAj (delete' 2)
  modifyBj (insert' left 3 8)
  getviewj

propActionValue a b =
    let (viewa,statea) = runState action1 (NonInc a b)
        (viewb,stateb) = runState action2 (initialize (Map.intersection) a b)
    in viewa === viewb

propActionState a b =
    let (viewa,NonInc a1 b1) = runState action1 (NonInc a b)
        (viewb,Inc _ a2 _ b2 _) = runState action2 (initialize (Map.intersection) a b)
    in (a1==a2) && (b1==b2)

propActionValue3 a b =
    let (viewa,statea) = runState action1 (NonInc a b)
        (viewb,stateb) = runState action3 (IM (Map.intersection a b) a b)
    in viewa === viewb

propActionState3 a b =
    let (viewa,NonInc a1 b1) = runState action1 (NonInc a b)
        (viewb,IM _ a2 b2) = runState action3 (IM (Map.intersection a b) a b)
    in (a1==a2) && (b1==b2)

-- ==============================================
-- computing Big O cost models

log2 :: Int -> Int
log2 n | n <= 2 = 1
log2 n = 1 + log2 ((n+1) `div` 2)

intersectO m n | m <= n = m * log2((n `div` m) + 1)
intersectO m n = intersectO n m

intersect'O m n d = d * ((log2 m) `div` 4)

plusO m d = d * (log2 m)

compareO m n d = (simple, incremental, speedup, show(60 / speedup)++" seconds")
  where simple = intersectO m n + (plusO m d)
        incremental =  intersect'O m n d + plusO n d
        speedup = fromIntegral simple / fromIntegral incremental
cs = [ compareO m 10000 20 | m <- [1000, 10000, 100000, 1000000, 10000000]]



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

instance Arbitrary v => Arbitrary (MChange v) where
  arbitrary = frequency [(1, Edit <$> arbitrary),
                         (1,pure Omit)
                         ]
  shrink Omit = []
  shrink (Edit x) = [ Edit i | i <- shrink x ]


instance (Ord k,Arbitrary k, Arbitrary v) => Arbitrary (Delta k v) where
  arbitrary = DM <$> arbitrary
  shrink (DM m) = [ DM i | i <- shrink m ]


{-
foo = testGroup "insert tests"
 [ testProperty "insert (+)" (propI @Int @Int (+))
 , testProperty "insert (\\ l r -> l)" (propI @Int @Int (\ l r -> l))
 , testProperty "insert (++)" (propI @Int @[Int] (++))
 ]
-}