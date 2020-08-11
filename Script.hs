{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE  FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE DeriveTraversable  #-}

module Script where

import Data.Map(Map,singleton,insert)
import qualified Data.Map as Map


data Connect pred x = TT | FF | Pred pred | And [x] | Or [x] | Not x
   deriving (Eq,Show,Functor,Ord,Foldable,Traversable)

data Fix f = In (f (Fix f))

eval :: (pred -> Bool) -> Fix (Connect pred) -> Bool
eval run (In x) = reduce run (fmap (eval run) x)

reduce:: (pred -> Bool) -> Connect pred Bool -> Bool
reduce p TT = True
reduce p FF = False
reduce p (Pred x) = p x
reduce p (And xs) = and xs
reduce p (Or xs) = or xs
reduce p (Not x) = not x

-- ===========================================================
-- Constructing some examples

tt = In TT
ff = In FF
pr s = In(Pred s)
conj xs = In(And xs)
disj xs = In(Or xs)
neg x = In(Not x)

term1 = conj[pr "a",disj[pr "a",neg (pr "b"),ff],tt,pr "b"]

-- ==================================================
-- instances for (Fix (Connect p))

instance Eq p => Eq(Fix (Connect p)) where
  (In x) == (In y) = x==y

instance Show p => Show(Fix (Connect p)) where
  show (In x) = show x

-- =================================================
-- Common sub expressions

type Trip p = (Int,Map Int (Connect p Int),Map (Connect p Int) Int)

state0 :: Ord p => Trip p
state0 = (2,Map.fromList[(0,FF),(1,TT)],Map.fromList[(FF,0),(TT,1)])

find :: Ord p => Connect p Int -> State (Trip p) Int
find x = do
   (n,m1,m2) <- get
   case Map.lookup x m2 of
      Just n -> pure n
      Nothing -> do { put (n+1,insert n x m1,insert x n m2); pure n}

cse:: Ord p => Fix (Connect p) -> State (Trip p) Int
cse (In x) = do
   y <- mapM cse x
   find y

commonSubExp:: Ord p => Fix (Connect p) -> (Int, Map Int (Connect p Int))
commonSubExp x =
  case unState (cse x) state0 of
   ((_,m1,_),n) -> (n,m1)

-- ====================================================================
-- Evaluating using common sub expressions

run :: (pred -> Bool) -> Map Int Bool -> (Connect pred Int) -> Bool
run go m x = reduce go (fmap (m Map.!) x)

eval2 :: Ord pred => (env -> pred -> Bool) -> env -> Fix (Connect pred) -> Bool
eval2 go env term = m1 Map.! n
   where (n,m0) = commonSubExp term
         m1 = Map.map (run (go env) m1) m0  -- Note the recursion on m1
         -- This builds a Map with lazy thunks in the value field of the Map
         -- The function itself just looks up the answer from the map, and
         -- the thunks are evaluated on demand, and only once, no matter
         -- how many time the sub expression occurs.


-- ===================================================

unState (State f) = f
newtype State s a = State (s -> (s,a))
  deriving Functor

instance Applicative (State s) where
   pure a = State(\ s -> (s,a))
   f <*> x = do { g <- f; y <- x; pure(g y)}

instance Monad (State s) where
  return x = pure x
  (State f) >>= g = State next
    where next s = case f s of
                    (s',a) -> unState (g a) s'

get :: State p p
get = State (\ s -> (s,s))

put :: p -> State p ()
put a = State(\ s -> (a,()))

modify :: (p -> p) -> State p ()
modify f = State(\ s -> (f s,()))