{-# LANGUAGE Rank2Types, FlexibleContexts, UndecidableInstances, TypeFamilies #-}
{-# LANGUAGE ConstraintKinds, KindSignatures, PolyKinds, TypeOperators #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}

module Reflect where
import Data.Proxy
import Data.Monoid
import Data.Reflection
import Data.Constraint
import Data.Constraint.Unsafe
import Data.Typeable
import Data.Semigroup

--------------------------------------------------------------------------------
-- Lift/ReifiableConstraint machinery.

newtype Lift (p :: * -> Constraint) (a :: *) (s :: *) = Lift { lower :: a }

class ReifiableConstraint p where
  data Def (p :: * -> Constraint) (a :: *) :: *
  reifiedIns :: Reifies s (Def p a) :- p (Lift p a s)
  extract :: proxy p -> (forall a. p a => Def p a)
  methods :: proxy p -> [String]

with :: Def p a -> (forall s. Reifies s (Def p a) => Lift p a s) -> a
with d v = reify d (lower . asProxyOf v)
  where
    asProxyOf :: f s -> Proxy s -> f s
    asProxyOf x _ = x

-- ========================================================
-- Given: (ReifiableConstraint m) instance.
-- We can build a Show instance for every (Def m a) type

instance(Typeable m,Typeable t,ReifiableConstraint m) => Show (Def m t) where
   show x = plistf id (name++"{ ") ms ", " " } :: Def " ++ name ++ tt
     where mproxy =  (Proxy :: Proxy m)
           name = show(typeRep mproxy)
           ms = methods mproxy
           tt = " "++show(typeRep (Proxy :: Proxy t))

plistf :: (a -> String) -> String -> [a] -> String -> String -> String
plistf f open xs sep close = open ++ help xs ++ close
  where help [] = ""
        help [x] = f x
        help (x:xs) = f x ++ sep ++ help xs

--------------------------------------------------------------------------------
-- Kicking it up to over 9000

using :: forall p a. ReifiableConstraint p => Def p a -> (p a => a) -> a
using d m = reify d $ \(_ :: Proxy s) ->
  let replaceProof :: Reifies s (Def p a) :- p a
      replaceProof = trans proof reifiedIns
        where proof = unsafeCoerceConstraint :: p (Lift p a s) :- p a
  in m \\ replaceProof

using2 :: forall p a. (ReifiableConstraint p) => (p a => a) -> Def p a -> a
using2 action def = using def action

registry_component = using2 @ Monoid (mappend mempty mempty)

--------------------------------------------------------------------------------
-- Examples of `ReifiableConstraint`
-- In general we would like to use Template Haskell to generate
-- both new class instances, and the proxy value.
-- $(modularize 'Eq)

-- ==========
instance ReifiableConstraint Eq where
  data Def Eq a = Eq { eq_ :: a -> a -> Bool }
  reifiedIns = Sub Dict
  extract p = Eq (==)
  methods p = [ "eq_" ]

instance Reifies s (Def Eq a) => Eq (Lift Eq a s) where
  a == b = eq_ (reflect a) (lower a) (lower b)

eqProxy :: Proxy Eq
eqProxy = Proxy

-- ===========
instance ReifiableConstraint Ord where
  data Def Ord a = Ord { compare_ :: a -> a -> Ordering }
  reifiedIns = Sub Dict
  extract p = Ord compare
  methods p = [ "compare_"]

-- We need an Eq(Lift Ord a s)instance to get an Ord(Lift Ord a s) instance
instance Reifies s (Def Ord a) => Eq (Lift Ord a s) where
  a == b = (compare a b == EQ)

instance Reifies s (Def Ord a) => Ord (Lift Ord a s) where
  compare a b = compare_ (reflect a) (lower a) (lower b)

ordProxy :: Proxy Ord
ordProxy = Proxy

-- =============

instance ReifiableConstraint Monoid where
  data Def Monoid a = Monoid { mappend_ :: a -> a -> a, mempty_ :: a }
  reifiedIns = Sub Dict
  extract p = Monoid mappend mempty
  methods p = [ "mappend_","mempty_"]

-- since Monoid requires a Semigroup instance
instance Reifies s (Def Monoid a) => Semigroup (Lift Monoid a s) where
  a <> b        = Lift $ mappend_ (reflect a) (lower a) (lower b)

instance Reifies s (Def Monoid a) => Monoid (Lift Monoid a s) where
  mappend a b        = Lift $ mappend_ (reflect a) (lower a) (lower b)
  mempty = a where a = Lift $ mempty_ (reflect a)

monoidProxy :: Proxy Monoid
monoidProxy = Proxy

{-
instance HasDict (Monoid x) (Def Monoid x) where
  evidence (Monoid _ _) = Dict
-}

-- ==========================================
-- My additions and experiments

-- An addition,
-- Some experiments

{-
class Foo t where ..

$(modularize 'Foo)

[d| instance ReifiableConstraint $( ) where
  data Def $( ) $( ) = $(_)
  reifiedIns = Sub Dict
|]
-}


-- /show

main :: IO ()
main = return ()


newtype Magic a r = Magic (forall (s :: *). Reifies s a => Proxy s -> r)

w :: Num n => n -> n
w = (\ n -> n + 3)

newtype Magic2 c a r = Magic2 (c a => r)

ex3 :: Magic2 Num n (n -> n)
ex3 = Magic2 w


data Tx c v = Tx
data Delta c v = Delta Int deriving Eq

data Gen x = Gen x
instance Functor Gen
instance Applicative Gen
instance Monad Gen


genNextDelta :: Tx c v -> Delta c v -> Gen (Delta c v)
genNextDelta tx delta = undefined

getDelta :: Tx c v -> Gen (Delta c v)
getDelta tx = fix (genNextDelta tx) (Delta 0)

applyDelta :: Tx c v -> Delta c v -> Tx c v
applyDelta tx delta = undefined

fix :: (Eq d,Monad m) => (d ->  m d) -> d -> m d
fix f d = do { d1 <- f d; if d1==d then pure d else fix f d1 }

converge :: Tx c v -> Gen (Tx c v)
converge tx = do
  delta <- getDelta tx
  pure(applyDelta tx delta)
