{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE  FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE  UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}


module SumProd
  where

import Data.Kind(Type)

-- =========================================
-- An Index into an N-ary structure.

data Ix (t::Type) (r::[Type]) where
  Z :: Ix t (t : r)
  S :: Ix t r -> Ix t (s : r)

-- A few small Ix
i0 :: Ix t (t : r)
i0 = Z
i1 :: Ix t (s : t : r)
i1 = S i0
i2 :: Ix t (s1 : s2 : t : r)
i2 = S i1
i3 :: Ix t (s1 : s2 : s3 : t : r)
i3 = S i2
i4 :: Ix t (s : s1 : s2 : s3 : t : r)
i4 = S i3
i5 :: Ix t (s1 : s2 : s3 : s4 : s5 : t : r)
i5 = S i4
i6 :: Ix t (s1 : s2 : s3 : s4 : s5 : s6 : t : r)
i6 = S i5

-- ============================
-- N-ary Products

data Id x = Id x

data Prod (f :: Type -> Type) (r :: [Type]) where
  N :: Prod f '[]
  PCons :: (f t) -> Prod f r -> Prod f (t ': r)

infixr 5 #
(#) :: t -> Prod Id r -> Prod Id (t ': r)
x # xs = PCons (Id x) xs

p1 :: Prod Id '[String, Int, Char]
p1 = ("abc" # 5 # 'c' # N)

infixr 5 !
(!) :: f t -> Prod f r -> Prod f (t ': r)
x ! xs = PCons x xs

p2 :: Prod [] '[Char, Integer, Bool]
p2 = ("abc" ! [5] ! [True,False] ! N)

proj :: Ix t r -> Prod f r -> f t
proj Z (PCons x _) = x
proj (S n) (PCons _ xs) = proj n xs

-- ===============================
-- N-ary Sums

data Sum (r :: [Type]) where
  Inject :: Ix t r -> t -> Sum r

extract :: Ix t r -> Sum r -> Maybe t
extract Z (Inject Z t) = Just t
extract (S n) (Inject (S m) t) = extract n (Inject m t)
extract _ _ = Nothing

s1 :: Sum (Bool : r)
s1 = Inject i0 True

s2 :: Sum (s1 : s2 : s3 : [Char] : r)
s2 = Inject i3 "abc"

-- =============================================
-- Splitting a list of Sum

class Split r where
  split :: [Sum r] -> Prod [] r -> Prod [] r

instance Split '[] where
  split [] ans = ans

instance Split r => Split (t : r) where
  split [] ans = ans
  split (Inject ix t : xs) ans = push ix t (split xs ans)

push :: Ix t r -> t -> Prod [] r -> Prod [] r
push Z t (PCons ts ys) = PCons (t:ts) ys
push (S n) t (PCons xs ys) = PCons xs (push n t ys)

ss :: [Sum (Int : Char : [Char] : r)]
ss = [ Inject Z (5::Int), Inject (S Z) 'c', Inject Z 3, Inject (S (S Z)) "abc"]

ans :: Prod [] '[Int, Char, [Char]]
ans = split ss (PCons [] (PCons [] (PCons [] N)))

-- ===========================================
-- Summary of a Type, encoding it as a Sum

class Summary t (r:: [Type]) where
  encode :: t -> Sum r
  decode :: Sum r -> t
  empty :: Prod [] r

instance Summary [a] '[(),(a,[a])] where
  encode [] = Inject Z ()
  encode (x : xs) = Inject (S Z) (x,xs)
  decode (Inject Z ()) = []
  decode (Inject (S Z) (x,xs)) = x : xs
  empty = [] ! [] ! N

data Timelock = Lock

data Script = Timelock Timelock | Plutus String

instance Summary Script '[Timelock,String] where
  encode (Timelock t) = Inject Z t
  encode (Plutus s) = Inject (S Z) s
  decode (Inject Z t) = Timelock t
  decode (Inject (S Z) s) = Plutus s
  empty = [] ! [] ! N

splitT :: forall r t. (Split r,Summary t r) => [t] -> Prod [] r
splitT xs = split (map encode xs) (empty @t @r)

-- ============================================

instance Show t => Show (Id t) where
  show(Id x) = show x

instance Show (Prod f '[]) where
  show (N) = ""

instance (Show (f t),Show (Prod f r)) => Show (Prod f (t ': r)) where
  show (PCons x xs) = show x ++ " " ++ show xs