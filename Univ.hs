{-# LANGUAGE
    RankNTypes,
    FlexibleInstances, FlexibleContexts,
    MultiParamTypeClasses, FunctionalDependencies,
    GADTs, DataKinds, PolyKinds, KindSignatures,
    ConstraintKinds
#-}


module Univ where

import Literal(Literal(..),Lit(..),evalLit)
import Control.Monad.Identity
import Data.Map.Strict(Map,toList)
import Data.Array
import Data.Set(Set)
import Unsafe.Coerce
import Control.Monad.State(State,runState,get,put,modify)

data Fix f = In (f (Fix f))

-- =====================================================================================
-- The Rep type itself, Any type: t, such that (Rep t) is inhabited is in the Universe.
-- =====================================================================================

data Rep:: * -> * where
 Int:: Rep Int
 Float:: Rep Float
 Double:: Rep Double
 Rational:: Rep Rational
 Integer:: Rep Integer
 Char:: Rep Char
 String:: Rep String
 Bool :: Rep Bool
 Unit :: Rep ()
 Dyn :: Rep Dyn
 List :: Rep a -> Rep[a]
 Array:: Rep key -> Rep val -> Rep(Array key val)
 Map:: Ord key => Rep key -> Rep val -> Rep(Map key val)
 Maybe:: Rep a -> Rep (Maybe a)
 Arrow:: Rep a -> Rep b -> Rep (a -> b)
 Either:: Rep a -> Rep b -> Rep (Either a b)
 Tuple:: Tup nest flat => List1 Rep nest -> Rep flat
 Rep:: Rep a -> Rep(Rep a)
 Prog:: Rep t -> Rep(Prog t)

-- ========================================================================
-- Every type: t, such that (Rep t) is inhabited has 4 Universal operations

class Univ t where
    toVal :: t -> Val
    fromVal:: Rep t -> Val -> Maybe t
    rep:: Rep t
    showU:: t -> String
    showU f = showR rep f

-- ===========================================================================
-- Every type in the Universe can be encoded "typelessly" in the type Val by
-- using the Universal operations 'toVal' and 'fromVal'. By pattern matching
-- on the embedded (Rep a) fields we can statically determine the type of
-- the data stored inside.

data Val where
   VLit:: Literal -> Val
   VConstant:: Maybe String -> Rep i -> i -> Val
   VList:: Rep a -> [a] -> Val
   VArray:: Rep i -> Rep t -> Array i t -> Val
   VMap:: Ord i => Rep i -> Rep t -> Map i t -> Val
   VMaybe:: Rep a -> Maybe a -> Val
   VArrow:: Rep a -> Rep b -> (a -> b) -> Val
   VEither:: Rep a -> Rep b -> (Either a b) -> Val
   VTuple:: Tup nest flat => Rep flat -> flat -> nest -> Val
   NTuple:: [Val] -> Val
   VRep:: Rep a -> Val
   VProg:: Rep a -> Prog a -> Val

-- ============================================================================
-- Every type in the Universe can be encoded as a Dyn. The difference between
-- 'Val' and 'Dyn' is that static type information is more "spread out" in 'Val'
-- distributed across many constructors, and some times several (Rep a) fields.
-- Both of these have uses.

data Dyn where
  Dynamic:: Rep i -> i -> Dyn

dyn:: Univ t => t -> Dyn
dyn x = Dynamic rep x

{-
data Value t where
  Value:: Rep i -> i -> Value i
-}

-- ==============================================================================
-- Instances of the Universal class for each type 't' where (Rep t) is inhabited

instance Univ Int where
    toVal n = VConstant Nothing Int n
    fromVal Int (VConstant _ Int n) = Just n
    fromVal Int (VLit (LInt n)) = Just n
    fromVal x y = Nothing
    rep =  Int
    showU = show

instance Univ Float where
    toVal n = VConstant Nothing Float n
    fromVal Float (VConstant _ Float n) = Just n
    fromVal Float (VLit (LFloat n)) = Just n
    fromVal x y = Nothing
    rep =  Float
    showU = show

instance Univ Double where
    toVal n = VConstant Nothing Double n
    fromVal Double (VConstant _ Double n) = Just n
    fromVal Double (VLit (LDouble n)) = Just n
    fromVal x y = Nothing
    rep =  Double
    showU = show

instance Univ Rational where
    toVal n = VConstant Nothing Rational n
    fromVal Rational (VConstant _ Rational n) = Just n
    fromVal Rational (VLit (LRational n)) = Just n
    fromVal x y = Nothing
    rep =  Rational
    showU = show

instance Univ Integer where
    toVal n = VConstant Nothing Integer n
    fromVal Integer (VConstant _ Integer n) = Just n
    fromVal Integer (VLit (LInteger n)) = Just n
    fromVal x y = Nothing
    rep =  Integer
    showU = show

instance Univ Char where
    toVal n = VConstant Nothing Char n
    fromVal Char (VConstant _ Char n) = Just n
    fromVal Char (VLit (LChar n)) = Just n
    fromVal x y = Nothing
    rep =  Char
    showU = show

instance {-# OVERLAPPING #-} Univ String where
    toVal n = VConstant Nothing String n
    fromVal String (VConstant _ String n) = Just n
    fromVal String (VList Char xs) = Just xs
    fromVal String (VLit (LString s)) = Just s
    fromVal x y = Nothing
    rep =  String
    showU x = x

instance Univ Bool where
    toVal n = VConstant Nothing Bool n
    fromVal Bool (VConstant _ Bool n) = Just n
    fromVal Bool (VLit (LBool n)) = Just n
    fromVal x y = Nothing
    rep =  Bool
    showU = show

instance Univ () where
    toVal n = VConstant Nothing Unit n
    fromVal Unit (VConstant _ Unit n) = Just n
    fromVal Unit (VLit LUnit) = Just ()
    fromVal x y = Nothing
    rep =  Unit
    showU x = "()"

instance {-# OVERLAPPABLE #-} Univ a => Univ [a] where
    toVal xs = VList rep xs
    fromVal (List a) (VList b xs) = do { Refl <- testEq a b; Just xs }
    fromVal (List a) (VConstant _ (List b) xs) =  do { Refl <- testEq a b; Just xs }
    fromVal _ _ = Nothing
    rep =  List rep
    showU xs = plistf showU "[" xs "," "]"

instance (Univ a,Univ b) => Univ (Array a b) where
    toVal xs = VArray rep rep xs
    fromVal (Array a b) (VArray m n xs) = do { Refl <- testEq a m; Refl <- testEq b n; Just xs}
    fromVal (Array a b) (VConstant _ (Array m n) xs) = do {Refl <- testEq a m; Refl <- testEq b n; Just xs}
    fromVal _ _ = Nothing
    rep =  Array rep rep
    showU x = showR rep x

instance (Ord a,Univ a,Univ b) => Univ (Map a b) where
    toVal xs = VMap rep rep xs
    fromVal (Map a b) (VMap m n xs) = do { Refl <- testEq a m; Refl <- testEq b n; Just xs}
    fromVal (Map a b) (VConstant _ (Map m n) xs) = do {Refl <- testEq a m; Refl <- testEq b n; Just xs}
    fromVal _ _ = Nothing
    rep =  Map rep rep
    showU x = showR rep x

instance Univ a => Univ (Maybe a) where
    toVal xs = VMaybe rep xs
    fromVal (Maybe a) (VMaybe b xs) = do { Refl <- testEq a b; Just xs }
    fromVal _ _ = Nothing
    rep = Maybe rep
    showU Nothing = "Nothing"
    showU (Just t) = "Just(" ++ showU t ++ ")"

instance (Univ a,Univ b) => Univ (a -> b) where
    toVal xs = VArrow rep rep xs
    fromVal (Arrow a b) (VArrow m n xs) = do { Refl <- testEq a m; Refl <- testEq b n; Just xs}
    fromVal (Arrow a b) (VConstant _ (Arrow m n) xs) = do {Refl <- testEq a m; Refl <- testEq b n; Just xs}
    fromVal _ _ = Nothing
    rep =  Arrow rep rep
    showU f = showR rep f

instance (Univ a, Univ b) => Univ(Either a b) where
   toVal e = VEither rep rep e
   fromVal (Either a b) (VEither m n e) = do { Refl <- testEq a m; Refl <- testEq b n; Just e}
   fromVal (Either a b) (VConstant _ (Either m n) e) = do { Refl <- testEq a m; Refl <- testEq b n; Just e}
   fromVal _ _ = Nothing
   rep = Either rep rep
   showU (Left x) = "(Left "++showU x++")"
   showU (Right x) = "(Right "++showU x++")"

instance Univ t => Univ (Rep t) where
   toVal x = VRep x
   fromVal (Rep m) (VConstant _ (Rep n) r) =  do {Refl <- testEq m n; Just r}
   fromVal (Rep m) x = Nothing
   rep = Rep rep

instance Univ a => Univ (Prog a) where
    toVal n = VProg rep n
    fromVal (Prog r1) (VProg r2 p) = do { Refl <- testEq r1 r2; Just p }
    fromVal _ _ = Nothing
    rep = Prog rep
    showU x = showR rep x

instance (Univ a, Univ b) =>  Univ(a,b) where
    toVal (a,b) = VTuple (Tuple (rep # rep # Nil1)) (a,b) (nest(a,b))
    fromVal (m@(Tuple _)) (VTuple n tup _) =  do {Refl <- testEq m n; Just tup}
    fromVal x y = Nothing
    rep =  Tuple(rep # rep # Nil1)

instance (Univ a, Univ b,Univ c) =>  Univ(a,b,c) where
    toVal (a,b,c) = VTuple (Tuple (rep # rep # rep # Nil1)) (a,b,c) (nest(a,b,c))
    fromVal (m@(Tuple _)) (VTuple n tup _) =  do {Refl <- testEq m n; Just tup}
    fromVal x y = Nothing
    rep =  Tuple(rep # rep # rep # Nil1)

instance (Univ a, Univ b, Univ c, Univ d) =>
   Univ (a,b,c,d) where
   toVal tup = VTuple (Tuple (rep # rep # rep # rep # Nil1)) tup (nest tup)
   fromVal (m@(Tuple _)) (VTuple n tup _) =  do {Refl <- testEq m n; Just tup}
   fromVal x y = Nothing
   rep =  Tuple(rep # rep # rep # rep # Nil1)

instance (Univ a, Univ b, Univ c, Univ d, Univ e) =>
   Univ (a,b,c,d,e) where
   toVal tup = VTuple (Tuple(rep # rep # rep # rep # rep # Nil1)) tup (nest tup)
   fromVal (m@(Tuple _)) (VTuple n tup _) =  do {Refl <- testEq m n; Just tup}
   fromVal x y = Nothing
   rep =  Tuple(rep # rep # rep # rep # rep # Nil1)

instance (Univ a, Univ b, Univ c, Univ d,Univ e,Univ f) =>
  Univ (a,b,c,d,e,f) where
  toVal tup = VTuple ( Tuple(rep # rep # rep # rep # rep # rep # Nil1)) tup (nest tup)
  fromVal (m@(Tuple _)) (VTuple n tup _) =  do {Refl <- testEq m n; Just tup}
  fromVal x y = Nothing
  rep =  Tuple(rep # rep # rep # rep # rep # rep # Nil1)

instance (Univ a, Univ b, Univ c, Univ d,Univ e,Univ f,Univ g) =>
   Univ (a,b,c,d,e,f,g) where
   toVal tup = VTuple (Tuple(rep # rep # rep # rep # rep # rep # rep # Nil1)) tup (nest tup)
   fromVal (m@(Tuple _)) (VTuple n tup _) =  do {Refl <- testEq m n; Just tup}
   fromVal x y = Nothing
   rep =   Tuple(rep # rep # rep # rep # rep # rep # rep # Nil1)

instance (Univ a, Univ b, Univ c, Univ d,Univ e,Univ f,Univ g,Univ h) =>
   Univ (a,b,c,d,e,f,g,h) where
   toVal tup = VTuple (Tuple(rep # rep # rep # rep # rep # rep # rep # rep # Nil1)) tup (nest tup)
   fromVal (m@(Tuple _)) (VTuple n tup _) =  do {Refl <- testEq m n; Just tup}
   fromVal x y = Nothing
   rep =  Tuple(rep # rep # rep # rep # rep # rep # rep # rep # Nil1)

instance (Univ a, Univ b, Univ c, Univ d,Univ e,Univ f,Univ g,Univ h,Univ i) =>
   Univ (a,b,c,d,e,f,g,h,i) where
   toVal tup = VTuple (Tuple(rep # rep # rep # rep # rep # rep # rep # rep # rep # Nil1)) tup (nest tup)
   fromVal (m@(Tuple _)) (VTuple n tup _) =  do {Refl <- testEq m n; Just tup}
   fromVal x y = Nothing
   rep =  Tuple(rep # rep # rep # rep # rep # rep # rep # rep # rep # Nil1)

instance (Univ a, Univ b, Univ c, Univ d,Univ e,Univ f,Univ g,Univ h,Univ i,Univ j) =>
   Univ (a,b,c,d,e,f,g,h,i,j) where
   toVal tup = VTuple (Tuple(rep # rep # rep # rep # rep # rep # rep # rep # rep # rep # Nil1)) tup (nest tup)
   fromVal (m@(Tuple _)) (VTuple n tup _) =  do {Refl <- testEq m n; Just tup}
   fromVal x y = Nothing
   rep =  Tuple(rep # rep # rep # rep # rep # rep # rep # rep # rep # rep # Nil1)

typeof:: Univ a => a -> Rep a
typeof x = rep

-- =========================================================================
-- The Universe includes Haskell tuples (of universe types) up to width 10
-- We need some class magic to make this happen.
-- =========================================================================

class (Univ nest, Univ flat) => Tup nest flat | flat -> nest, nest -> flat where
   unnest :: nest -> flat
   nest :: flat -> nest
   flat_nest_pair :: (Rep flat, List1 Rep nest)
   toList1 :: flat -> List1 Identity nest

pair :: Tup nest flat => List1 Rep nest -> (Rep flat,List1 Rep nest)
pair x = (Tuple x,x)

instance (Univ a,Univ b) => Tup (a,(b,())) (a,b) where
   unnest (a,(b,())) = (a,b)
   nest (a,b) =  (a,(b,()))
   flat_nest_pair = pair(rep # rep # Nil1)
   toList1 (a,b) = a !# b !# Nil1

instance (Univ a,Univ b,Univ c) => Tup (a,(b,(c,()))) (a,b,c) where
   unnest (a,(b,(c,()))) = (a,b,c)
   nest (a,b,c) = (a,(b,(c,())))
   flat_nest_pair = pair(rep # rep # rep # Nil1)
   toList1 (a,b,c) = a !# b !# c !# Nil1

instance  (Univ a,Univ b,Univ c,Univ d) => Tup (a,(b,(c,(d,()))))  (a,b,c,d) where
   unnest (a,(b,(c,(d,())))) = (a,b,c,d)
   nest (a,b,c,d) = (a,(b,(c,(d,()))))
   flat_nest_pair = pair(rep #rep # rep # rep # Nil1)
   toList1 (a,b,c,d) = a !# b !# c !# d !# Nil1

instance (Univ a,Univ b,Univ c,Univ d,Univ e) => Tup (a,(b,(c,(d,(e,()))))) (a,b,c,d,e) where
   unnest (a,(b,(c,(d,(e,()))))) = (a,b,c,d,e)
   nest (a,b,c,d,e) = (a,(b,(c,(d,(e,())))))
   flat_nest_pair = pair(rep # rep #rep # rep # rep # Nil1)
   toList1 (a,b,c,d,e) = a !# b !# c !# d !# e !# Nil1

instance (Univ a,Univ b,Univ c,Univ d,Univ e,Univ f) => Tup (a,(b,(c,(d,(e,(f,())))))) (a,b,c,d,e,f) where
    unnest (a,(b,(c,(d,(e,(f,())))))) = (a,b,c,d,e,f)
    nest (a,b,c,d,e,f) = (a,(b,(c,(d,(e,(f,()))))))
    flat_nest_pair = pair(rep # rep # rep #rep # rep # rep # Nil1)
    toList1 (a,b,c,d,e,f) = a !# b !# c !# d !# e !# f !# Nil1


instance (Univ a,Univ b,Univ c,Univ d,Univ e,Univ f,Univ g) =>
    Tup (a,(b,(c,(d,(e,(f,(g,()))))))) (a,b,c,d,e,f,g) where
    unnest(a,(b,(c,(d,(e,(f,(g,()))))))) = (a,b,c,d,e,f,g)
    nest (a,b,c,d,e,f,g) = (a,(b,(c,(d,(e,(f,(g,())))))))
    flat_nest_pair = pair(rep # rep # rep # rep #rep # rep # rep # Nil1)
    toList1 (a,b,c,d,e,f,g) = a !# b !# c !# d !# e !# f !# g !# Nil1

instance  (Univ a,Univ b,Univ c,Univ d,Univ e,Univ f,Univ g,Univ h) =>
    Tup (a,(b,(c,(d,(e,(f,(g,(h,())))))))) (a,b,c,d,e,f,g,h) where
    unnest (a,(b,(c,(d,(e,(f,(g,(h,())))))))) = (a,b,c,d,e,f,g,h)
    nest  (a,b,c,d,e,f,g,h) = (a,(b,(c,(d,(e,(f,(g,(h,()))))))))
    flat_nest_pair = pair(rep # rep # rep # rep # rep #rep # rep # rep # Nil1)
    toList1 (a,b,c,d,e,f,g,h) = a !# b !# c !# d !# e !# f !# g !# h !# Nil1

instance (Univ a,Univ b,Univ c,Univ d,Univ e,Univ f,Univ g,Univ h,Univ i) =>
    Tup (a,(b,(c,(d,(e,(f,(g,(h,(i,())))))))))  (a,b,c,d,e,f,g,h,i) where
    unnest (a,(b,(c,(d,(e,(f,(g,(h,(i,()))))))))) = (a,b,c,d,e,f,g,h,i)
    nest  (a,b,c,d,e,f,g,h,i) = (a,(b,(c,(d,(e,(f,(g,(h,(i,())))))))))
    flat_nest_pair = pair(rep # rep # rep # rep # rep # rep #rep # rep # rep # Nil1)
    toList1 (a,b,c,d,e,f,g,h,i) = a !# b !# c !# d !# e !# f !# g !# h !# i !# Nil1

instance (Univ a,Univ b,Univ c,Univ d,Univ e,Univ f,Univ g,Univ h,Univ i,Univ j) =>
    Tup (a,(b,(c,(d,(e,(f,(g,(h,(i,(j,()))))))))))  (a,b,c,d,e,f,g,h,i,j) where
    unnest (a,(b,(c,(d,(e,(f,(g,(h,(i,(j,())))))))))) = (a,b,c,d,e,f,g,h,i,j)
    nest  (a,b,c,d,e,f,g,h,i,j) = (a,(b,(c,(d,(e,(f,(g,(h,(i,(j,()))))))))))
    flat_nest_pair = pair(rep# rep # rep # rep # rep # rep # rep #rep # rep # rep # Nil1)
    toList1 (a,b,c,d,e,f,g,h,i,j) = a !# b !# c !# d !# e !# f !# g !# h !# i !# j !# Nil1

-- =============================================================================
-- Class Reflect constructs (Reps of Tuples) from (Tuples of Reps)
-- reflect (Int,Bool,String) --> Rep(Int,Bool,String)
-- part of the class magic.

class Reflect a b | a -> b , b -> a where
  reflect :: a -> b

instance (Univ a, Univ b) => Reflect (Rep a, Rep b) (Rep(a,b)) where
   reflect(a,b) = Tuple(a # b # Nil1)

instance (Univ a, Univ b,Univ c) => Reflect (Rep a, Rep b,Rep c) (Rep(a,b,c)) where
   reflect(a,b,c) = Tuple(a # b # c # Nil1)

instance (Univ a, Univ b,Univ c,Univ d) =>
   Reflect (Rep a, Rep b,Rep c,Rep d)
           (Rep(a,b,c,d)) where
   reflect(a,b,c,d) = Tuple(a # b # c # d # Nil1)

instance (Univ a, Univ b,Univ c,Univ d,Univ e) =>
   Reflect (Rep a, Rep b,Rep c,Rep d,Rep e)
           (Rep(a,b,c,d,e)) where
   reflect(a,b,c,d,e) = Tuple(a # b # c # d # e # Nil1)

instance (Univ a, Univ b,Univ c,Univ d,Univ e,Univ f) =>
   Reflect (Rep a, Rep b,Rep c,Rep d,Rep e,Rep f)
           (Rep(a,b,c,d,e,f)) where
   reflect(a,b,c,d,e,f) = Tuple(a # b # c # d # e # f # Nil1)

instance (Univ a, Univ b,Univ c,Univ d,Univ e,Univ f,Univ g) =>
   Reflect (Rep a, Rep b,Rep c,Rep d,Rep e,Rep f,Rep g)
           (Rep(a,b,c,d,e,f,g)) where
   reflect(a,b,c,d,e,f,g) = Tuple(a # b # c # d # e # f # g # Nil1)

instance (Univ a, Univ b,Univ c,Univ d,Univ e,Univ f,Univ g,Univ h) =>
   Reflect (Rep a, Rep b,Rep c,Rep d,Rep e,Rep f,Rep g,Rep h)
           (Rep(a,b,c,d,e,f,g,h)) where
   reflect(a,b,c,d,e,f,g,h) = Tuple(a # b # c # d # e # f # g # h # Nil1)

instance (Univ a, Univ b,Univ c,Univ d,Univ e,Univ f,Univ g,Univ h,Univ i) =>
   Reflect (Rep a, Rep b,Rep c,Rep d,Rep e,Rep f,Rep g,Rep h,Rep i)
           (Rep(a,b,c,d,e,f,g,h,i)) where
   reflect(a,b,c,d,e,f,g,h,i) = Tuple(a # b # c # d # e # f # g # h # i # Nil1)

instance (Univ a, Univ b,Univ c,Univ d,Univ e,Univ f,Univ g,Univ h,Univ i,Univ j) =>
   Reflect (Rep a, Rep b,Rep c,Rep d,Rep e,Rep f,Rep g,Rep h,Rep i,Rep j)
           (Rep(a,b,c,d,e,f,g,h,i,j)) where
   reflect(a,b,c,d,e,f,g,h,i,j) = Tuple(a # b # c # d # e # f # g # h # i # j # Nil1)

-- =========================================================================
-- Type indexed lists to encode tuples.
-- More of the class magic.

data List1 :: (* -> *) -> * -> * where
  Nil1  :: List1 f ()
  Cons1 :: Univ a => f a -> List1 f b -> List1 f (a,b)

-- Index preserving Map
mapL :: (forall t . f t -> g t) -> List1 f t -> List1 g t
mapL f Nil1 = Nil1
mapL f (Cons1 x xs) = Cons1 (f x) (mapL f xs)

-- Index Erasing Map
mapR :: (forall t . Univ t => f t -> s) -> List1 f t -> [s]
mapR f Nil1 = []
mapR f (Cons1 x xs) = f x : mapR f xs

-- Build List1 using infix: (Int # Bool # String # Nil1) :: List1 Rep (Int, (Bool, (String, ())))
infixr 5 #
y # ys = Cons1 y ys

infixr 5 !#
(!#) :: Univ a => a -> List1 Identity x -> List1 Identity (a,x)
y !# ys = Cons1 (Identity y) ys

-- Infix for the the nested type: (Int % Bool % String % Unit) :: Rep (Int, (Bool, (String, ())))
infixr 5 %
x % y = Tuple (x # y # Nil1)

-- ==============================================================
-- Showing things in the universe (if you know their Rep)

showR :: Rep t -> t -> String
showR Int t = show t
showR Float t = show t
showR Double t = show t
showR Rational t = show t
showR Integer t = show t
showR Char t = [t]
showR String t = t
showR Bool t = show t
showR Unit t = "()"
showR (List t) xs = plistf (showR t) "[" xs "," "]"
showR (Map k v) xs = "Map"++(plistf format "{" (toList xs) "," "}")
   where format (x,y) = showR k x ++ " => " ++ showR v y
showR (Maybe t) Nothing = "Nothing"
showR (Maybe t) (Just x) = "(Just "++showR t x++")"
showR (Arrow a b) fun = "<fun "++show a++" -> "++show b++">"
showR (Tuple xs) ys = showNestedAsFlat xs (nest ys)
showR (Rep t) x = "(Rep "++show x++")"
showR (Prog t) x = "<Program:: "++show t++">"

showNestedAsFlat:: List1 Rep t -> t -> String
showNestedAsFlat ll nest = "(" ++ help ll nest
   where help :: List1 Rep t -> t -> String
         help Nil1 () = ")"
         help (Cons1 rep Nil1) (x,()) = showR rep x ++")"
         help (Cons1 rep ys) (x,y) = showR rep x ++","++ help ys y

plistf :: (a -> String) -> String -> [a] -> String -> String -> String
plistf f open xs sep close = open ++ help xs ++ close
  where help [] = ""
        help [x] = f x
        help (x:xs) = f x ++ sep ++ help xs

-- ================================
-- Rep can be displayed with show

instance Show (Rep i) where
  show Int = "Int"
  show Float = "Float"
  show Double = "Double"
  show Rational = "Rational"
  show Integer = "Integer"
  show Char = "Char"
  show String = "String"
  show Bool = "Bool"
  show Unit = "()r"
  show Dyn = "Dyn"
  show (List v) = "(List "++show v++")"
  show (Map a b) = "(Map "++show a++" "++show b++")"
  show (Maybe a) = "(Maybe "++show a++")"
  show (Arrow a b) = "("++show a++" -> "++show b++")"
  show (Tuple xs) = plistf id "(" (mapR show xs) "," ")"
  show (Rep z) = "(Rep "++show z++")"

-- ===========================================================
-- Computing proofs that two Rep types are equal.
-- At runtime we dynamically construct a (Maybe static-proof)
-- ===========================================================

data Equal:: k -> k -> * where
  Refl :: Equal x x

testEq:: Rep a -> Rep b -> Maybe(Equal a b)
testEq Int Int = Just Refl
testEq Float Float = Just Refl
testEq Double Double = Just Refl
testEq Rational Rational = Just Refl
testEq Integer Integer = Just Refl
testEq Char Char = Just Refl
testEq String String = Just Refl
testEq String (List Char) = Just Refl
testEq (List Char) String = Just Refl
testEq Bool Bool = Just Refl
testEq Unit Unit = Just Refl
testEq (List x) (List m) =
  do { Refl <- testEq x m
     ;  Just Refl }
testEq (Map a b) (Map c d) =
  do { Refl <- testEq a c
     ; Refl <- testEq b d
     ; Just Refl }
testEq (Maybe x) (Maybe y) =
  do { Refl <- testEq x y
     ; Just Refl}
testEq (Arrow x y) (Arrow m n) =
  do { Refl <- testEq x m
     ; Refl <- testEq y n
     ; Just Refl }
testEq (Array x y) (Array m n) =
  do { Refl <- testEq x m
     ; Refl <- testEq y n
     ; Just Refl }
testEq (Tuple x) (Tuple y) =
  do { Refl <- testList1 x y     -- If he two List1 are equal the types must be equal.
     ; Just (unsafeCoerce Refl) }
testEq (Rep x) (Rep m) =
  do { Refl <- testEq x m
     ;  Just Refl }

testList1:: List1 Rep n1 -> List1 Rep n2 -> Maybe(Equal n1 n2)
testList1 Nil1 Nil1 = Just Refl
testList1 (Cons1 x xs)  (Cons1 y ys) =
   do { Refl <- testEq x y
      ; Refl <- testList1 xs ys
      ; Just Refl }

-- =================================================
-- Programs

data Prog t where
   ELit:: Lit t -> Prog t
   EPrim:: String -> Int -> t -> Prog t  -- We promise 't' is total, and costs no more then 'Int'
   EVar:: String -> Rep t -> Prog t
   EApp:: Prog(a -> t) -> Prog a -> Prog t
   ETuple:: Tup nest flat => List1 Prog nest -> Prog flat
   EAbs:: Tup nest dom => List1 Pat nest -> Prog rng -> Prog(dom -> rng)

data Pat t where
   PVar:: String -> Rep t -> Pat t
   PTuple:: Tup nest flat => List1 Pat nest -> Pat flat
   PLit:: Lit t -> Pat t
   PPrim:: Rep t -> (t -> Env -> Env) -> Pat t
   PUnderscore :: Pat t

newtype Env = Env (Map String Val)


eval :: Env -> Prog t -> Metered t
eval env (ELit l) = (pure (evalLit l))  -- Constants cost nothing to evaluate
eval env (EPrim name cost x) = decrement cost (pure x)
eval env (EApp (EPrim name cost f) arg) =
   do { v <- eval env arg ; decrement cost (pure (f v))}

-- ==========================================================
-- The Metering Monad

data Result t = Ok t | TooCostly | NotOk String
newtype Metered t = Metered { runMetered :: (Int -> (Int,Result t)) }

instance Functor Result where
   fmap f (Ok t) = Ok (f t)
   fmap f TooCostly = TooCostly
   fmap f (NotOk s) = NotOk s

instance Functor Metered where
   fmap f (Metered g) = Metered h
      where h n = (m,fmap f r) where (m,r) = g n

instance Applicative Metered where
   pure x = Metered(\ n -> (n,Ok x))
   g <*> y = do { f <- g; x <- y; pure(f x) }


instance Monad Metered where
   return x = pure x
   (Metered f) >>= g = Metered h
     where h n | n<=0 = (0,TooCostly)
           h n = case f n of
                  (m,Ok y) -> runMetered (g y) (m-1)
                  (m,TooCostly) -> (0,TooCostly)
                  (m,NotOk s) -> (m,NotOk s)

decrement:: Int -> Metered t -> Metered t
decrement n (Metered f) = Metered g
   where g m = case f m of
                (l,Ok y) | l > n -> (l-n,Ok y)
                (l,Ok y) -> (0,TooCostly)
                (l,ans) -> (l,ans)