{-# OPTIONS_GHC  -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

{-# LANGUAGE Rank2Types, TypeFamilies #-}
{-# LANGUAGE ConstraintKinds, KindSignatures, PolyKinds, TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

module EqualityProofs where

-- import Data.Typeable(Typeable(..), typeOf, TypeRep, splitTyConApp, typeRepTyCon, typeRepArgs)

import Type.Reflection(Typeable,typeOf, TypeRep, typeRep, (:~:)(Refl))
import Data.Type.Equality(TestEquality(testEquality) )
import Data.Proxy
import Data.Constraint(Dict(Dict),Constraint)
import {-# SOURCE #-} Classes(B(..))

data Action b where
  Action:: TypeRep a -> (a -> b) -> Action b

xs :: [Action Int]
xs = [Action (typeRep @Char) (\ x -> 5)]

run :: TypeRep a -> [Action b] -> a -> Maybe b
run rep [] a = Nothing
run rep (Action rep2 f : more) a =
   case testEquality rep rep2 of
     Just Refl -> Just (f a)
     Nothing -> run rep more a

action :: forall a b. Typeable a => (a -> b) -> Action b
action f = Action (typeRep @a) f

data Rep t = Rep (TypeRep t)

match :: forall t s. Typeable t => TypeRep s -> Maybe (s :~: t)
match s = testEquality s (typeRep @t)

foo :: forall t s. Typeable s => s -> TypeRep t -> t
foo s rep | Just Refl <- match @Int rep  = 3
          | Just Refl <- match @Bool rep  = True
          | Just Refl <- match @[s] rep = [s,s]
foo s rep = error ("No match at type: "++ show(typeOf s)++" :~: "++show rep)

bar :: TypeRep [a] -> TypeRep [b] -> Maybe ([a] :~: [b])
bar x y = testEquality x y

{-
class B t where
  getInt:: t -> Int
  getBool:: t -> Bool
-}


instance B (Bod E1) where
  getInt (Body n b) = n
  getBool (Body n b) = b

instance B (Bod E2) where
  getInt (Body2 n b _) = n
  getBool (Body2 n b _) = b

test3 :: Bod E1 -> Int
test3 t@(Body{}) = getInt t


class (Typeable era, B(Bod era)) => Era era where
  data Bod era :: *
  this:: TypeRep era
  this = typeRep @era



newtype EraTag e v = Tag { unTag:: v}



data E1
data E2

-- data Body era = B (Body era) => Body {a::Int, b::Bool}
-- data Body2 era = B (Body2 era) => Body2 {a2::Int, b2::Bool, c2::String}


instance Era E1 where
  data Bod E1 = B (Bod E1) => Body {a::Int, b::Bool}

instance Era E2 where
  data Bod E2 = B (Bod E2) => Body2 {a2::Int, b2::Bool, c2::String}

test4 :: forall (e :: *) . Era e => Bod e -> Int
test4 b | Just Refl <- match @E1 (this @e) = (getInt b)
        | Just Refl <- match @E2 (this @e) = getInt b
