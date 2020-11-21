
-- | Flags is a mapping from String to small values.
--   It's intended use is as parameter to a familty of functions
--   That control some aspect of the computation.
module Flags where

import Data.Map(Map,insert)
import qualified Data.Map as Map

data Flag = Int Int | Char Char | Bool Bool | List [Flag] | Tuple [Flag]
  deriving Show

class Flagger t where
  extract:: Flag -> Maybe t
  flag:: t -> Flag

instance Flagger Int where
  extract (Int n) = Just n
  extract _ = Nothing
  flag = Int

instance Flagger Char where
  extract (Char n) = Just n
  extract _ = Nothing
  flag = Char

instance Flagger Bool where
  extract (Bool n) = Just n
  extract _ = Nothing
  flag = Bool

instance Flagger a => Flagger [a] where
  extract (List fs) = sequence(map extract fs)
  extract _ = Nothing
  flag xs = List(map flag xs)

instance (Flagger a,Flagger b) => Flagger (a,b) where
  extract (Tuple [x,y]) = do a <- extract x; b <- extract y; Just(a,b)
  extract _ = Nothing
  flag (x,y) = Tuple[flag x, flag y]

instance (Flagger a,Flagger b,Flagger c) => Flagger (a,b,c) where
  extract (Tuple [x,y,z]) = do a <- extract x; b <- extract y; c<- extract z; Just(a,b,c)
  extract _ = Nothing
  flag (x,y,z) = Tuple[flag x, flag y, flag z]


ff = List[Int 5,Int 6, Int 2]
gg =  List[Int 5,Bool True, Int 2]


newtype Flags = Flags (Map String Flag)

fetch:: Flagger t => String -> Flags -> Maybe t
fetch key (Flags m)  = case Map.lookup key m of { Just t -> extract t; Nothing -> Nothing }

add:: Flagger t => String -> t -> Flags -> Flags
add key t (Flags m) = Flags(insert key (flag t) m)

test :: String -> Flags -> Bool -> Bool
test key flags def = fetchWDF key flags def

-- | fetch With Default Flag
fetchWDF:: Flagger t => String -> Flags -> t -> t
fetchWDF key (Flags m) def = maybe def (maybe def id . extract) (Map.lookup key m)

-- foo :: Flags -> Int -> Int
foo flags n = n + fetchWDF "size" flags 0
