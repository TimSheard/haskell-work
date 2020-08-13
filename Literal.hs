{-# LANGUAGE GADTs, RankNTypes  #-}

module Literal where
--------------------------------------------------------------------

data Literal
   = LChar { unChar::Char }             -- 'x'
   | LString {unString::String}         -- "abc" "\nabc"
   | LInt { unInt :: Int }              -- 5 , -5
   | LRational {unRational :: Rational} -- 4%5
   | LInteger {unInteger :: Integer }   -- 0234704370329473294
   | LFloat { unFloat::Float }         -- 2.3 , 0.5 , -3.4
   | LDouble { unDouble::Double}         -- 2.3 , 0.5 , -3.4
   | LBool {unBool:: Bool }             -- True , False
   | LUnit                              -- ()
   | LEntity {unEntity:: Int}           -- [10009]
  deriving (Eq,Ord)


compareL (LChar x) (LChar y) = compare x y
compareL (LString x) (LString y) = compare x y
compareL (LInt x) (LInt y) = compare x y
compareL (LRational x) (LRational y) = compare x y
compareL (LInteger x) (LInteger y) = compare x y
compareL (LFloat x) (LFloat y) = compare x y
compareL (LDouble x) (LDouble y) = compare x y
compareL (LBool x) (LBool y) = compare x y
compareL LUnit LUnit = EQ
compareL (LEntity x) (LEntity y) = compare x y
compareL x y = error("Wrong types in comparison:  "++show x++" does not have the same type as "++show y)

instance Show Literal where
  show (LChar c) = show c
  show (LString s) = show s
  show (LInt n) = show n
  show (LRational n) = show n
  show (LInteger n) = show n
  show (LFloat n) = show n
  show (LDouble n) = show n
  show (LBool t) = show t
  show LUnit = "()"
  show (LEntity n) = "["++show n++"]"

-- liftInteger is an attempt to implement toInteger, which always returns an LInteger
-- object, then if you operate on it in a context that demands (say a Float) then
-- it is lazily lifted to a float. So there is implict coercion on Integer,
-- but no other type.

liftInteger :: String -> (forall t . Num t => (t -> t -> t)) -> Literal -> Literal -> Literal
liftInteger s f (LInteger x) (LInt y) = LInt (f (fromInteger x) y)
liftInteger s f (LInt x) (LInteger y) = LInt (f x (fromInteger y))
liftInteger s f (LInteger x) (LFloat y) = LFloat (f (fromInteger x) y)
liftInteger s f (LFloat x) (LInteger y) = LFloat (f x (fromInteger y))
liftInteger s f (LInteger x) (LDouble y) = LDouble (f (fromInteger x) y)
liftInteger s f (LDouble x) (LInteger y) = LDouble (f x (fromInteger y))
liftInteger s f (LInteger x) (LRational y) = LRational (f (fromInteger x) y)
liftInteger s f (LRational x) (LInteger y) = LRational (f x (fromInteger y))
liftInteger s f x y = error ("Incompatible types for overloaded opertor "++s)

instance Num Literal where
  fromInteger n = LInt(fromInteger n)
  (+) (LInt n) (LInt m) = LInt(n+m)
  (+) (LFloat n) (LFloat m) = LFloat(n+m)
  (+) (LDouble n) (LDouble m) = LDouble(n+m)
  (+) (LRational n) (LRational m) = LRational(n+m)
  (+) (LInteger n) (LInteger m) = LInteger(n+m)
  (+) x y = liftInteger "(+)" (+) x y
  (*) (LInt n) (LInt m) = LInt(n*m)
  (*) (LFloat n) (LFloat m) = LFloat(n*m)
  (*) (LDouble n) (LDouble m) = LDouble(n*m)
  (*) (LRational n) (LRational m) = LRational(n*m)
  (*) (LInteger n) (LInteger m) = LInteger(n*m)
  (*) x y = liftInteger "(*)" (*) x y
  (-) (LInt n) (LInt m) = LInt(n-m)
  (-) (LFloat n) (LFloat m) = LFloat(n-m)
  (-) (LDouble n) (LDouble m) = LDouble(n-m)
  (-) (LRational n) (LRational m) = LRational(n-m)
  (-) (LInteger n) (LInteger m) = LInteger(n-m)
  (-) x y = liftInteger "(-)" (-) x y
  abs (LInt n) = LInt(abs n)
  abs (LFloat n) = LFloat(abs n)
  abs (LDouble n) = LDouble(abs n)
  abs (LInteger n) = LInteger(abs n)
  abs (LRational n) = LRational(abs n)
  abs x = error ("Non Num in instance (Num Literal) for 'abs'")
  negate (LInt n) = LInt(negate n)
  negate(LFloat n) = LFloat(negate n)
  negate(LDouble n) = LDouble(negate n)
  negate (LInteger n) = LInteger(negate n)
  negate (LRational n) = LRational(negate n)
  negate x = error ("Non Num in instance (Num Literal) for 'negate'")
  signum (LInt n) = LInt(signum n)
  signum (LFloat n) = LFloat(signum n)
  signum (LDouble n) = LDouble(signum n)
  signum (LInteger n) = LInteger(signum n)
  signum (LRational n) = LRational(signum n)
  signum x = error ("Non Num in instance (Num Literal) for 'signum'")

{-
toLiteral :: HasRep t => t -> Literal
toLiteral t = repToLiteral repOf t

repToLiteral :: Rep t -> t -> Literal
repToLiteral Char n = LChar n
repToLiteral String n = LString n
repToLiteral Int n = LInt n
repToLiteral Rational n = LRational n
repToLiteral Integer n = LInteger n
repToLiteral Float n = LFloat n
repToLiteral Double n = LDouble n
repToLiteral Bool t = LBool t
repToLiteral Unit n = LUnit
-}


data Lit t where
   LitChar :: Char -> Lit Char
   LitString :: String -> Lit String
   LitInt :: Int -> Lit Int
   LitRational :: Rational -> Lit Rational
   LitInteger :: Integer -> Lit Integer
   LitFloat :: Float -> Lit Float
   LitDouble :: Double -> Lit Double
   LitBool :: Bool -> Lit Bool
   LitUnit :: Lit ()

litToLiteral:: Lit t -> Literal
litToLiteral x = case x of
  LitChar n -> LChar n
  LitString n -> LString n
  LitInt n -> LInt n
  LitRational n -> LRational n
  LitInteger n -> LInteger n
  LitFloat n -> LFloat n
  LitDouble n -> LDouble n
  LitBool n -> LBool n
  LitUnit ->  LUnit

evalLit:: Lit t -> t
evalLit x = case x of
  LitChar n -> n
  LitString n -> n
  LitInt n -> n
  LitRational n -> n
  LitInteger n -> n
  LitFloat n -> n
  LitDouble n -> n
  LitBool n -> n
  LitUnit -> ()
