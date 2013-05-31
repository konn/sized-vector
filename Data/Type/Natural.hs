{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, GADTs    #-}
{-# LANGUAGE KindSignatures, MultiParamTypeClasses, NoImplicitPrelude #-}
{-# LANGUAGE PolyKinds, RankNTypes, TemplateHaskell, TypeFamilies     #-}
{-# LANGUAGE TypeOperators, UndecidableInstances                      #-}
-- | Type level peano natural number, some arithmetic functions and their singletons.
module Data.Type.Natural (
                         -- * Natural numbers and its singleton type
                           -- | Peano natural numbers. It will be promoted to the type-level natural number.
                           Nat(..),
                           -- | Singleton type for 'Nat'.
                           SNat
                         -- ** Smart constructors
                         , sZ, sS
                         -- ** Arithmetic functions and thir singletons.
                         , min, Min, sMin, max, Max, sMax, (:+:), (%+), (:*:), (%*), (:-:), (%-)
                         -- ** Type-level predicate & judgements
                         , Leq(..), (:<=), (:<<=), LeqInstance, leqRefl, leqSucc
                         , boolToPropLeq, boolToClassLeq, propToClassLeq
                         -- * Type-classes for singletons
                         --   (These will be removed once singletons package available for the latest singletons package)
                         , Sing(..), SingInstance(..), singInstance
                         -- * Conversion functions
                         , natToInt, intToNat, sNatToInt
                         -- * Useful type synonyms and constructors
                         , Zero, One, Two, Three, Four, Five, Six, Seven, Eight, Nine, Ten
                         , Eleven, Twelve, Thirteen, Fourteen, Fifteen, Sixteen, Seventeen, Eighteen, Nineteen, Twenty
                         , sZero, sOne, sTwo, sThree, sFour, sFive, sSix, sSeven, sEight, sNine, sTen, sEleven
                         , sTwelve, sThirteen, sFourteen, sFifteen, sSixteen, sSeventeen, sEighteen, sNineteen, sTwenty
                         , N0, N1, N2, N3, N4, N5, N6, N7, N8, N9, N10, N11, N12, N13, N14, N15, N16, N17, N18, N19, N20
                         , sN0, sN1, sN2, sN3, sN4, sN5, sN6, sN7, sN8, sN9, sN10, sN11, sN12, sN13, sN14
                         , sN15, sN16, sN17, sN18, sN19, sN20
                         ) where
import           Data.Singletons
import           Prelude         (Bool (..), Eq (..), Integral (..), Ord ((<)),
                                  Show (..), error, id, otherwise, ($))
import qualified Prelude         as P

--------------------------------------------------
-- * Natural numbers and its singleton type
--------------------------------------------------
singletons [d|
 data Nat = Z | S Nat
            deriving (Show, Eq, Ord)
 |]

--------------------------------------------------
-- ** Arithmetic functions.
--------------------------------------------------

singletons [d|
 -- | Minimum function.
 min :: Nat -> Nat -> Nat
 min Z     Z     = Z
 min Z     (S _) = Z
 min (S _) Z     = Z
 min (S m) (S n) = S (min m n)

 -- | Maximum function.
 max :: Nat -> Nat -> Nat
 max Z     Z     = Z
 max Z     (S n) = S n
 max (S n) Z     = S n
 max (S n) (S m) = S (max n m)
 |]

singletons [d|
 (+) :: Nat -> Nat -> Nat
 Z   + n = n
 S m + n = S (m + n)

 (-) :: Nat -> Nat -> Nat
 n   - Z   = n
 S n - S m = n - m
 Z   - S _ = Z

 (*) :: Nat -> Nat -> Nat
 Z   * S _ = Z
 S n * m   = n * m + n
 |]

instance P.Num Nat where
  n - m = n - m
  n + m = n + m
  n * m = n * m
  abs = id
  signum Z = Z
  signum _ = S Z
  fromInteger 0             = Z
  fromInteger n | n < 0     = error "negative integer"
                | otherwise = S $ P.fromInteger (n P.- 1)

infixl 6 :-:, %:-, -

type n :-: m = n :- m
infix 6 :+:, %+, %:+, :+

type n :+: m = n :+ m

-- | Addition for singleton numbers.
(%+) :: SNat n -> SNat m -> SNat (n :+: m)
(%+) = (%:+)

infix 7 :*:, %*, %:*, :*

-- | Type-level multiplication.
type n :*: m = n :* m

-- | Multiplication for singleton numbers.
(%*) :: SNat n -> SNat m -> SNat (n :*: m)
(%*) = (%:*)

--------------------------------------------------
-- ** Type-level predicate & judgements.
--------------------------------------------------
-- | Comparison via type-class.
class (n :: Nat) :<= (m :: Nat)
instance Z :<= n
instance (n :<= m) => S n :<= S m


-- | Comparison function
{-
type family   (n :: Nat) :<<= (m :: Nat) :: Bool
type instance Z   :<<= n   = True
type instance S n :<<= Z   = False
type instance S n :<<= S m = n :<<= m
-}
singletons [d|
 (<<=) :: Nat -> Nat -> Bool
 Z   <<= _   = True
 S _ <<= Z   = False
 S n <<= S m = n <<= m
 |]

(%-) :: (n :<<= m) ~ True => SNat n -> SNat m -> SNat (n :-: m)
n   %- SZ    = n
SS n %- SS m = n %- m
_    %- _    = error "impossible!"

infixl 6 %-


--------------------------------------------------
-- Useful type synonyms and constructors.
--------------------------------------------------

singletons [d|
 zero, one, two, three, four, five, six, seven, eight, nine, ten :: Nat           
 eleven, twelve, thirteen, fourteen, fifteen, sixteen, seventeen, eighteen, nineteen, twenty :: Nat           
 zero      = Z
 one       = S zero
 two       = S one
 three     = S two
 four      = S three
 five      = S four
 six       = S five
 seven     = S six
 eight     = S seven
 nine      = S eight
 ten       = S nine
 eleven    = S ten
 twelve    = S eleven
 thirteen  = S twelve
 fourteen  = S thirteen
 fifteen   = S fourteen
 sixteen   = S fifteen
 seventeen = S sixteen
 eighteen  = S seventeen
 nineteen  = S eighteen
 twenty    = S nineteen
 n0  = zero
 n1  = one
 n2  = two
 n3  = three
 n4  = four
 n5  = five
 n6  = six
 n7  = seven
 n8  = eight
 n9  = nine
 n10 = ten
 n11 = eleven
 n12 = twelve
 n13 = thirteen
 n14 = fourteen
 n15 = fifteen
 n16 = sixteen
 n17 = seventeen
 n18 = eighteen
 n19 = nineteen
 n20 = twenty
 |]

-- | Comparison witness via GADTs.
-- | Comparison witness via GADTs.
data Leq (n :: Nat) (m :: Nat) where
  ZeroLeq     :: SNat m -> Leq Zero m
  SuccLeqSucc :: Leq n m -> Leq (S n) (S m)

data LeqInstance n m where
  LeqInstance :: (n :<= m) => LeqInstance n m

boolToPropLeq :: (n :<<= m) ~ True => SNat n -> SNat m -> Leq n m
boolToPropLeq SZ     m      = ZeroLeq m
boolToPropLeq (SS n) (SS m) = SuccLeqSucc $ boolToPropLeq n m
boolToPropLeq _      _      = error "impossible happend!"

boolToClassLeq :: (n :<<= m) ~ True => SNat n -> SNat m -> LeqInstance n m
boolToClassLeq SZ     _      = LeqInstance
boolToClassLeq (SS n) (SS m) =
  case boolToClassLeq n m of
    LeqInstance -> LeqInstance
boolToClassLeq _ _ = error "impossible!"

propToClassLeq :: Leq n m -> LeqInstance n m
propToClassLeq (ZeroLeq _) = LeqInstance
propToClassLeq (SuccLeqSucc leq) =
  case propToClassLeq leq of
    LeqInstance -> LeqInstance

leqRefl :: SNat n -> Leq n n
leqRefl SZ = ZeroLeq sZ
leqRefl (SS n) = SuccLeqSucc $ leqRefl n

leqSucc :: SNat n -> Leq n (S n)
leqSucc SZ = ZeroLeq sOne
leqSucc (SS n) = SuccLeqSucc $ leqSucc n

--------------------------------------------------
-- * Conversion functions.
--------------------------------------------------

-- | Convert integral numbers into 'Nat'
intToNat :: (Integral a, Ord a) => a -> Nat
intToNat 0 = Z
intToNat n
    | n < 0     = error "negative integer"
    | otherwise = S $ intToNat (n P.- 1)

-- | Convert 'Nat' into normal integers.
natToInt :: Integral n => Nat -> n
natToInt Z     = 0
natToInt (S n) = natToInt n P.+ 1

-- | Convert 'SNat n' into normal integers.
sNatToInt :: P.Num n => SNat x -> n
sNatToInt SZ     = 0
sNatToInt (SS n) = sNatToInt n P.+ 1
