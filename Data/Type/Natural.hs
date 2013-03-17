{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, GADTs        #-}
{-# LANGUAGE KindSignatures, MultiParamTypeClasses, NoImplicitPrelude     #-}
{-# LANGUAGE PolyKinds, TypeFamilies, TypeOperators, UndecidableInstances #-}
-- | Type level peano natural number, some arithmetic functions and their singletons.
module Data.Type.Natural (
                         -- * Natural numbers and its singleton type
                           Nat(..), SNat(..)
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
import Prelude (Eq (..), Integral (..), Num (..), Ord ((<)), Show (..), error,
                id, otherwise, ($), Bool(..))

--------------------------------------------------
-- * Natural numbers and its singleton type
--------------------------------------------------

-- | Peano natural numbers. It will be promoted to the type-level natural number.
data Nat = Z | S Nat
           deriving (Show, Eq, Ord)

-- | Singleton type for 'Nat'.
--   When constructing data, use smart constructors such as 'sZ' and 'sS'.
data SNat (n :: Nat) where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

--------------------------------------------------
-- ** Smart constructors.
--------------------------------------------------

-- | The smart constructor for @SZ@.
sZ :: SNat Z
sZ = case singInstance SZ of
       SingInstance -> SZ

-- | The smart constructor for @SS n@.
sS :: SNat n -> SNat (S n)
sS n = case singInstance n of
         SingInstance -> SS n

--------------------------------------------------
-- ** Arithmetic functions.
--------------------------------------------------

-- | Minimum function.
min :: Nat -> Nat -> Nat
min Z     Z     = Z
min Z     (S _) = Z
min (S _) Z     = Z
min (S m) (S n) = S (min m n)

-- | Type-level minimum function.
type family Min (n :: Nat) (m :: Nat) :: Nat
type instance Min Z Z     = Z
type instance Min Z (S n) = Z
type instance Min (S m) Z = Z
type instance Min (S n) (S m) = S (Min n m)

-- | Singleton function for minimum function.
sMin :: SNat n -> SNat m -> SNat (Min n m)
sMin SZ     SZ     = sZ
sMin SZ     (SS _) = sZ
sMin (SS _) SZ     = sZ
sMin (SS m) (SS n) = sS (sMin m n)

-- | Maximum function.
max :: Nat -> Nat -> Nat
max Z     Z     = Z
max Z     (S n) = S n
max (S n) Z     = S n
max (S n) (S m) = S (max n m)

-- | Type-level maximum function.
type family Max (n :: Nat) (m :: Nat) :: Nat
type instance Max Z Z     = Z
type instance Max Z (S n) = S n
type instance Max (S n) Z = S n
type instance Max (S n) (S m) = S (Max n m)

-- | Singleton function for maximum.
sMax :: SNat n -> SNat m -> SNat (Max n m)
sMax SZ     SZ     = SZ
sMax (SS n) SZ     = SS n
sMax SZ     (SS n) = SS n
sMax (SS n) (SS m) = SS (sMax n m)

instance Num Nat where
  n   - Z   = n
  S n - S m = n - m
  Z     + n = n
  (S m) + n = S (m + n)
  Z     * _ = 0
  (S m) * n = m * n + n
  abs = id
  signum Z = Z
  signum _ = S Z
  fromInteger 0             = Z
  fromInteger n | n < 0     = error "negative integer"
                | otherwise = S $ fromInteger (n - 1)

infixl 6 :-:, %-
type family (n :: Nat) :-: (m :: Nat) :: Nat
type instance n     :-: Z     = n
type instance (S n) :-: (S m) = n :-: m

(%-) :: (n :<<= m) ~ True => SNat n -> SNat m -> SNat (n :-: m)
n   %- SZ    = n
SS n %- SS m = n %- m
_    %- _    = error "impossible!"

infix 6 :+:, %+

-- | Type-level addition.
type family (n :: Nat) :+: (m :: Nat) :: Nat
type instance  Z   :+: n = n
type instance  S m :+: n = S (m :+: n)

-- | Addition for singleton numbers.
(%+) :: SNat n -> SNat m -> SNat (n :+: m)
SZ   %+ n = n
SS n %+ m = sS (n %+ m)

infix 7 :*:, %*

-- | Type-level multiplication.
type family   (n :: Nat) :*: (m :: Nat) :: Nat
type instance Z   :*: n = Z
type instance S m :*: n = m :*: n :+: n

-- | Multiplication for singleton numbers.
(%*) :: SNat n -> SNat m -> SNat (n :*: m)
SZ   %* _ = sZ
SS n %* m = n %* m %+ m

--------------------------------------------------
-- ** Type-level predicate & judgements.
--------------------------------------------------
-- | Comparison via type-class.
class (n :: Nat) :<= (m :: Nat)
instance Z :<= n
instance (n :<= m) => S n :<= S m

-- | Comparison function
type family   (n :: Nat) :<<= (m :: Nat) :: Bool
type instance Z   :<<= n   = True
type instance S n :<<= Z   = False
type instance S n :<<= S m = n :<<= m

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

leqRefl :: SNat n -> LeqInstance n n
leqRefl SZ = LeqInstance
leqRefl (SS n) =
  case leqRefl n of
    LeqInstance -> LeqInstance

leqSucc :: SNat n -> LeqInstance n (S n)
leqSucc SZ = LeqInstance
leqSucc (SS n) =
    case leqSucc n of
      LeqInstance -> LeqInstance


--------------------------------------------------
-- * Type classes for singletons.
--------------------------------------------------

-- | Singleton type-class.
-- This class will be removed soon after singletons package available for the latest Haskell Paltform.
class Sing n where
  -- | Automatically compute singletons.
  sing :: SNat n

instance Sing Z where
  sing = SZ

instance Sing n => Sing (S n) where
  sing = SS sing

-- | Witness for 'Sing' instance.
--   This type will be removed soon after singletons package available for the latest Haskell Paltform.
data SingInstance a where
  SingInstance :: Sing a => SingInstance a

-- | Get witness for singleton integers.
--   This function will be removed soon after singletons package available for the latest Haskell Paltform.
singInstance :: SNat n -> SingInstance n
singInstance SZ = SingInstance
singInstance (SS n) =
    case singInstance n of
      SingInstance -> SingInstance

--------------------------------------------------
-- * Conversion functions.
--------------------------------------------------

-- | Convert integral numbers into 'Nat'
intToNat :: (Integral a, Ord a) => a -> Nat
intToNat 0 = Z
intToNat n
    | n < 0     = error "negative integer"
    | otherwise = S $ intToNat (n - 1)

-- | Convert 'Nat' into normal integers.
natToInt :: Integral n => Nat -> n
natToInt Z     = 0
natToInt (S n) = natToInt n + 1

-- | Convert 'SNat n' into normal integers.
sNatToInt :: Num n => SNat x -> n
sNatToInt SZ     = 0
sNatToInt (SS n) = sNatToInt n + 1

--------------------------------------------------
-- Useful type synonyms and constructors.
--------------------------------------------------

type Zero      = Z
type One       = S Zero
type Two       = S One
type Three     = S Two
type Four      = S Three
type Five      = S Four
type Six       = S Five
type Seven     = S Six
type Eight     = S Seven
type Nine      = S Eight
type Ten       = S Nine
type Eleven    = S Ten
type Twelve    = S Eleven
type Thirteen  = S Twelve
type Fourteen  = S Thirteen
type Fifteen   = S Fourteen
type Sixteen   = S Fifteen
type Seventeen = S Sixteen
type Eighteen  = S Seventeen
type Nineteen  = S Eighteen
type Twenty    = S Nineteen

type N0  = Z
type N1  = One
type N2  = Two
type N3  = Three
type N4  = Four
type N5  = Five
type N6  = Six
type N7  = Seven
type N8  = Eight
type N9  = Nine
type N10 = Ten
type N11 = Eleven
type N12 = Twelve
type N13 = Thirteen
type N14 = Fourteen
type N15 = Fifteen
type N16 = Sixteen
type N17 = Seventeen
type N18 = Eighteen
type N19 = Nineteen
type N20 = Twenty

sZero :: SNat 'Z
sZero = sZ

sOne :: SNat One
sOne = sS sZero
sTwo :: SNat Two
sTwo = sS sOne
sThree :: SNat Three
sThree = sS sTwo
sFour :: SNat Four
sFour = sS sThree
sFive :: SNat Five
sFive = sS sFour
sSix :: SNat Six
sSix = sS sFive
sSeven :: SNat Seven
sSeven = sS sSix
sEight :: SNat Eight
sEight = sS sSeven
sNine :: SNat Nine
sNine = sS sEight
sTen :: SNat Ten
sTen = sS sNine
sEleven :: SNat Eleven
sEleven = sS sTen
sTwelve :: SNat Twelve
sTwelve = sS sEleven
sThirteen :: SNat Thirteen
sThirteen = sS sTwelve
sFourteen :: SNat Fourteen
sFourteen = sS sThirteen
sFifteen :: SNat Fifteen
sFifteen = sS sFourteen
sSixteen :: SNat Sixteen
sSixteen = sS sFifteen
sSeventeen :: SNat Seventeen
sSeventeen = sS sSixteen
sEighteen :: SNat Eighteen
sEighteen = sS sSeventeen
sNineteen :: SNat Nineteen
sNineteen = sS sEighteen
sTwenty :: SNat Twenty
sTwenty = sS sNineteen

sN0 :: SNat 'Z
sN0  = sZ
sN1 :: SNat One
sN1  = sOne
sN2 :: SNat Two
sN2  = sTwo
sN3 :: SNat Three
sN3  = sThree
sN4 :: SNat Four
sN4  = sFour
sN5 :: SNat Five
sN5  = sFive
sN6 :: SNat Six
sN6  = sSix
sN7 :: SNat Seven
sN7  = sSeven
sN8 :: SNat Eight
sN8  = sEight
sN9 :: SNat Nine
sN9  = sNine
sN10 :: SNat Ten
sN10 = sTen
sN11 :: SNat Eleven
sN11 = sEleven
sN12 :: SNat Twelve
sN12 = sTwelve
sN13 :: SNat Thirteen
sN13 = sThirteen
sN14 :: SNat Fourteen
sN14 = sFourteen
sN15 :: SNat Fifteen
sN15 = sFifteen
sN16 :: SNat Sixteen
sN16 = sSixteen
sN17 :: SNat Seventeen
sN17 = sSeventeen
sN18 :: SNat Eighteen
sN18 = sEighteen
sN19 :: SNat Nineteen
sN19 = sNineteen
sN20 :: SNat Twenty
sN20 = sTwenty
