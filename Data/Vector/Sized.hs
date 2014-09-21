{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds, GADTs, MultiParamTypeClasses, PolyKinds    #-}
{-# LANGUAGE ScopedTypeVariables, StandaloneDeriving, TypeFamilies #-}
{-# LANGUAGE TypeOperators, NoImplicitPrelude                      #-}
-- | Size-parameterized vector types and functions.
module Data.Vector.Sized ( -- * Vectors and indices
                           Vector (..), Index,
                           -- ** Re-exports
                           module Data.Type.Ordinal,
                           -- * Conversion & Construction
                           replicate, replicate', singleton, uncons,
                           -- ** List
                           fromList, fromList', unsafeFromList, unsafeFromList', toList,
                           -- * Basic functions
                           append, head, last, tail, init, null, length, sLength,
                           -- * Vector transformations
                           map, reverse, intersperse, transpose,
                           -- * Reducing vectors (folds)
                           foldl, foldl', foldl1, foldl1', foldr, foldr1,
                           -- ** Special folds
                           concat, and, or, any, all, sum, product, maximum, minimum,
                           -- * Subvectors
                           -- ** Extracting subvectors
                           take, takeAtMost, drop, splitAt, splitAtMost, stripPrefix,
                           -- * Searching vectors
                           -- ** Searching by equality
                           elem, notElem,
                           -- ** Searching with a predicate
                           find,
                           -- * Indexing vectors
                           (!!), (%!!), index, sIndex, elemIndex, sElemIndex
                         , findIndex, sFindIndex, findIndices, sFindIndices
                         , elemIndices, sElemIndices,
                           -- * Zipping vectors
                           zip, zipSame, zipWith, zipWithSame, unzip
                         ) where
import           Control.Applicative
import           Control.DeepSeq
import           Data.Hashable
import           Data.Maybe
import           Data.Type.Monomorphic
import           Data.Type.Natural     hiding (promote)
import           Data.Type.Ordinal
import qualified Prelude               as P
import           Prelude               (Eq(..), Bool(..), Int, Show(..), (&&), Num(..)
                                       , (||), not, error, ($), (.), seq, fst, snd
                                       , flip, otherwise)
import           Proof.Equational      hiding (promote)

-- | Fixed-length list.
data Vector (a :: *) (n :: Nat)  where
  Nil  :: Vector a Z
  (:-) :: a -> Vector a n -> Vector a (S n)

infixr 5 :-

-- | Type synonym for @Ordinal@.
type Index = Ordinal

-- | Monomorphic representation of 'Vector' @a n@ is @[a]@.
instance Monomorphicable (Vector a) where
  type MonomorphicRep (Vector a) = [a]
  demote (Monomorphic vec) = toList vec
  promote [] = Monomorphic Nil
  promote (x:xs) =
    case promote xs of
      Monomorphic vec -> Monomorphic $ x :- vec

deriving instance Show a => Show (Vector a n)
deriving instance P.Ord a => P.Ord (Vector a n)
instance (Eq a) => Eq (Vector a n) where
  Nil == Nil = True
  (x :- xs) == (y :- ys) = x == y && xs == ys
  _ == _ = error "impossible!"

--------------------------------------------------
-- Conversion & Construction
--------------------------------------------------

-- | 'replicate' @n x@ is a vector of length @n@ with @x@ the value of every element.
replicate :: SNat n -> a -> Vector a n
replicate SZ _ = Nil
replicate (SS n) a = a :- replicate n a

-- | 'replicate', with the length inferred.
replicate' :: forall n a. SingI n => a -> Vector a n
replicate' = replicate (sing :: SNat n)

-- | Construct a singleton vector.
singleton :: a -> Vector a (S Z)
singleton = (:- Nil)

-- | Uncons the non-empty list.
uncons :: Vector a (S n) -> (a, Vector a n)
uncons (a :- as) = (a, as)

-- | Convert a list into a vector.
-- If a given list is shorter than the length, it returns @Nothing@.
fromList :: SNat n -> [a] -> Maybe (Vector a n)
fromList SZ     _      = Just Nil
fromList (SS n) (x:xs) = (x :-) <$> fromList n xs
fromList _      _      = Nothing

-- | Unsafe version of 'fromList'.
-- If a given list is shorter than the length, it aborts.
unsafeFromList :: SNat n -> [a] -> Vector a n
unsafeFromList len = fromMaybe (error "Length too short") . fromList len

-- | Convert a list into vector, with length inferred.
fromList' :: SingI n => [a] -> Maybe (Vector a n)
fromList' = fromList sing

-- | Unsafe version of 'unsafeFromList'.
unsafeFromList' :: SingI n => [a] -> Vector a n
unsafeFromList' = unsafeFromList sing

-- | Convert a vector into a list.
toList :: Vector a n -> [a]
toList = foldr (:) []

--------------------------------------------------
-- Basic Functions
--------------------------------------------------

-- | Append two @Vector@s.
append :: Vector a n -> Vector a m -> Vector a (n :+: m)
append (x :- xs) ys = x :- append xs ys
append Nil       ys = ys

-- | Extract the first element of a non-empty vector.
head :: Vector a (S n) -> a
head (x :- _) = x

-- | Extract the last element of a non-empty vector.
last :: Vector a (S n) -> a
last (x :- Nil) = x
last (_ :- xs@(_ :- _)) = last xs

-- | Extract the elements after the head of a non-empty list.
tail :: Vector a (S n) -> Vector a n
tail (_ :- xs) = xs

-- | Extract the elements before the last of a non-empty list.
init :: Vector a (S n) -> Vector a n
init (a :- as) =
  case as of
    Nil    -> Nil
    _ :- _ -> a :- init as

-- | Test whether a @Vector@ is empty, though it's clear from the type parameter.
null :: Vector a n -> Bool
null Nil = True
null _   = False

-- | 'length' returns the length of a finite list as an 'Int'.
length :: Vector a n -> Int
length = sNatToInt . sLength

-- | 'sLength' returns the length of a finite list as a 'SNat' @n@.
sLength :: Vector a n -> SNat n
sLength Nil       = sZ
sLength (_ :- xs) = sS $ sLength xs

--------------------------------------------------
-- Vector transformations
--------------------------------------------------

-- | 'map' @f xs@ is the vector obtained by applying @f@ to each element of xs.
map :: (a -> b) -> Vector a n -> Vector b n
map _ Nil       = Nil
map f (x :- xs) = f x :- map f xs

-- | 'reverse' @xs@ returns the elements of xs in reverse order. @xs@ must be finite.
reverse :: forall a n. Vector a n -> Vector a n
reverse xs0 = coerce (plusZR (sLength xs0)) $ go Nil xs0
  where
    go :: Vector a m -> Vector a k -> Vector a (k :+ m)
    go acc Nil = acc
    go acc (x :- xs) = coerce (symmetry $ plusSR (sLength xs) (sLength acc)) $ go (x:- acc) xs
         
-- | The 'intersperse' function takes an element and a vector and
-- \`intersperses\' that element between the elements of the vector.
intersperse :: a -> Vector a n -> Vector a ((Two :* n) :- One)
intersperse _ Nil = Nil
intersperse a (x :- xs) =
  coerce (plusSR (sLength xs) (sLength xs)) $ x :- prependToAll a xs

prependToAll :: a -> Vector a n -> Vector a (Two :* n)
prependToAll _ Nil = Nil
prependToAll a (x :- xs) =
  x :- (coerce (plusSR (sLength xs) (sLength xs)) $ a :- prependToAll a xs)

-- | The 'transpose' function transposes the rows and columns of its argument.
transpose :: SingI n => Vector (Vector a n) m -> Vector (Vector a m) n
transpose Nil = replicate' Nil
transpose (Nil :- _) = Nil
transpose ((x :- xs) :- xss) =
    case singInstance (sLength xs) of
      SingInstance -> (x :- map head xss) :- transpose (xs :- map tail xss)

--------------------------------------------------
-- Reducing vectors (folds)
--------------------------------------------------

-- | Left fold.
foldl :: (a -> b -> a) -> a -> Vector b n -> a
foldl _ a Nil       = a
foldl f a (b :- bs) = foldl f (f a b) bs

-- | A strict version of 'foldl'.
foldl' :: forall a b n. (a -> b -> a) -> a -> Vector b n -> a
foldl' f z0 xs0 = lgo z0 xs0
  where
    lgo :: a -> Vector b m -> a
    lgo z Nil = z
    lgo z (x :- xs) = let z' = f z x in z' `seq` lgo z' xs

-- | Left fold for non-empty vector.
foldl1 :: (a -> a -> a) -> Vector a (S n) -> a
foldl1 f (a :- as) = foldl f a as

-- | A strict version of 'foldl1'.
foldl1' :: (a -> a -> a) -> Vector a (S n) -> a
foldl1' f (a :- as) = foldl' f a as

-- | Right fold.
foldr :: (a -> b -> b) -> b -> Vector a n -> b
foldr _ b Nil       = b
foldr f a (x :- xs) = f x (foldr f a xs)

-- | Right fold for non-empty vector.
foldr1 :: (a -> a -> a) -> Vector a (S n) -> a
foldr1 _ (x :- Nil) = x
foldr1 f (x :- xs@(_ :- _)) = f x (foldr1 f xs)

-- | The function 'concat' concatenates all vectors in th vector.
concat :: Vector (Vector a n) m -> Vector a (m :*: n)
concat Nil = Nil
concat (xs :- xss) =
  let n = sLength xs
      n0 = sLength xss
  in coerce (symmetry $ plusCommutative (n0 %* n) n) $ xs `append` concat xss

and, or :: Vector Bool m -> Bool
-- | 'and' returns the conjunction of a Boolean vector.
and = foldr (&&) True

-- | 'or' returns the disjunction of a Boolean vector.
or  = foldr (||) False

any, all :: (a -> Bool) -> Vector a n -> Bool
-- | Applied to a predicate and a list, 'any' determines if any element of the vector satisfies the predicate. 
any p = or . map p
-- | Applied to a predicate and a list, 'all' determines if all element of the vector satisfies the predicate. 
all p = and . map p

sum, product :: P.Num a => Vector a n -> a
sum = foldr (+) 0
product = foldr (*) 1

maximum, minimum :: P.Ord a => Vector a (S n) -> a
maximum = foldr1 P.max
minimum = foldr1 P.min

--------------------------------------------------
-- Subvectors
--------------------------------------------------

-- | 'take' @n xs@ returns the prefix of @xs@ of length @n@,
-- with @n@ less than or equal to the length of @xs@.
take :: (n :<<= m) ~ True => SNat n -> Vector a m -> Vector a n
take SZ     _         = Nil
take (SS n) (x :- xs) = x :- take n xs
take _ _ = error "imposible!"

-- | A variant of @take@ which returns entire @xs@ if @n@ is greater than the length of @xs@.
takeAtMost :: SNat n -> Vector a m -> Vector a (Min n m)
takeAtMost = (fst .) . splitAtMost

-- | 'drop' @n xs@ returns the suffix of @xs@ after the first @n@ elements,
-- with @n@ less than or equal to the length of @xs@.
drop :: (n :<<= m) ~ True => SNat n -> Vector a m -> Vector a (m :-: n)
drop n = snd . splitAt n

-- | 'splitAt' @n xs@ returns a tuple where first element is @xs@ prefix of length @n@
-- and second element is the remainder of the list. @n@ should be less than or equal to the length of @xs@.
splitAt :: (n :<<= m) ~ True => SNat n -> Vector a m -> (Vector a n, Vector a (m :-: n))
splitAt SZ     xs        = (Nil, xs)
splitAt (SS n) (x :- xs) =
  case splitAt n xs of
    (xs', ys') -> (x :- xs', ys')
splitAt _ _ = error "could not happen!"

-- | A varian of 'splitAt' which allows @n@ to be greater than the length of @xs@.
splitAtMost :: SNat n -> Vector a m -> (Vector a (Min n m), Vector a (m :-: n))
splitAtMost SZ Nil = (Nil, Nil)
splitAtMost SZ (x :- xs) = (Nil, x :- xs)
splitAtMost (SS _) Nil = (Nil, Nil)
splitAtMost (SS n) (x :- xs) =
  case splitAtMost n xs of
    (ys, zs) -> (x :- ys, zs)

-- | The 'stripPrefix' function drops the given prefix from a vector.
-- It returns @Nothing@ if the vector did not start with the prefix given or shorter than the prefix,
-- or Just the vector after the prefix, if it does.
stripPrefix :: Eq a => Vector a n -> Vector a m -> Maybe (Vector a (m :- n))
stripPrefix Nil ys = Just ys
stripPrefix (_ :- _) Nil = Nothing
stripPrefix (x :- xs) (y :- ys)
    | x == y    = stripPrefix xs ys
    | otherwise = Nothing

--------------------------------------------------
-- Searching vectors
--------------------------------------------------

elem, notElem :: Eq a => a -> Vector a n -> Bool
elem a = any (== a)
notElem a = all (/= a)

find :: (a -> Bool) -> Vector a n -> Maybe a
find _ Nil = Nothing
find p (x :- xs)
    | p x       = Just x
    | otherwise = find p xs

--------------------------------------------------
-- Indexing vectors
--------------------------------------------------

-- | List index (subscript) operator, starting from @sZero@.
(!!) ::  ((n :<<= m) ~ True) => Vector a (S m) -> SNat n -> a
(!!) = flip index

-- | A 'Index' version of '!!'.
(%!!) :: Vector a n -> Index n -> a
(%!!) = flip sIndex

-- | Flipped version of '!!'.
index :: ((n :<<= m) ~ True) => SNat n -> Vector a (S m) -> a
index SZ     (a :- _)  = a
index (SS n) (_ :- (a :- as)) = index n (a :- as)

-- | A 'Index' version of 'index'.
sIndex :: Index n -> Vector a n -> a
sIndex OZ (x :- _) = x
sIndex (OS n) (_ :- xs) = sIndex n xs

-- | The 'elemIndex' function returns the index (as 'Int') of the first element in the given list
-- which is equal (by '==') to the query element, or Nothing if there is no such element.
elemIndex :: Eq a => a -> Vector a n -> Maybe Int
elemIndex a = findIndex (== a)

-- | 'Index' version of 'elemIndex'.
sElemIndex :: Eq a => a -> Vector a n -> Maybe (Index n)
sElemIndex a = sFindIndex (== a)

-- | The 'elemIndices' function extends 'elemIndex', by returning the indices of all elements equal to the query element,
-- in ascending order.
elemIndices :: Eq a => a -> Vector a n -> [Int]
elemIndices a = findIndices (== a)

-- | 'Index' version of 'elemIndices'.
sElemIndices :: Eq a => a -> Vector a n -> [Index n]
sElemIndices a = sFindIndices (== a)

-- | The findIndex function takes a predicate and a vector
-- and returns the index of the first element in the vector
-- satisfying the predicate, or Nothing if there is no such element.
findIndex :: (a -> Bool) -> Vector a n -> Maybe Int
findIndex p = listToMaybe . findIndices p

-- | 'Index' version of 'findIndex'.
sFindIndex :: (a -> Bool) -> Vector a n -> Maybe (Index n)
sFindIndex p = listToMaybe . sFindIndices p

-- | The 'findIndices' function extends 'findIndex', by returning the indices of all elements satisfying the predicate,
--  in ascending order.
findIndices :: (a -> Bool) -> Vector a n -> [Int]
findIndices p = P.map ordToInt . sFindIndices p

-- | 'Index' version of 'findIndices'.
sFindIndices :: (a -> Bool) -> Vector a n -> [Index n]
sFindIndices _ Nil = []
sFindIndices p (x :- xs)
  | p x       = OZ : P.map OS (sFindIndices p xs)
  | otherwise = P.map OS $ sFindIndices p xs

--------------------------------------------------
-- Zipping vectors
--------------------------------------------------

-- | 'zip' takes two vectors and returns a vector of corresponding pairs.
--  If one input list is short, excess elements of the longer list are discarded.
zip :: Vector a n -> Vector b m  -> Vector (a, b) (Min n m)
zip = zipWith (,)

-- | Same as 'zip', but the given vectors must have the same length.
zipSame :: Vector a n -> Vector b n -> Vector (a, b) n
zipSame = zipWithSame (,)

-- | 'zipWith' generalises 'zip' by zipping with the function given as the first argument, instead of a tupling function.
zipWith :: (a -> b -> c) -> Vector a n -> Vector b m -> Vector c (Min n m)
zipWith _ Nil Nil             = Nil
zipWith _ Nil (_ :- _)        = Nil
zipWith _ (_ :- _) Nil        = Nil
zipWith f (x :- xs) (y :- ys) = f x y :- zipWith f xs ys

-- | Same as 'zipWith', but the given vectors must have the same length.
zipWithSame :: (a -> b -> c) -> Vector a n -> Vector b n -> Vector c n
zipWithSame _ Nil Nil = Nil
zipWithSame f (x :- xs) (y :- ys) = f x y :- zipWithSame f xs ys
zipWithSame _ _ _ = error "cannot happen"

-- | Inverse of 'zipSame'.
unzip :: Vector (a, b) n -> (Vector a n, Vector b n)
unzip Nil = (Nil, Nil)
unzip ((a, b) :- ps) =
  let (as, bs) = unzip ps
  in (a :- as, b :- bs)

instance NFData a => NFData (Vector a n) where
  rnf = rnfVector

rnfVector :: NFData a => Vector a n -> ()
rnfVector Nil = Nil `seq` ()
rnfVector (x :- xs) = rnf x `seq` rnf xs `seq` ()

vecHashWithSalt :: Hashable a => Int -> Vector a n -> Int
vecHashWithSalt salt Nil = salt `hashWithSalt` (0 :: Int)
vecHashWithSalt salt xs  = foldl hashWithSalt salt xs

instance Hashable a => Hashable (Vector a n) where
  hash Nil = 0
  hash (a :- as) = foldl hashWithSalt (hash a) as
  hashWithSalt   = vecHashWithSalt

ordinalVecs :: SNat n -> Vector (Ordinal n) n
ordinalVecs SZ      = Nil
ordinalVecs (SS sn) = OZ :- map OS (ordinalVecs sn)

ifoldl :: (a -> Index n -> b -> a) -> a -> Vector b n -> a
ifoldl fun a0 vs = foldl (\a (b, c) -> fun a b c) a0 $ zipSame (ordinalVecs $ sLength vs) vs
