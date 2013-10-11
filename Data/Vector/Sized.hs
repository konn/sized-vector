{-# LANGUAGE DataKinds, GADTs, MultiParamTypeClasses, PolyKinds #-}
{-# LANGUAGE StandaloneDeriving, TypeFamilies, TypeOperators    #-}
-- | Size-parameterized vector types and functions.
module Data.Vector.Sized ( Vector (..), sLength, length, append, foldr
                         , foldl, singleton, zipWith, zipWithSame, toList, fromList
                         , unsafeFromList, fromList', unsafeFromList'
                         , all, splitAt, takeAtMost, splitAtMost
                         , drop, take, map, head, tail, index) where
import Control.Applicative
import Data.Maybe
import Data.Singletons       hiding (promote)
import Data.Type.Monomorphic
import Data.Type.Natural     hiding (promote)
import Prelude               hiding (all, drop, foldl, foldr, head, length, map,
                              splitAt, tail, take, zipWith)

data Vector (a :: *) (n :: Nat)  where
  Nil  :: Vector a Z
  (:-) :: a -> Vector a n -> Vector a (S n)

infixr 5 :-

deriving instance Show a => Show (Vector a n)
instance (Eq a) => Eq (Vector a n) where
  Nil == Nil = True
  (x :- xs) == (y :- ys) = x == y && xs == ys
  _ == _ = error "impossible!"

sLength :: Vector a n -> SNat n
sLength Nil       = sZ
sLength (_ :- xs) = sS $ sLength xs

length :: Vector a n -> Int
length = sNatToInt . sLength

append :: Vector a n -> Vector a m -> Vector a (n :+: m)
append (x :- xs) ys = x :- append xs ys
append Nil       ys = ys

foldr :: (a -> b -> b) -> b -> Vector a n -> b
foldr _ b Nil       = b
foldr f a (x :- xs) = f x (foldr f a xs)

foldl :: (a -> b -> a) -> a -> Vector b n -> a
foldl _ a Nil       = a
foldl f a (b :- bs) = foldl f (f a b) bs

singleton :: a -> Vector a (S Z)
singleton = (:- Nil)

zipWithSame :: (a -> b -> c) -> Vector a n -> Vector b n -> Vector c n
zipWithSame _ Nil Nil = Nil
zipWithSame f (x :- xs) (y :- ys) = f x y :- zipWithSame f xs ys
zipWithSame _ _ _ = error "cannot happen"

zipWith :: (a -> b -> c) -> Vector a n -> Vector b m -> Vector c (Min n m)
zipWith _ Nil Nil             = Nil
zipWith _ Nil (_ :- _)        = Nil
zipWith _ (_ :- _) Nil        = Nil
zipWith f (x :- xs) (y :- ys) = f x y :- zipWith f xs ys

toList :: Vector a n -> [a]
toList = foldr (:) []

fromList :: SNat n -> [a] -> Maybe (Vector a n)
fromList SZ     _      = Just Nil
fromList (SS n) (x:xs) = (x :-) <$> fromList n xs
fromList _      _      = Nothing

unsafeFromList :: SNat n -> [a] -> Vector a n
unsafeFromList len = fromMaybe (error "Length too short") . fromList len

fromList' :: SingRep n => [a] -> Maybe (Vector a n)
fromList' = fromList sing

unsafeFromList' :: SingRep n => [a] -> Vector a n
unsafeFromList' = unsafeFromList sing

all :: (a -> Bool) -> Vector a n -> Bool
all p = foldr ((&&) . p) False

splitAt :: (n :<<= m) ~ True => SNat n -> Vector a m -> (Vector a n, Vector a (m :-: n))
splitAt SZ     xs        = (Nil, xs)
splitAt (SS n) (x :- xs) =
  case splitAt n xs of
    (xs', ys') -> (x :- xs', ys')
splitAt _ _ = error "could not happen!"

drop :: (n :<<= m) ~ True => SNat n -> Vector a m -> Vector a (m :-: n)
drop n = snd . splitAt n

take :: (n :<<= m) ~ True => SNat n -> Vector a m -> Vector a n
take SZ     _         = Nil
take (SS n) (x :- xs) = x :- take n xs
take _ _ = error "imposible!"

takeAtMost :: SNat n -> Vector a m -> Vector a (Min n m)
takeAtMost = (fst .) . splitAtMost

splitAtMost :: SNat n -> Vector a m -> (Vector a (Min n m), Vector a (m :-: n))
splitAtMost SZ Nil = (Nil, Nil)
splitAtMost SZ (x :- xs) = (Nil, x :- xs)
splitAtMost (SS _) Nil = (Nil, Nil)
splitAtMost (SS n) (x :- xs) =
  case splitAtMost n xs of
    (ys, zs) -> (x :- ys, zs)

map :: (a -> b) -> Vector a n -> Vector b n
map _ Nil       = Nil
map f (x :- xs) = f x :- map f xs

head :: Vector a (S n) -> a
head (x :- _) = x

tail :: Vector a (S n) -> Vector a n
tail (_ :- xs) = xs

index :: ((n :<<= m) ~ True) => SNat n -> Vector a (S m) -> a
index SZ     (a :- _)  = a
index (SS n) (_ :- (a :- as)) = index n (a :- as)

instance Monomorphicable (Vector a) where
  type MonomorphicRep (Vector a) = [a]
  demote (Monomorphic vec) = toList vec
  promote [] = Monomorphic Nil
  promote (x:xs) =
    case promote xs of
      Monomorphic vec -> Monomorphic $ x :- vec
