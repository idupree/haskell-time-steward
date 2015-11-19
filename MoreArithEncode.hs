{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables, DeriveDataTypeable, DeriveGeneric, TemplateHaskell, ViewPatterns, PatternSynonyms, TypeOperators, StandaloneDeriving, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, GeneralizedNewtypeDeriving #-}

module MoreArithEncode where

import Data.List as List
import Data.Set as Set
import Data.Map as Map

import Data.ArithEncode as AE

import Math.NumberTheory.Powers.Squares (integerSquareRoot')


import Control.DeepSeq
import System.IO.Unsafe
import Control.Exception
import Data.Typeable
import Debug.Trace
trace1 :: (Show a) => a -> a
trace1 a = trace (show a) a
trace2 :: (Show a) => String -> a -> a
trace2 s a = trace (s ++ show a) a

-- For testing/debugging this module:
newtype I3 = I3 Integer deriving (Eq, Ord, Typeable, Num, Real, Integral, Enum); instance Bounded I3 where {minBound = 0; maxBound = 2}; instance Show I3 where {show (I3 i) = show i}
newtype I5 = I5 Integer deriving (Eq, Ord, Typeable, Num, Real, Integral, Enum); instance Bounded I5 where {minBound = 0; maxBound = 4}; instance Show I5 where {show (I5 i) = show i}
newtype I8 = I8 Integer deriving (Eq, Ord, Typeable, Num, Real, Integral, Enum); instance Bounded I8 where {minBound = 0; maxBound = 7}; instance Show I8 where {show (I8 i) = show i}

traceEncoding :: String -> Encoding a -> Encoding a
traceEncoding s enc = mkEncoding
  (trace2 ("encode "++s) . (AE.encode enc))
  (AE.decode enc . trace2 ("decode "++s))
  (AE.size enc)
  (AE.inDomain enc)


isqrt :: Integer -> Integer
isqrt = integerSquareRoot'

{-
TODO check for overflow bugs in AE ... this session is with a version of 'enum'
that always shifts minBound to zero
*TestSim> AE.encode (AE.set (enum :: Encoding Int)) (Set.fromList [0])
0
*TestSim> AE.encode (AE.set (enum :: Encoding Int)) (Set.fromList [])
0
*TestSim> AE.encode (AE.set (enum :: Encoding Int)) (Set.fromList [1])
0
*TestSim> AE.encode (AE.set (enum :: Encoding Int)) (Set.fromList [3])
0
*TestSim> AE.encode (boundedint :: Encoding Int) (Set.fromList [3])

<interactive>:7:41:
    Couldn't match expected type ‘Int’ with actual type ‘Set a0’
    In the second argument of ‘AE.encode’, namely ‘(Set.fromList [3])’
    In the expression:
      AE.encode (boundedint :: Encoding Int) (Set.fromList [3])
*TestSim> AE.encode (boundedint :: Encoding Int) (3)
9223372036854775811
*TestSim> AE.encode (boundedint :: Encoding Word64) (3)
3
*TestSim> AE.encode (AE.set (enum :: Encoding Word64)) (Set.fromList [1])
2
*TestSim> AE.encode (AE.set (enum :: Encoding Word64)) (Set.fromList [0])
1
-}


identityUnder :: Integer -> Encoding Integer
identityUnder n = mkEncoding id id (Just n) (< n)

identityMaybeUnder :: Maybe Integer -> Encoding Integer
identityMaybeUnder Nothing = identity
identityMaybeUnder (Just n) = identityUnder n

identity0MaybeUnder :: Integer -> Encoding Integer
identity0MaybeUnder 0 = identity
identity0MaybeUnder n = identityUnder (n - 1)

testCasesForSize :: Maybe Integer -> [Integer]
testCasesForSize (Just n)
  | n == 0 = []
  | n < t1 + c2 = [0 .. n-1]
  -- | n < 2^8192 =
  | otherwise = takeWhile (< 2^8192) $
    [0 .. t1 - 1] ++ takeWhile (< t2) (iterate (\x -> x * 19 `div` 11 + 1) t1) ++ [t2 .. n-1]
  where
     t1 = 40
     c2 = 10
     t2 = n - c2
testCasesForSize Nothing =
  takeWhile (< 2^8192) $
    [0 .. t1 - 1] ++ (iterate (\x -> x * 19 `div` 11 + 1) t1)
  where
     t1 = 40

exceptionsFail :: String -> [String] -> [String]
exceptionsFail what result = unsafePerformIO $
  let io = evaluate (force result)
             `catches` [
           Handler (\(ex :: SomeAsyncException) -> throwIO ex >> io),
           Handler (\(ex :: SomeException) -> return ["Exception: " ++ what ++ ": " ++ show ex])
           ]
  in io

-- returns: list of errors
testEncoding :: (Ord a) => Encoding a -> [String]
testEncoding enc = reverse $ snd $ List.foldl' (\(seen, errs) i ->
   let
     a = AE.decode enc i
     i' = AE.encode enc a
   in (Map.insertWith (\new old -> old) a i seen,
       exceptionsFail (show i) (
         (case Map.lookup a seen of
           Nothing -> []
           Just iOther -> ["decode to the same thing: " ++ show iOther ++ ", " ++ show i]
         ) ++
         (if AE.inDomain enc a then [] else
           ["decodes to something not in domain: " ++ show i]) ++
         (if i == i' then [] else
           ["decodes to a number it didn't encode to: " ++ show i ++ " -> " ++ show i'])
       ) ++
       errs
       -- not tested: that values in the domain
       -- cover all integers, or encode without errors
       -- (because we have no good way to make values
       -- other than decode)
       )
  ) (Map.empty, []) (testCasesForSize (AE.size enc))

{-
testEncoding :: (Ord a) => Encoding a -> Bool
testEncoding enc = snd $ List.foldl' (\(seen, ok) i ->
   let a = AE.decode enc i
   in (Set.insert a seen,
       ok &&
       -- two different integers should not decode to the same thing
       Set.notMember a seen &&
       -- a decoding should be in the domain
       AE.inDomain enc a &&
       -- a decoding should encode to what it came from
       AE.encode enc a == i
       -- not tested: that values in the domain
       -- cover all integers, or encode without errors
       -- (because we have no good way to make values
       -- other than decode)
       )
  ) (Set.empty, True) (testCasesForSize (AE.size enc))
-}

testEncoding1 :: (Ord a) => (Encoding Integer -> Encoding a) -> [String]
testEncoding1 f = List.concatMap (\argsize ->
  fmap (("[" ++ show argsize ++ "]: ") ++)
       (testEncoding (f (identity0MaybeUnder argsize)))
  ) [0..6]

testEncoding2 :: (Ord a) => (Encoding Integer -> Encoding Integer -> Encoding a) -> [String]
testEncoding2 f = List.concatMap (\(argsize1, argsize2) ->
  fmap (("[" ++ show argsize1 ++ ", " ++ show argsize2 ++ "]: ") ++)
       (testEncoding (f (identity0MaybeUnder argsize1) (identity0MaybeUnder argsize2)))
  ) [(a, b) | a <- [0..4], b <- [0..4]]

testEncodingNat1 :: (Ord a) => (Integer -> Encoding Integer -> Encoding a) -> [String]
testEncodingNat1 f = List.concatMap (\(argsize1, argsize2) ->
  fmap (("[" ++ show argsize1 ++ ", " ++ show argsize2 ++ "]: ") ++)
       (testEncoding (f argsize1 (identity0MaybeUnder argsize2)))
  ) [(a, b) | a <- [0..4], b <- [0..4]]

-- Tests the "Encoding b"; the "Encoding a" is just to help generate instances
-- of the "Encoding b".
--
-- example:
--
-- testEncodingX (interleavedpair identity identity) (\(i, j) -> boundedSeq i (identity0MaybeUnder j))
testEncodingX :: (Show a, Ord b) => Encoding a -> (a -> Encoding b) -> [String]
testEncodingX argenc f = List.concatMap (\arg ->
  fmap (("[" ++ show arg ++ "]: ") ++)
       (testEncoding (f arg))
  ) (List.concatMap
      (\i -> case AE.size argenc of
        Just s | i >= s -> []
        _ -> [AE.decode argenc i])
      [0..25])

-- Takes a series of presumably normal integer encodings,
-- and turns them into encodings each of which never encode
-- to the same integer as another one, for the purposes
-- of testing "union".
testDisjointify :: [Encoding Integer] -> [Encoding Integer]
testDisjointify [] = []
testDisjointify [enc] = [enc]
testDisjointify l = let modval = List.genericLength l in modval `Prelude.seq`
  fmap (\(n, enc) ->
  AE.mkEncoding
    (\a -> case a `divMod` modval of (d, m) | m == n -> d)
    (\i -> i*modval + n)
    (AE.size enc)
    (\a -> a `mod` modval == n)
  ) (List.zip [0..] l)

altunionimpl :: [Encoding ty] -> Encoding ty
altunionimpl [] = void
altunionimpl (enc:[]) = enc
altunionimpl (enc:encs) = let
  restEnc = altunionimpl encs
  eitherEnc = AE.either enc restEnc
  --isFirst a = case (AE.inDomain enc a, AE.inDomain restEnc a) of
  in
  mkEncoding
  (\a -> if AE.inDomain enc a
         then AE.encode eitherEnc (Left a)
         else AE.encode eitherEnc (Right a))
  (\i -> case AE.decode eitherEnc i of Left a -> a; Right a -> a)
  (AE.size eitherEnc)
  (\a -> AE.inDomain enc a || AE.inDomain restEnc a)


-- Bool is common and simple so might as well make a direct, fast encoding
bool :: Encoding Bool
bool = mkEncoding encode decode (Just 2) (const True)
  where
    encode False = 0
    encode True = 1
    decode 0 = False
    decode 1 = True

--boundedencoding :: forall a. (a -> Integer) -> (Integer -> a) ->
boundedencoding :: forall a. (Bounded a) => (a -> Integer) -> (Integer -> a) -> Encoding a
boundedencoding toI fromI =
  let
    lo = toI (minBound::a)
    hi = toI (maxBound::a)
    --hiLoAbsValDisparity = abs lo - abs hi
    minAbsHiLoVal = min (abs lo) (abs hi)
    --valsWithinMinAbsHiLoVal = minAbsHiLoVal*2 + 1
    count = (hi - lo + 1)
  in
  if lo > -10
  then --start at minBound corresponding to 0
   AE.mkEncoding
   (\a -> toI a - lo)
   (\i -> fromI (i + lo))
   (Just count)
   (const True)
  else if hi < 10
  then -- go backwards
   AE.mkEncoding
   (\a -> hi - toI a)
   (\i -> fromI (hi - i))
   (Just count)
   (const True)
  else -- includes zero, high pos, high neg: better to interleave
   AE.mkEncoding
   (\(toI -> a) -> if abs a <= minAbsHiLoVal
     then (if a <= 0 then -a * 2 else a*2 - 1)
     else (abs a + minAbsHiLoVal)
     --(abs a - minAbsHiLoVal) + (valsWithinMinAbsHiLoVal - 1)
   )
   (\i -> fromI (if abs i < minAbsHiLoVal*2 + 1
     then (if even i then -i `div` 2 else (i+1) `div` 2)
     else (if abs lo < abs hi then (i - minAbsHiLoVal)
                              else negate (i - minAbsHiLoVal))
   ))
   (Just count)
   (const True)



boundedint :: forall a. (Bounded a, Integral a) => Encoding a
boundedint = boundedencoding toInteger fromInteger
--boundedint = AE.mkEncoding
--  (\a -> toInteger a - toInteger (minBound :: a))
--  (\i -> fromInteger (i + toInteger (minBound::a)))
--  (Just (toInteger (maxBound::a) - toInteger (minBound::a) + 1))
--  (const True)

enum :: forall a. (Bounded a, Enum a, Eq a) => Encoding a
enum = if
  toEnum (fromEnum (minBound::a)) /= (minBound::a) ||
  toEnum (fromEnum (maxBound::a)) /= (maxBound::a)
  then
    error "enum does not roundtrip its bounds through Int. Maybe you can use 'boundedint'?"
  else
    boundedencoding (toInteger . fromEnum) (toEnum . fromInteger)
{- AE.mkEncoding
  (\a -> toI a - toI (minBound :: a))
  (\i -> fromI (i + toI (minBound::a)))
  (Just (toI (maxBound::a) - toI (minBound::a) + 1))
  (const True)
  where
  toI = toInteger . fromEnum
  fromI = toEnum . fromInteger-}

wraptotal :: (a -> b)
     -- ^ The forward encoding function.
     -> (b -> a)
     -- ^ The reverse encoding function.
     -> Encoding b
     -- ^ The inner encoding.
     -> Encoding a
wraptotal fwd rev enc = AE.wrap (Just . fwd) (Just . rev) enc


encEncode = AE.encode
encDecode = AE.decode
encInDomain = AE.inDomain
encSize = AE.size

newtype OrderedSize = OrderedSize { unOrderedSize :: (Maybe Integer) }
  deriving (Eq)
-- alternately, OrderedSize = Down (Maybe (Down Integer))
-- with Down = Data.Ord.Down
instance Ord OrderedSize where
  compare (OrderedSize (Just a)) (OrderedSize (Just b)) = compare a b
  compare (OrderedSize Nothing) (OrderedSize Nothing) = EQ
  compare (OrderedSize (Just _)) (OrderedSize Nothing) = LT
  compare (OrderedSize Nothing) (OrderedSize (Just _)) = GT
{-
instance Num OrderedSize where
  fromInteger i = if i >= 0
    then OrderedSize (Just i)
    else error "OrderedSize should be nonnegative"
  OrderedSize a + OrderedSize b = OrderedSize ((+) <$> a <*> b)
  OrderedSize a * OrderedSize b = OrderedSize ((*) <$> a <*> b)
  OrderedSize a - OrderedSize b = case (a, b) of
    (Nothing, Nothing) -> error "Inf - Inf is undefined"
    (Just _, Nothing) -> error "finite - Inf is not a size"
    (Nothing, Just _) -> OrderedSize Nothing
    (Just a, Just b)
      | a >= b -> OrderedSize (Just (a - b))
      | otherwise -> error "a - b | a < b shouldn't be a size"
  abs (OrderedSize a) = OrderedSize (fmap abs a)
  negate o@(OrderedSize (Just 0)) = o
  negate _ = error "negate: OrderedSize should be nonnegative"
  signum (OrderedSize Nothing) = OrderedSize (Just 1)
  signum (OrderedSize (Just a)) = OrderedSize (Just (signum a))
-}

compareToSize :: Integer -> Maybe Integer -> a -> (Integer -> a) -> a
compareToSize i sz sizeIsGreater sizeIsLE = case sz of
  Nothing -> sizeIsGreater
  Just s -> if s <= i then sizeIsLE s else sizeIsGreater

compareToOSize :: Integer -> OrderedSize -> a -> (Integer -> a) -> a
compareToOSize i (OrderedSize sz) = compareToSize i sz

triangleSize :: Integer -> Integer
triangleSize width = ((width*(width+1)) `quot` 2)
-- triangleWidth rounds down - it returns the width of
-- the largest complete triangle you can make with 'sz'
-- number of items.
triangleWidth :: Integer -> Integer
triangleWidth sz = (isqrt ((8 * sz) + 1) - 1) `quot` 2

mkInterleavedPairCore :: Encoding ty1 -> Encoding ty2 ->
              ((ty1, ty2) -> Integer, Integer -> (ty1, ty2), Maybe Integer)
mkInterleavedPairCore e1 e2 =
  let
    encode1 = encEncode e1
    decode1 = encDecode e1
    sizeval1 = encSize e1
    encode2 = encEncode e2
    decode2 = encDecode e2
    sizeval2 = encSize e2
           --Encoding { encEncode = encode1, encDecode = decode1,
           --           encSize = sizeval1 }
           --Encoding { encEncode = encode2, encDecode = decode2,
           --           encSize = sizeval2 } =
  in
  if sizeval1 == Just 0 || sizeval2 == Just 0
  then (
    \_ -> error "void pair encoding",
    \_ -> error "void pair decoding",
    Just 0
    )
  else
  let
    sizeval =
      do
        size1 <- sizeval1
        size2 <- sizeval2
        return (size1 * size2)

    osizeval1 = OrderedSize sizeval1
    osizeval2 = OrderedSize sizeval2
    osizeval = OrderedSize sizeval
    ominsizeval = min osizeval1 osizeval2
    omaxsizeval = max osizeval1 osizeval2
    --osizesumval = osizeval1 + osizeval2

    --oj = OrderedSize . Just
    --uo = unOrderedSize

    -- threshold1: where the shape of the progression
    -- turns from a triangle into a parallelogram.
    -- Exists (finite) if either encoding is finite.
    --
    -- threshold2: where the parallelogram turns into
    -- another triangle. Exists (finite) if both encodings
    -- are finite.
    threshold1 = fmap triangleSize (unOrderedSize ominsizeval)
    threshold2 = (-) <$> sizeval <*> threshold1
    othreshold2 = OrderedSize threshold2

    convertidx idx1 idx2 =
      let
        sumval = idx1 + idx2
      in
      compareToOSize sumval ominsizeval
      (triangleSize sumval + idx2) $
      \iminsizeval ->
      let Just ithreshold1 = threshold1 in
      compareToOSize sumval omaxsizeval
      (
      sumval*iminsizeval
      + (if osizeval1 < osizeval2 then
         let Just isizeval1 = sizeval1 in
         isizeval1 - 1 - idx1
         else idx2)
      - (iminsizeval*iminsizeval - ithreshold1)
      ) $
      \imaxsizeval -> let
      Just isizeval1 = sizeval1
      Just isizeval2 = sizeval2
      isizesumval = isizeval1 + isizeval2
      isizeval = isizeval1 * isizeval2
      in
      isizeval - 1 - (triangleSize (isizesumval - 2 - sumval) + (isizeval2 - 1 - idx2))

    decodefunc num =
      compareToSize num threshold1
      (let
        sumval = triangleWidth num
        num2 = num - triangleSize sumval
        num1 = sumval - num2
        in (decode1 num1, decode2 num2)) $
      \ithreshold1 ->
      let Just iminsizeval = unOrderedSize ominsizeval in
      compareToSize num threshold2
      (let
        (q, r) = (num - ithreshold1) `quotRem` iminsizeval
        firstIsShorter = osizeval1 < osizeval2
        num1 = (if firstIsShorter then 0 else q+1) + (iminsizeval - 1) - r
        num2 = (if firstIsShorter then q+1 else 0) + r
        in (decode1 num1, decode2 num2)) $
      \ithreshold2 ->
      let
      Just isizeval1 = sizeval1
      Just isizeval2 = sizeval2
      isizesumval = isizeval1 + isizeval2
      isizeval = isizeval1 * isizeval2
      antiNum = isizeval - 1 - num
      antiSumval = triangleWidth antiNum
      antiNum2 = antiNum - triangleSize antiSumval
      antiNum1 = antiSumval - antiNum2
      num1 = isizeval1 - 1 - antiNum1
      num2 = isizeval2 - 1 - antiNum2
      in (decode1 num1, decode2 num2)

    encodefunc (val1, val2) = convertidx (encode1 val1) (encode2 val2)

  in
    (encodefunc, decodefunc, sizeval)

-- | Take encodings for two datatypes A and B, and build an encoding
-- for a pair (A, B).
interleavedpair :: Encoding ty1 -> Encoding ty2 -> Encoding (ty1, ty2)
interleavedpair enc1 -- @ Encoding { encInDomain = indomain1 }
     enc2 = -- @ Encoding { encInDomain = indomain2 } =
  let
    indomain1 = encInDomain enc1
    indomain2 = encInDomain enc2
    (encodefunc, decodefunc, sizeval) = mkInterleavedPairCore enc1 enc2

    indomainfunc (val1, val2) = indomain1 val1 && indomain2 val2
  in
    mkEncoding encodefunc decodefunc sizeval indomainfunc
    --Encoding { encEncode = encodefunc, encDecode = decodefunc,
    --           encSize = sizeval, encInDomain = indomainfunc }

--interleavedPairishList :: Encoding ty -> Encoding ty -> Encoding [ty]

interleavedtriple :: Encoding ty1 -> Encoding ty2 -> Encoding ty3 ->
                     Encoding (ty1, ty2, ty3)
interleavedtriple enc1 enc2 enc3 =
  wraptotal
  (\(val1, val2, val3) -> ((val1, val2), val3))
  (\((val1, val2), val3) -> (val1, val2, val3))
  (interleavedpair (interleavedpair enc1 enc2) enc3)
{-
  let
    fwdshuffle (val1, val2, val3) = ((val1, val2), val3)
    revshuffle ((val1, val2), val3) = (val1, val2, val3)

    --Encoding { encEncode = encodefunc, encDecode = decodefunc,
    --           encSize = sizeval, encInDomain = indomainfunc } =
    enc =
      interleavedpair (interleavedpair enc1 enc2) enc3

    newencode = AE.encode enc . fwdshuffle
    newdecode = revshuffle . AE.decode enc
    newindomain = AE.inDomain enc . fwdshuffle
    sizeval = AE.size enc
  in
    mkEncoding newencode newdecode sizeval newindomain
    --Encoding { encEncode = newencode, encDecode = newdecode,
    --           encSize = sizeval, encInDomain = newindomain }
-}

interleavedquad :: Encoding ty1 -> Encoding ty2 ->
                   Encoding ty3 -> Encoding ty4 ->
                   Encoding (ty1, ty2, ty3, ty4)
interleavedquad enc1 enc2 enc3 enc4 =
  wraptotal
  (\(val1, val2, val3, val4) -> (((val1, val2), val3), val4))
  (\(((val1, val2), val3), val4) -> (val1, val2, val3, val4))
  (interleavedpair (interleavedpair (interleavedpair enc1 enc2) enc3) enc4)


interleavedTuplishList :: [Encoding ty] -> Encoding [ty]
interleavedTuplishList [] = AE.mkEncoding (\[] -> 0) (\0 -> []) (Just 1) (List.null)
interleavedTuplishList (enc:[]) = AE.mkEncoding
  (\(x:[]) -> AE.encode enc x)
  (\i -> AE.decode enc i : [])
  (AE.size enc)
  (\xs -> case xs of (x:[]) -> AE.inDomain enc x; _ -> False)
interleavedTuplishList (enc1:encs) = let
  encAsPair = interleavedpair enc1 (interleavedTuplishList encs)
  in -- wraptotal (\(x:xs) -> (x, xs)) (\(x, xs) -> (x:xs)) encAsPair
  mkEncoding
  (\(x:xs) -> AE.encode encAsPair (x, xs))
  (\i -> case AE.decode encAsPair i of (x, xs) -> (x:xs))
  (AE.size encAsPair)
  (\xs_ -> case xs_ of (x:xs) -> AE.inDomain encAsPair (x, xs); [] -> False)


--HACK so it doesn't compute integer sizes that don't fit in memory,
-- such as the number of possible 'Map UInt128 Bool'.
-- The cost of the hack is sometimes decoding will lead to an error...
-- particularly since I unfortunately have to apply pretendinfinite to the
-- key type in order to prevent computing the too-large number.
pretendinfinite :: Encoding ty -> Encoding ty
pretendinfinite enc = mkInfEncoding (AE.encode enc) (AE.decode enc) (AE.inDomain enc)

pretendInfiniteIfMoreThan :: Integer -> Encoding ty -> Encoding ty
pretendInfiniteIfMoreThan i enc =
  case AE.size enc of
    Just s | s > i -> pretendinfinite enc
    -- otherwise, small enough, or no need to pretend
    _ -> enc







