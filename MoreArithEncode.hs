{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables, DeriveDataTypeable, DeriveGeneric, TemplateHaskell, ViewPatterns, PatternSynonyms, TypeOperators, StandaloneDeriving, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts #-}

module MoreArithEncode where

import Data.List as List

import Data.ArithEncode as AE

import Math.NumberTheory.Powers.Squares (integerSquareRoot')


--import Debug.Trace
--trace1 :: (Show a) => a -> a
--trace1 a = trace (show a) a
--trace2 :: (Show a) => String -> a -> a
--trace2 s a = trace (s ++ show a) a


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
  let
    (convertidx, decodefunc) = case (sizeval1, sizeval2) of
      (Just maxval, _) ->
        let
          threshold = ((maxval*(maxval+1)) `quot` 2)

          convertidx' idx1 idx2 =
            if idx1 + idx2 >= maxval
            then (idx1 + idx2)*maxval - idx1 - 1
            else
            let
              sumval = idx1 + idx2
              base = (((sumval + 1) * sumval)) `quot` 2
            in
              base + idx2

          newdecode num =
            if num >= threshold
            then let
              (q, r) = (num - threshold) `quotRem` maxval
              num2 = q + r + 1
              num1 = (maxval - 1) - r
              in (decode1 num1, decode2 num2)
            else
            let
              sumval = (isqrt ((8 * num) + 1) - 1) `quot` 2
              base = (((sumval + 1) * sumval)) `quot` 2
              num2 = num - base
              num1 = sumval - num2
            in
              (decode1 num1, decode2 num2)
          --convertidx' idx1 idx2 = (idx2 * maxval) + idx1
          --newdecode num = (decode1 (num `mod` maxval), decode2 (num `quot` maxval))
        in
          (convertidx', newdecode)
      (_, Just maxval) ->
        let
          convertidx' idx1 idx2 = (idx1 * maxval) + idx2
          newdecode num = (decode1 (num `quot` maxval), decode2 (num `mod` maxval))
        in
          (convertidx', newdecode)
      (Nothing, Nothing) ->
        let
          convertidx' idx1 idx2 =
            let
              sumval = idx1 + idx2
              base = (((sumval + 1) * sumval)) `quot` 2
            in
              base + idx2

          newdecode num =
            let
              sumval = (isqrt ((8 * num) + 1) - 1) `quot` 2
              base = (((sumval + 1) * sumval)) `quot` 2
              num2 = num - base
              num1 = sumval - num2
            in
              (decode1 num1, decode2 num2)
        in
          (convertidx', newdecode)

    encodefunc (val1, val2) = convertidx (encode1 val1) (encode2 val2)

    sizeval =
      do
        size1 <- sizeval1
        size2 <- sizeval2
        return (size1 * size2)
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







