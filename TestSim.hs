{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables, DeriveDataTypeable, DeriveGeneric, TemplateHaskell, ViewPatterns, PatternSynonyms, TypeOperators #-}

module TestSim where

import TimeSteward1

import Control.Monad as Monad
import Data.Functor.Identity(Identity(Identity), runIdentity)
import Data.Maybe as Maybe
import Data.List as List
import Data.Map.Strict as Map
import Data.Set as Set
import Data.Ord
import Data.ByteString

import Data.Dynamic as Dynamic

import Data.Word (Word32, Word64)
-- hackage 'memory'
import Data.ByteArray.Hash (sipHash, SipKey(SipKey), SipHash(SipHash))
-- hackage 'cereal'
import Data.Serialize (Serialize, encode)
import GHC.Generics (Generic)

import Text.Printf

import Test.QuickCheck
import Test.QuickCheck.All
import Test.QuickCheck.Gen
import Test.QuickCheck.Modifiers
import Test.QuickCheck.Random

--import InefficientFlatTimeSteward as TSI
--import FlatTimeSteward as TSI
import CrossverifiedTimeStewards as TSI

type TSI = TimeStewardInstance

newtype SomeFieldType phantom t = SomeFieldType t
  deriving (Eq, Ord, Show, Typeable, Generic)
instance (Serialize t) => Serialize (SomeFieldType phantom t)
instance (Eq t, Ord t, Show t, Typeable phantom, Typeable t, Serialize t, Arbitrary t) => FieldType (SomeFieldType phantom t) where
  -- TODO this better
  -- maybe use https://downloads.haskell.org/~ghc/7.10.1/docs/html/users_guide/type-level-literals.html
  -- (which exists in 7.8 as well)
  -- These constants are randomly generated.
  -- I... I think I can make a phantom integer argument to SomeFieldType
  -- that is randomly generated at runtime, omg. For testing.
  defaultFieldValue = SomeFieldType (unGen arbitrary (mkQCGen 0x3ba19626350be65a) 0x72184e45670f84ca)

--pattern DFs a <- [a] where DFs a = [a,a]
-- bidirectional custom is not in ghc 7.8, only 7.10+

viewTSI tsi = (TSI.getNow tsi, TSI.getEntityFieldStates tsi,
               TSI.getFiatEvents tsi, TSI.getPredictors tsi)

pattern TSIpat now efs fiat predictors <- (viewTSI -> (now, efs, fiat, predictors))
{-  where
  TSIpat now efs fiat predictors =
    TSI.setFiatEvents fiat (TSI.makeTimeStewardInstance now efs predictors)
-}

tSIpat now efs fiat predictors =
    TSI.setFiatEvents fiat (TSI.makeTimeStewardInstance now efs predictors)

-- add fiat events TODO
instance Arbitrary CrossverifiedTimeStewardsInstance where
  arbitrary = liftM3 TSI.makeTimeStewardInstance arbitrary arbitrary arbitrary
  shrink (TSIpat a b c d) =
    [ tSIpat a' b' c' d' | (a', b', c', d') <- shrink (a, b, c, d) ]

-- not randomly distributed but maybe that's okay
-- maybe it's easier to read
-- if it's not okay, map siphash over the usually-small random ints
instance Arbitrary UInt128 where
  arbitrary = arbitrarySizedIntegral
  shrink = shrinkIntegral

instance Arbitrary EntityId where
  arbitrary = fmap EntityId arbitrary
  shrink (EntityId i) = fmap EntityId (shrink i)

instance Arbitrary ExtendedTime where
  arbitrary = liftM3 ExtendedTime arbitrary arbitrary arbitrary
  shrink (ExtendedTime a b c) =
    [ ExtendedTime a' b' c' | (a', b', c') <- shrink (a, b, c)]

instance (Arbitrary t) => Arbitrary (SomeFieldType phantom t) where
  arbitrary = fmap SomeFieldType arbitrary
  shrink (SomeFieldType x) = fmap SomeFieldType (shrink x)


--fieldify :: (FieldType (SomeFieldType phantom t)) => SomeFieldType phantom t -> FieldValue
--fieldify :: (Eq t, Ord t, Show t, Typeable phantom, Typeable t, Serialize t, Arbitrary t) => SomeFieldType phantom t -> FieldValue
--fieldify x = FieldValue (SomeFieldType x)
--ffieldify x f = fmap (FieldValue (SomeFieldType x)) f

-- TODO this could be more flexible or whatever
instance Arbitrary FieldValue where
  arbitrary = oneof [
    fmap (\x -> FieldValue (SomeFieldType x :: SomeFieldType () Integer)) arbitrary,
    fmap (\x -> FieldValue (SomeFieldType x :: SomeFieldType () [Integer])) arbitrary,
    fmap (\x -> FieldValue (SomeFieldType x :: SomeFieldType () UInt128)) arbitrary,
    fmap (\x -> FieldValue (SomeFieldType x :: SomeFieldType Bool UInt128)) arbitrary,
    fmap (\x -> FieldValue (SomeFieldType x :: SomeFieldType () ())) arbitrary,
    fmap (\x -> FieldValue (SomeFieldType x :: SomeFieldType () Bool)) arbitrary
    ]
  shrink (FieldValue (f :: f_t)) =
    case () of
      ()
        | Just (x :: SomeFieldType () Integer) <- cast f -> fmap FieldValue (shrink x `asTypeOf` [x])
        | Just (x :: SomeFieldType () [Integer]) <- cast f -> fmap FieldValue (shrink x `asTypeOf` [x])
        | Just (x :: SomeFieldType () UInt128) <- cast f -> fmap FieldValue (shrink x `asTypeOf` [x])
        | Just (x :: SomeFieldType Bool UInt128) <- cast f -> fmap FieldValue (shrink x `asTypeOf` [x])
        | Just (x :: SomeFieldType () ()) <- cast f -> fmap FieldValue (shrink x `asTypeOf` [x])
        | Just (x :: SomeFieldType () Bool) <- cast f -> fmap FieldValue (shrink x `asTypeOf` [x])
        | otherwise -> []
  --shrink (FieldValue (f :: f_t)) =
  --case eqT :: Maybe (f_t :~: SomeFieldType phantom t) of
  --  Nothing -> []
  --  Just Refl -> fmap FieldValue (shrink f)
    --case cast f of
    --Just (SomeFieldType x) -> fmap (\x' -> FieldValue (SomeFieldType x')) (shrink x)
    --Nothing -> []

instance (Ord k, Arbitrary k, Arbitrary v) => Arbitrary (Map k v) where
  -- are duplicate keys any concern here?
  arbitrary = fmap Map.fromList arbitrary
  -- modeled after OrderedList's shrink instance,
  -- in case it helps remove duplicates or something
  shrink = fmap Map.fromList
    . List.filter (\kvs -> let ks = fmap fst kvs in List.sort ks == ks)
    . shrink
    . Map.toList

-- or rather than Map.fromList here, we need instance Arbitrary Map?...
instance Arbitrary EntityFields where
  arbitrary = fmap (initializeEntityFields . Map.fromList) arbitrary
  --shrink =

-- See CTSI.crossverify for implementation rationales.
-- Not implementing Eq CTSI because... not sure, just a feeling.
-- Ah because there's no way to *really* check the predictors or
-- the fiat events.
equivalentTimeStewards :: TimeStewardInstance -> TimeStewardInstance -> Bool
equivalentTimeStewards a b =
  TSI.getEntityFieldStates a == TSI.getEntityFieldStates b &&
  Map.keys (TSI.getFiatEvents a) == Map.keys (TSI.getFiatEvents b) &&
  TSI.getNow a == TSI.getNow b




-- does the world's arbitrary instance need to include some moves
-- for this to test more stuff?
-- newtype PristineWorld
-- newtype LivedIn/UsedWorld
prop_remakable world =
  equivalentTimeStewards
    world
    (TSI.setFiatEvents (TSI.getFiatEvents world)
      (TSI.makeTimeStewardInstance
        (TSI.getNow world)
        (TSI.getEntityFieldStates world)
        (TSI.getPredictors world)))

prop_IntermediateMoveToFutureTimeIsHarmless (Ordered times) world1 =
  List.length times > 1 ==>
    equivalentTimeStewards
      (TSI.moveToFutureTime (List.last times) world1)
      (List.foldl' (\w t -> TSI.moveToFutureTime t w) world1 times)



return []  --required just before the next line so GHC typechecks the above declarations soon enough for the below line to find the above declarations
runTests :: IO Bool
runTests = $quickCheckAll

main :: IO ()
main = runTests >>= print

{-

Things we can test:

done: Whether different TSIs do the same thing

Whether functions I claimed are "idempotent" do actually seem to be

to quickcheck: Whether TSI.moveToFutureTime more or less frequently does a different thing (it shouldn't)
(plz include testing moves by less than a BaseTime tick)

Whether FTSI does the same thing if you do remakePrediction and/or initializePredictions
on it sporadically

to quickcheck: Also: make the test sim have some fiat events and interacting actors


non-flat:
you can read the past and change the past
it may or may not have a meaningful "now". If it doesn't, it'll be harder to test TSI.moveToFutureTime?
But there will still be one even if it's called TSI.updateToTime, there just might not be a
TSI.getNow (although it would be easy to make one anyway, but then we'd have to decide what
that meant if you changed the past: whether to change it or keep it the same).
Testing consistency with flat ones will be important as far as we can, but about testing the time
travel features... Aha, we can still do that. Compare to simpler ones traveling forward in time from
their starting point to the point at which you changed time, or such.


Random actors doing random stuff... maybe there are like seven "slots" for entities and
they do things to each other / themselves in random combinations... also generate random
numbers of predictors... and 0-3 ish number of field types...
randomly test going forward (and back) in time by random amounts...
-}


