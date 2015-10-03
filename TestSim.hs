{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables, DeriveDataTypeable, DeriveGeneric, TemplateHaskell, ViewPatterns, PatternSynonyms, TypeOperators, StandaloneDeriving #-}

module TestSim where

import TimeSteward1

import Control.Monad as Monad
import Control.Applicative as Applicative
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
import Test.QuickCheck.Function
import Test.QuickCheck.Gen
import Test.QuickCheck.Modifiers
import Test.QuickCheck.Random

--import InefficientFlatTimeSteward as TSI
--import FlatTimeSteward as TSI
import CrossverifiedTimeStewards as TSI

type TSI = TimeStewardInstance

-- for convenience(?), make all the fields be from the same type constructor
newtype ConcreteField phantom t = ConcreteField t
  deriving (Eq, Ord, Typeable, Generic)
unConcreteField :: ConcreteField phantom t -> t
unConcreteField (ConcreteField t) = t
instance (Serialize t) => Serialize (ConcreteField phantom t)
instance (Typeable phantom, Typeable t, Show t) => Show (ConcreteField phantom t) where
  showsPrec prec (ConcreteField t) =
    showString "CF<" . shows (typeRep (Proxy :: Proxy phantom)) .
    showString ", " . shows (typeRep (Proxy :: Proxy t)) .
    showString ">" . showsPrec prec t
instance (Eq t, Ord t, Show t, Typeable phantom, Typeable t, Serialize t, Arbitrary t) => FieldType (ConcreteField phantom t) where
  -- TODO this better
  -- maybe use https://downloads.haskell.org/~ghc/7.10.1/docs/html/users_guide/type-level-literals.html
  -- (which exists in 7.8 as well)
  -- These constants are randomly generated.
  -- I... I think I can make a phantom integer argument to ConcreteField
  -- that is randomly generated at runtime, omg. For testing.
  defaultFieldValue = ConcreteField (unGen arbitrary (mkQCGen 0x3ba19626350be65a) 100)

--pattern DFs a <- [a] where DFs a = [a,a]
-- bidirectional custom is not in ghc 7.8, only 7.10+

viewTSI :: CrossverifiedTimeStewardsInstance
                 -> (ExtendedTime,
                     EntityFields,
                     Map ExtendedTime Event,
                     [Predictor])
viewTSI tsi = (TSI.getNow tsi, TSI.getEntityFieldStates tsi,
               TSI.getFiatEvents tsi, TSI.getPredictors tsi)

pattern TSIpat now efs fiat predictors <- (viewTSI -> (now, efs, fiat, predictors))
{-  where
  TSIpat now efs fiat predictors =
    TSI.setFiatEvents fiat (TSI.makeTimeStewardInstance now efs predictors)
-}

tSIpat :: ExtendedTime
                -> EntityFields
                -> Map ExtendedTime Event
                -> [Predictor]
                -> CrossverifiedTimeStewardsInstance
tSIpat now efs fiat predictors =
    TSI.setFiatEvents fiat (TSI.makeTimeStewardInstance now efs predictors)

{-
-- add fiat events TODO
-- can't shrink here, have to use a generator
instance Arbitrary CrossverifiedTimeStewardsInstance where
  arbitrary = liftM3 TSI.makeTimeStewardInstance arbitrary arbitrary arbitrary
  shrink (TSIpat a b c d) =
    [ tSIpat a' b' c' d' | (a', b', c', d') <- shrink (a, b, c, d) ]
-}

-- not randomly distributed but maybe that's okay
-- maybe it's easier to read
-- if it's not okay, map siphash over the usually-small random ints
instance Arbitrary UInt128 where
  arbitrary = arbitrarySizedBoundedIntegral
  -- shrinkIntegral caused underflows in UInt128, which I currently have be 'error'
--  shrink = const []
  shrink = List.map fromInteger . List.filter
             (\i -> i >= toInteger (minBound :: UInt128) && i <= toInteger (maxBound :: UInt128))
           . shrink . toInteger

instance CoArbitrary UInt128 where
  coarbitrary = coarbitrary . toInteger

instance Function UInt128 where
  function = functionMap toInteger fromInteger

instance Arbitrary EntityId where --newtypederivable
  arbitrary = fmap EntityId arbitrary
  shrink (EntityId i) = fmap EntityId (shrink i)

instance CoArbitrary EntityId where --newtypederivable
  coarbitrary (EntityId i) = coarbitrary i

instance Function EntityId where --newtypederivable
  function = functionMap unEntityId EntityId

instance Arbitrary ExtendedTime where
  arbitrary = liftM3 ExtendedTime arbitrary arbitrary arbitrary
  shrink (ExtendedTime a b c) =
    [ ExtendedTime a' b' c' | (a', b', c') <- shrink (a, b, c)]

instance (Arbitrary t) => Arbitrary (ConcreteField phantom t) where
  arbitrary = fmap ConcreteField arbitrary
  shrink (ConcreteField x) = fmap ConcreteField (shrink x)

instance (CoArbitrary t) => CoArbitrary (ConcreteField phantom t) where
  coarbitrary (ConcreteField t) = coarbitrary t

instance (Function t) => Function (ConcreteField phantom t) where
  function = functionMap unConcreteField ConcreteField

--fieldify :: (FieldType (ConcreteField phantom t)) => ConcreteField phantom t -> FieldValue
--fieldify :: (Eq t, Ord t, Show t, Typeable phantom, Typeable t, Serialize t, Arbitrary t) => ConcreteField phantom t -> FieldValue
--fieldify x = FieldValue (ConcreteField x)
--ffieldify x f = fmap (FieldValue (ConcreteField x)) f

data TestFieldType where TestFieldType :: (Eq t, Ord t, Show t, Typeable phantom, Typeable t, Serialize t, Arbitrary t, CoArbitrary t, Function t) => Proxy (phantom, t) -> TestFieldType
deriving instance Show TestFieldType

testedFieldTypes :: [TestFieldType]
testedFieldTypes = [
  TestFieldType (Proxy :: Proxy ((), Integer)),
  TestFieldType (Proxy :: Proxy ((), [Integer])),
  TestFieldType (Proxy :: Proxy ((), UInt128)),
  TestFieldType (Proxy :: Proxy (Bool, UInt128)),
  TestFieldType (Proxy :: Proxy ((), ())),
  TestFieldType (Proxy :: Proxy ((), Bool))
  ]

instance Arbitrary TestFieldType where
  arbitrary = elements testedFieldTypes
  -- hmm
  shrink (TestFieldType (_::Proxy (phantom, t))) =
    if isNothing (eqT :: Maybe ((phantom, t) :~: ((), ())))
    then [TestFieldType (Proxy::Proxy ((), ()))]
    else []
    

instance Arbitrary FieldValue where
  arbitrary = oneof (fmap (\(TestFieldType (_::Proxy (phantom, t))) ->
      fmap FieldValue (arbitrary :: Gen (ConcreteField phantom t))
      --fmap (\cf -> FieldValue (cf :: ConcreteField phantom t)) arbitrary
    ) testedFieldTypes)
  shrink (FieldValue (f :: f_t)) =
    List.foldr (\(TestFieldType (_::Proxy (phantom, t))) tryNext ->
      case cast f :: Maybe (ConcreteField phantom t) of
        Nothing -> tryNext
        Just cf -> fmap FieldValue (shrink cf)) [] testedFieldTypes
    ++
    -- hmm will changing the type in it break anything else I wonder
    -- Should I shrink it to anything besides a nullish one
    if isNothing (eqT :: Maybe (f_t :~: ConcreteField () ()))
    then [FieldValue (ConcreteField () :: ConcreteField () ())]
    else []
{-
-- TODO this could be more flexible or whatever
  arbitrary = oneof [
    fmap (\x -> FieldValue (ConcreteField x :: ConcreteField () Integer)) arbitrary,
    fmap (\x -> FieldValue (ConcreteField x :: ConcreteField () [Integer])) arbitrary,
    fmap (\x -> FieldValue (ConcreteField x :: ConcreteField () UInt128)) arbitrary,
    fmap (\x -> FieldValue (ConcreteField x :: ConcreteField Bool UInt128)) arbitrary,
    fmap (\x -> FieldValue (ConcreteField x :: ConcreteField () ())) arbitrary,
    fmap (\x -> FieldValue (ConcreteField x :: ConcreteField () Bool)) arbitrary
    ]
  shrink (FieldValue (f :: f_t)) =
    case () of
      ()
        | Just (x :: ConcreteField () Integer) <- cast f -> fmap FieldValue (shrink x `asTypeOf` [x])
        | Just (x :: ConcreteField () [Integer]) <- cast f -> fmap FieldValue (shrink x `asTypeOf` [x])
        | Just (x :: ConcreteField () UInt128) <- cast f -> fmap FieldValue (shrink x `asTypeOf` [x])
        | Just (x :: ConcreteField Bool UInt128) <- cast f -> fmap FieldValue (shrink x `asTypeOf` [x])
        | Just (x :: ConcreteField () ()) <- cast f -> fmap FieldValue (shrink x `asTypeOf` [x])
        | Just (x :: ConcreteField () Bool) <- cast f -> fmap FieldValue (shrink x `asTypeOf` [x])
        | otherwise -> []
-}
  --shrink (FieldValue (f :: f_t)) =
  --case eqT :: Maybe (f_t :~: ConcreteField phantom t) of
  --  Nothing -> []
  --  Just Refl -> fmap FieldValue (shrink f)
    --case cast f of
    --Just (ConcreteField x) -> fmap (\x' -> FieldValue (ConcreteField x')) (shrink x)
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
  shrink efs = fmap initializeEntityFieldsNonuniform (shrink (getAllEntityFields efs))

-- should any of the fields of this be strict fields??
-- VRC = ValueRetrievalComputation
data VRCGenerator result where
  VRCGet :: (FieldType f, Function f, CoArbitrary f) => EntityId -> (Fun f (VRCGenerator result)) -> VRCGenerator result
  VRCGetIgnore :: (FieldType f) => EntityId -> Proxy f -> VRCGenerator result -> VRCGenerator result
  VRCResult :: result -> VRCGenerator result
deriving instance (Show result) => Show (VRCGenerator result)

instance (Arbitrary result) => Arbitrary (VRCGenerator result) where
  arbitrary = oneof $
    [
      fmap VRCResult arbitrary
    ] ++
    List.concatMap (\(TestFieldType (_::Proxy (phantom, t))) ->
        [
        liftM3 VRCGetIgnore
          arbitrary (pure (Proxy::Proxy (ConcreteField phantom t))) arbitrary,
        liftM2 VRCGet
          arbitrary (arbitrary :: Gen (Fun (ConcreteField phantom t) (VRCGenerator result)))
        ]
      ) testedFieldTypes
  shrink (VRCResult efs) = fmap VRCResult (shrink efs)
  -- TODO consider also shrink the proxy type somehow
  shrink (VRCGetIgnore entityId (proxy :: Proxy f_t) g) =
    [g] ++
    [VRCGetIgnore se proxy g | se <- shrink entityId] ++
    --hmm
    [VRCGetIgnore entityId (Proxy :: Proxy (ConcreteField () ())) g
      | isNothing (eqT :: Maybe (f_t :~: ConcreteField () ()))] ++
    [VRCGetIgnore entityId proxy sg | sg <- shrink g]
  shrink (VRCGet entityId (f_g :: Fun f (VRCGenerator result))) =
    -- is it possible to shrink a "Fun" function's argument type?
    -- to shrink the result of the function? probably at least that...
    [VRCGet se f_g | se <- shrink entityId] ++
    [VRCGetIgnore entityId (Proxy::Proxy f) (apply f_g defaultFieldValue)] ++
    [VRCGet entityId s_f_g | s_f_g <- shrink f_g]

newtype EventGenerator = EventGenerator
    (VRCGenerator [(EntityId, FieldValue)])
  deriving (Show)
-- Do I want to use GeneralizedNewtypeDeriving? I forget whether it is sound yet.
-- Probably depends on whether I'd want to use it in more than a couple places.
-- deriving (Show, Arbitrary)

instance Arbitrary EventGenerator where --newtypederivable
  arbitrary = fmap EventGenerator arbitrary
  shrink (EventGenerator g) = fmap EventGenerator (shrink g)

data PredictorGenerator = PredictorGenerator
    TestFieldType
    (Fun EntityId (VRCGenerator (Maybe (BaseTime, EventGenerator))))
  deriving (Show)

instance Arbitrary PredictorGenerator where
  arbitrary = liftM2 PredictorGenerator arbitrary arbitrary
  shrink (PredictorGenerator t f) =
    [PredictorGenerator t' f | t' <- shrink t] ++
    [PredictorGenerator t f' | f' <- shrink f]

vrcGeneratorToVRC :: forall m result. (Monad m) => ValueRetriever m -> VRCGenerator result -> m result
vrcGeneratorToVRC valueRetriever = go
  where
    go :: VRCGenerator result -> m result
    go (VRCResult result) =
      return result
    go (VRCGet entityId continuation) =
      valueRetriever entityId >>= go . apply continuation
    go (VRCGetIgnore entityId (_::Proxy f) continuation) =
      (valueRetriever entityId :: m f) >> go continuation

eventGeneratorToEvent :: EventGenerator -> Event
eventGeneratorToEvent (EventGenerator vrc) = Event (\valueRetriever ->
    vrcGeneratorToVRC valueRetriever vrc
  )

predictorGeneratorToPredictor :: PredictorGenerator -> Predictor
predictorGeneratorToPredictor
  (PredictorGenerator
    (TestFieldType (_::Proxy (phantom, t)))
    f_vrc) =
      Predictor
        (Proxy :: Proxy (ConcreteField phantom t))
        (\valueRetriever entityId ->
          liftM (fmap (fmap eventGeneratorToEvent))
            (vrcGeneratorToVRC valueRetriever (apply f_vrc entityId)))

data PristineTSIGenerator =
  PristineTSIGenerator
    ExtendedTime EntityFields (Map ExtendedTime EventGenerator) [PredictorGenerator]
  deriving (Show, Typeable, Generic)

instance Arbitrary PristineTSIGenerator where
  arbitrary = liftM4 PristineTSIGenerator arbitrary arbitrary arbitrary arbitrary
  shrink = genericShrink

pristineTSIGeneratorToTSI :: PristineTSIGenerator -> TimeStewardInstance
pristineTSIGeneratorToTSI (PristineTSIGenerator now efs fiat predictors) =
  tSIpat now efs (Map.map eventGeneratorToEvent fiat)
    (List.map predictorGeneratorToPredictor predictors)

pattern PristineWorld w <- (pristineTSIGeneratorToTSI -> w)

-- TODO have some tests with nonpristine

--newtype PristineTSI = PristineTSI TimeStewardInstance
--  deriving (Show)

--instance Arbitrary
--tSIpat

{-
data EventGenerator where
  EventGeneratorGet :: (FieldType f, Function f, CoArbitrary f) => EntityId -> (Fun f EventGenerator) -> EventGenerator
  EventGeneratorGetIgnore :: (FieldType f) => EntityId -> Proxy f -> EventGenerator -> EventGenerator
  EventGeneratorResult :: [(EntityId, FieldValue)] -> EventGenerator
deriving instance Show EventGenerator

instance Arbitrary EventGenerator where
  arbitrary = oneof $
    [
      fmap EventGeneratorResult arbitrary
    ] ++
    List.concatMap (\(TestFieldType (_::Proxy (phantom, t))) ->
        [
        liftM3 EventGeneratorGetIgnore
          arbitrary (pure (Proxy::Proxy (ConcreteField phantom t))) arbitrary,
        liftM2 EventGeneratorGet
          arbitrary (arbitrary :: Gen (Fun (ConcreteField phantom t) EventGenerator))
        ]
      ) testedFieldTypes
  shrink (EventGeneratorResult efs) = fmap EventGeneratorResult (shrink efs)
  -- TODO consider also shrink the proxy type somehow
  shrink (EventGeneratorGetIgnore entityId (proxy :: Proxy f_t) g) =
    [g] ++
    [EventGeneratorGetIgnore se proxy g | se <- shrink entityId] ++
    --hmm
    [EventGeneratorGetIgnore entityId (Proxy :: Proxy (ConcreteField () ())) g
      | isNothing (eqT :: Maybe (f_t :~: ConcreteField () ()))] ++
    [EventGeneratorGetIgnore entityId proxy sg | sg <- shrink g]
  shrink (EventGeneratorGet entityId (f_g :: Fun f EventGenerator)) =
    -- is it possible to shrink a "Fun" function's argument type?
    -- to shrink the result of the function? probably at least that...
    [EventGeneratorGet se f_g | se <- shrink entityId] ++
    [EventGeneratorGetIgnore entityId (Proxy::Proxy f) (apply f_g defaultFieldValue)] ++
    [EventGeneratorGet entityId s_f_g | s_f_g <- shrink f_g]
  --TODO more?
  -- shrink: maybe, pass defaultFieldValue instead of 
  -- Can we shrink it to an 'arbitrary' one instead?

data PredictorGenerator =PredictorGenerator proxy (Fun entityid Gen)
data PredictorGenerator where
  PredictorGeneratorGet :: (FieldType f, Function f, CoArbitrary f) => EntityId -> (Fun f PredictorGenerator) -> PredictorGenerator
  PredictorGeneratorGetIgnore :: (FieldType f) => EntityId -> Proxy f -> PredictorGenerator -> PredictorGenerator
  PredictorGeneratorResult :: Maybe (BaseTime, EventGenerator) -> PredictorGenerator
deriving instance Show EventGenerator
-}

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
prop_remakable (PristineWorld world) =
  equivalentTimeStewards
    world
    (TSI.setFiatEvents (TSI.getFiatEvents world)
      (TSI.makeTimeStewardInstance
        (TSI.getNow world)
        (TSI.getEntityFieldStates world)
        (TSI.getPredictors world)))

prop_IntermediateMoveToFutureTimeIsHarmless (Ordered times) (PristineWorld world1) =
  List.length times > 1 ==>
    equivalentTimeStewards
      (TSI.moveToFutureTime (List.last times) world1)
      (List.foldl' (\w t -> TSI.moveToFutureTime t w) world1 times)



return []  --required just before the next line so GHC typechecks the above declarations soon enough for the below line to find the above declarations
runTests :: IO Bool
runTests = $verboseCheckAll
--runTests = $quickCheckAll

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


