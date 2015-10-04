{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables, DeriveDataTypeable, DeriveGeneric, TemplateHaskell, ViewPatterns, PatternSynonyms, TypeOperators, StandaloneDeriving, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts #-}

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

-- hackage tasty
import Test.Tasty
-- hackage tasty-smallcheck
import Test.Tasty.SmallCheck as SC
-- hackage tasty-quickcheck
import Test.Tasty.QuickCheck as QC


-- hackage QuickCheck
import Test.QuickCheck as QC
import Test.QuickCheck.All as QC
import Test.QuickCheck.Function as QC
import Test.QuickCheck.Gen as QC
import Test.QuickCheck.Modifiers as QC
import Test.QuickCheck.Random as QC
-- hackage quickcheck-instances
import Test.QuickCheck.Instances

-- hackage smallcheck
import Test.SmallCheck as SC
import Test.SmallCheck.Series as SC
import Test.SmallCheck.Drivers as SC
-- hackage smallcheck-series:
import Test.SmallCheck.Series.Instances

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

instance (Monad m) => Serial m UInt128 where
  --series = fmap (fromInteger . (0x1000 +) . SC.getNonNegative) series
  series = fmap (fromInteger . SC.getNonNegative) series
instance (Monad m) => CoSerial m UInt128 where
  coseries rs = fmap (. toInteger) (coseries rs)

instance Arbitrary EntityId where --newtypederivable
  arbitrary = fmap EntityId arbitrary
  shrink (EntityId i) = fmap EntityId (shrink i)

instance CoArbitrary EntityId where --newtypederivable
  coarbitrary (EntityId i) = coarbitrary i

instance Function EntityId where --newtypederivable
  function = functionMap unEntityId EntityId

instance (Monad m) => Serial m EntityId where --newtypederivable? genericable
  series = fmap EntityId series
instance (Monad m) => CoSerial m EntityId where --newtypederivable? genericable
  coseries rs = fmap (. unEntityId) (coseries rs)


instance Arbitrary ExtendedTime where
  arbitrary = liftM3 ExtendedTime arbitrary arbitrary arbitrary
  shrink (ExtendedTime a b c) =
    [ ExtendedTime a' b' c' | (a', b', c') <- shrink (a, b, c)]

instance CoArbitrary ExtendedTime where
  coarbitrary (ExtendedTime a b c) = coarbitrary a . coarbitrary b . coarbitrary c

instance Function ExtendedTime where
  function = functionMap
    (\(ExtendedTime a b c) -> (a, b, c))
    (\(a, b, c) -> (ExtendedTime a b c))
-- this toInteger/fromInteger should really be in an instance for Word64 instead
--    (\(ExtendedTime a b c) -> (a, toInteger b, c))
--    (\(a, b, c) -> (ExtendedTime a (fromInteger b) c))

instance (Monad m) => Serial m ExtendedTime where
  series = cons3 ExtendedTime

instance (Monad m) => CoSerial m ExtendedTime where
  coseries rs =
    alts3 rs >>- \f ->
    return $ \t ->
      case t of
        ExtendedTime a b c -> f a b c


instance (Arbitrary t) => Arbitrary (ConcreteField phantom t) where
  arbitrary = fmap ConcreteField arbitrary
  shrink (ConcreteField x) = fmap ConcreteField (shrink x)

instance (CoArbitrary t) => CoArbitrary (ConcreteField phantom t) where
  coarbitrary (ConcreteField t) = coarbitrary t

instance (Function t) => Function (ConcreteField phantom t) where
  function = functionMap unConcreteField ConcreteField

instance (Monad m, Serial m t) => Serial m (ConcreteField phantom t) where --newtypederivable? genericable
  series = fmap ConcreteField series
instance (Monad m, CoSerial m t) => CoSerial m (ConcreteField phantom t) where --newtypederivable? genericable
  coseries rs = fmap (. unConcreteField) (coseries rs)


--fieldify :: (FieldType (ConcreteField phantom t)) => ConcreteField phantom t -> FieldValue
--fieldify :: (Eq t, Ord t, Show t, Typeable phantom, Typeable t, Serialize t, Arbitrary t) => ConcreteField phantom t -> FieldValue
--fieldify x = FieldValue (ConcreteField x)
--ffieldify x f = fmap (FieldValue (ConcreteField x)) f

data TestFieldType where
  TestFieldType ::
      (Eq t, Ord t, Show t, Typeable phantom, Typeable t, Serialize t,
       Arbitrary t, CoArbitrary t, Function t,
       --illegal constraint: forall m. (Monad m) => Serial m t
       -- I guess there's no way to store those FlexibleContexts dictionaries
       -- in a GADT?
       --Serial m t, CoSerial m t
       Serial Identity t, CoSerial Identity t,
       Serial IO t, CoSerial IO t
      ) =>
        (forall m. (Monad m) => Series m t) -> -- series
        (forall m b. (Monad m) => Series m b -> Series m (t -> b)) -> -- coseries
        Proxy (ConcreteField phantom t)
      -> TestFieldType
instance Show TestFieldType where
  showsPrec prec (TestFieldType _ _ proxy) = showsPrec prec proxy

testedFieldTypesTuple ::
  ( 
  Proxy (ConcreteField () ()),
  Proxy (ConcreteField () Integer),
  Proxy (ConcreteField () [Integer]),
  Proxy (ConcreteField () BaseTime),
  Proxy (ConcreteField () ExtendedTime),
  Proxy (ConcreteField () UInt128),
  Proxy (ConcreteField Bool UInt128),
  Proxy (ConcreteField () Bool)
  )
testedFieldTypesTuple = (Proxy, Proxy, Proxy, Proxy, Proxy, Proxy, Proxy, Proxy)

testedFieldTypes :: [TestFieldType]
testedFieldTypes = case testedFieldTypesTuple of
  (a, b, c, d, e, f, g, h) -> [
    TestFieldType series coseries a,
    TestFieldType series coseries b,
    TestFieldType series coseries c,
    TestFieldType series coseries d,
    TestFieldType series coseries e,
    TestFieldType series coseries f,
    TestFieldType series coseries g,
    TestFieldType series coseries h
    ]
nullestTestedFieldTypeProxy :: Proxy (ConcreteField () ())
nullestTestedFieldTypeProxy = Proxy
nullestTestedFieldType :: TestFieldType
nullestTestedFieldType = List.head testedFieldTypes

pattern TFT proxy <- (TestFieldType _ _ proxy)

{-
data TestFieldType where
  TestFieldType ::
      (Eq t, Ord t, Show t, Typeable phantom, Typeable t, Serialize t,
       Arbitrary t, CoArbitrary t, Function t,
       --illegal constraint: forall m. (Monad m) => Serial m t
       -- I guess there's no way to store those FlexibleContexts dictionaries
       -- in a GADT?
       --Serial m t, CoSerial m t
       Serial Identity t, CoSerial Identity t,
       Serial IO t, CoSerial IO t
      ) => Proxy (phantom, t) -> TestFieldType
deriving instance Show TestFieldType

-- :: (forall t. (Eq t,....) -> x) -> x

testedFieldTypesTuple ::
  ( 
  Proxy ((), Integer),
  Proxy ((), [Integer]),
  Proxy ((), BaseTime),
  Proxy ((), ExtendedTime),
  Proxy ((), UInt128),
  Proxy (Bool, UInt128),
  Proxy ((), ()),
  Proxy ((), Bool)
  )
testedFieldTypesTuple = (Proxy, Proxy, Proxy, Proxy, Proxy, Proxy, Proxy, Proxy)

testedFieldTypes :: [TestFieldType]
testedFieldTypes = case testedFieldTypesTuple of
  (a, b, c, d, e, f, g, h) ->
    [TestFieldType a, TestFieldType b, TestFieldType c, TestFieldType d,
     TestFieldType e, TestFieldType f, TestFieldType g, TestFieldType h]
[
  TestFieldType (Proxy :: Proxy ((), Integer)),
  TestFieldType (Proxy :: Proxy ((), [Integer])),
  TestFieldType (Proxy :: Proxy ((), BaseTime)),
  TestFieldType (Proxy :: Proxy ((), ExtendedTime)),
  TestFieldType (Proxy :: Proxy ((), UInt128)),
  TestFieldType (Proxy :: Proxy (Bool, UInt128)),
  TestFieldType (Proxy :: Proxy ((), ())),
  TestFieldType (Proxy :: Proxy ((), Bool))
  ]
-- TODO just use ConcreteField directly everywhere?
ftProxyTupleToConcrete :: Proxy (phantom, t) -> Proxy (ConcreteField phantom t)
ftProxyTupleToConcrete Proxy = Proxy
-}

instance Arbitrary TestFieldType where
  arbitrary = elements testedFieldTypes
  shrink (TFT proxy) =
    if cast proxy == Just nullestTestedFieldTypeProxy
    then []
    else [nullestTestedFieldType]
  -- hmm
{-
  shrink (TFT (proxy::Proxy (ConcreteField phantom t))) =
    if isNothing (eqT :: Maybe (ConcreteField phantom t :~: ConcreteField () ()))
    then [nullestTestedFieldType]
    else []-}

instance (Monad m) => Serial m TestFieldType where
  series = List.foldr1 (\/) (List.map cons0 testedFieldTypes)
--  series = case testedFieldTypesTuple of
--    (a, b, c, d, e, f, g, h) ->
--      cons0 (TestFieldType a) \/ cons0 (TestFieldType b) \/ cons0 (TestFieldType c) \/
--      cons0 (TestFieldType d) \/ cons0 (TestFieldType e) \/ cons0 (TestFieldType f) \/
--      cons0 (TestFieldType g) \/ cons0 (TestFieldType h)
--      cons0 a \/ cons0 b \/ cons0 c \/ cons0 d \/ cons0 e \/ 
--      cons0 f \/ cons0 g \/ cons0 h
--  series = List.foldr1 (\/) (List.map cons0 testedFieldTypes)


instance Arbitrary FieldValue where
  arbitrary = oneof (fmap (\(TFT (_::Proxy (ConcreteField p t))) ->
      fmap FieldValue (arbitrary :: Gen (ConcreteField p t))
      --fmap (\cf -> FieldValue (cf :: ConcreteField phantom t)) arbitrary
    ) testedFieldTypes)
  shrink (FieldValue (f :: f_t)) =
    List.foldr (\(TFT (_::Proxy (ConcreteField p t))) tryNext ->
      case cast f :: Maybe (ConcreteField p t) of
        Nothing -> tryNext
        Just cf -> fmap FieldValue (shrink cf)) [] testedFieldTypes
    ++
    -- hmm will changing the type in it break anything else I wonder
    -- Should I shrink it to anything besides a nullish one
    if isNothing (eqT :: Maybe (f_t :~: ConcreteField () ()))
    then [FieldValue (ConcreteField () :: ConcreteField () ())]
    else []

instance (Monad m) => Serial m FieldValue where
  series = List.foldr1 (\/) (List.map (\(TestFieldType series_ _ (_::Proxy (ConcreteField p t))) ->
      series_ >>= \t -> cons0 (FieldValue (ConcreteField t :: ConcreteField p t))
    ) testedFieldTypes)
{-
instance (Monad m) => Serial m FieldValue where
  series = case testedFieldTypesTuple of
    (a, b, c, d, e, f, g, h) ->
      cons1 (FieldValue :: -> FieldValue) series
      ftProxyTupleToConcrete
-}

-- Orphans that should be defined in their own libraries but aren't!
{-
instance (Ord k, Arbitrary k, Arbitrary v) => Arbitrary (Map k v) where
  -- are duplicate keys any concern here?
  arbitrary = fmap Map.fromList arbitrary
  -- modeled after OrderedList's shrink instance,
  -- in case it helps remove duplicates or something
  shrink = fmap Map.fromList
    . List.filter (\kvs -> let ks = fmap fst kvs in List.sort ks == ks)
    . shrink
    . Map.toList
-}
--instance CoArbitrary Word64 where
--  coarbitrary = coarbitrary . toInteger
-- TODO is functionMap toInteger fromInteger correct with negative numbers in this?
instance Function Word64 where
  function = functionMap toInteger fromInteger
{-
instance (Monad m) => Serial m Word64 where
  series = fmap (fromInteger . SC.getNonNegative) series
instance (Monad m) => CoSerial m Word64 where
  coseries rs = fmap (. toInteger) (coseries rs)
-}
instance (Monad m) => Serial m (Proxy p) where
  series = return Proxy
instance (Monad m) => CoSerial m (Proxy p) where
  coseries rs = constM rs


-- or rather than Map.fromList here, we need instance Arbitrary Map?...
instance Arbitrary EntityFields where
  arbitrary = fmap (initializeEntityFields . Map.fromList) arbitrary
  shrink efs = fmap initializeEntityFieldsNonuniform (shrink (getAllEntityFields efs))

-- TODO the Serial Map instance from smallcheck-series looks like it only
-- generates maps of size 1. fix???

instance (Monad m) => Serial m EntityFields where
  series = fmap initializeEntityFieldsNonuniform series
{-
  series = fmap (EntityFields . Map.fromList) $
    cons0 [] \/
    decDepth (do
      TestFieldType series_ _ _ <- series
      let series_fieldlist =
            cons0 [] \/
              decDepth ((\entityId fieldVal xs -> (entityId, fieldVal) : xs)
                <$> series <~> series_ <~> series_fieldlist)
      let series_efot_pair = fmap (\list ->
            (EntityFieldsOfType (Map.fromList list))) series_fieldlist
      EntityFieldsOfType (series_
      (:) <$> series_ <~> series
-}

-- quickcheck and smallcheck don't agree on how to represent functions
data FunFun a b = SCFun (a -> b) | QCFun (QC.Fun a b)
applyFunFun :: FunFun a b -> a -> b
applyFunFun (SCFun f) = f
applyFunFun (QCFun f) = QC.apply f
instance (Function a, CoArbitrary a, Arbitrary b) => Arbitrary (FunFun a b) where
  arbitrary = fmap QCFun arbitrary
instance (Serial Identity a, Show a, Show b) => Show (FunFun a b) where
  show (SCFun f) = show f
  show (QCFun f) = show f
instance (CoSerial m a, Serial m b) => Serial m (FunFun a b) where
  series = fmap SCFun series


-- should any of the fields of this be strict fields??
-- VRC = ValueRetrievalComputation
data VRCGenerator result where
  VRCGet :: (FieldType f, Function f, CoArbitrary f, Serial Identity f) => EntityId -> (FunFun f (VRCGenerator result)) -> VRCGenerator result
  VRCGetIgnore :: (FieldType f) => EntityId -> Proxy f -> VRCGenerator result -> VRCGenerator result
  VRCResult :: result -> VRCGenerator result
deriving instance (Show result) => Show (VRCGenerator result)

instance (Arbitrary result) => Arbitrary (VRCGenerator result) where
  arbitrary = oneof $
    [
      fmap VRCResult arbitrary
    ] ++
    List.concatMap (\(TFT (proxy::Proxy (ConcreteField p t))) ->
        [
        liftM3 VRCGetIgnore
          arbitrary (pure proxy) arbitrary,
        liftM2 VRCGet
          arbitrary (arbitrary :: Gen (FunFun (ConcreteField p t) (VRCGenerator result)))
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
  shrink (VRCGet entityId (f_g :: FunFun f (VRCGenerator result))) =
    -- is it possible to shrink a "Fun" function's argument type?
    -- to shrink the result of the function? probably at least that...
    [VRCGet se f_g | se <- shrink entityId] ++
    [VRCGetIgnore entityId (Proxy::Proxy f) (applyFunFun f_g defaultFieldValue)] ++
    [VRCGet entityId s_f_g | s_f_g <- shrink f_g]

instance (Monad m, Serial m result) => Serial m (VRCGenerator result) where
  series =
    cons1 VRCResult \/
    List.foldr1 (\/) (
    List.concatMap (\(TestFieldType series_ coseries_ (proxy::Proxy (ConcreteField p t))) ->
        [
        cons3 (VRCGetIgnore :: EntityId -> Proxy (ConcreteField p t) -> VRCGenerator result -> VRCGenerator result),
        --cons2 (VRCGet :: EntityId -> (FunFun (ConcreteField p t) (VRCGenerator result)) -> VRCGenerator result)
        decDepth $
          (VRCGet :: EntityId -> (FunFun (ConcreteField p t) (VRCGenerator result)) -> VRCGenerator result)
          <$> series <~> fmap (SCFun . (. unConcreteField)) (coseries_ series)
        ]
      ) testedFieldTypes
    )

newtype EventGenerator = EventGenerator
    (VRCGenerator [(EntityId, FieldValue)])
  deriving (Show)
-- Do I want to use GeneralizedNewtypeDeriving? I forget whether it is sound yet.
-- Probably depends on whether I'd want to use it in more than a couple places.
-- deriving (Show, Arbitrary)

instance Arbitrary EventGenerator where --newtypederivable
  arbitrary = fmap EventGenerator arbitrary
  shrink (EventGenerator g) = fmap EventGenerator (shrink g)

instance (Monad m) => Serial m EventGenerator where
  series = newtypeCons EventGenerator

data PredictorGenerator = PredictorGenerator
    TestFieldType
    (FunFun EntityId (VRCGenerator (Maybe (BaseTime, EventGenerator))))
  deriving (Show)

instance Arbitrary PredictorGenerator where
  arbitrary = liftM2 PredictorGenerator arbitrary arbitrary
  shrink (PredictorGenerator t f) =
    [PredictorGenerator t' f | t' <- shrink t] ++
    [PredictorGenerator t f' | f' <- shrink f]

instance (Monad m) => Serial m PredictorGenerator where
  series = cons2 PredictorGenerator

vrcGeneratorToVRC :: forall m result. (Monad m) => ValueRetriever m -> VRCGenerator result -> m result
vrcGeneratorToVRC valueRetriever = go
  where
    go :: VRCGenerator result -> m result
    go (VRCResult result) =
      return result
    go (VRCGet entityId continuation) =
      valueRetriever entityId >>= go . applyFunFun continuation
    go (VRCGetIgnore entityId (_::Proxy f) continuation) =
      (valueRetriever entityId :: m f) >> go continuation

eventGeneratorToEvent :: EventGenerator -> Event
eventGeneratorToEvent (EventGenerator vrc) = Event (\valueRetriever ->
    vrcGeneratorToVRC valueRetriever vrc
  )

predictorGeneratorToPredictor :: PredictorGenerator -> Predictor
predictorGeneratorToPredictor
  (PredictorGenerator
    (TFT proxy)
    f_vrc) =
      Predictor
        proxy
        (\valueRetriever entityId ->
          liftM (fmap (fmap eventGeneratorToEvent))
            (vrcGeneratorToVRC valueRetriever (applyFunFun f_vrc entityId)))

data PristineTSIGenerator =
  PristineTSIGenerator
    ExtendedTime EntityFields (Map ExtendedTime EventGenerator) [PredictorGenerator]
  deriving (Show, Typeable, Generic)

instance Arbitrary PristineTSIGenerator where
  arbitrary = liftM4 PristineTSIGenerator arbitrary arbitrary arbitrary arbitrary
  shrink = genericShrink

instance (Monad m) => Serial m PristineTSIGenerator where
  series = cons4 PristineTSIGenerator

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
    [EventGeneratorGetIgnore entityId (Proxy::Proxy f) (applyFunFun f_g defaultFieldValue)] ++
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


scprop_remakable :: (SC.Testable m PristineTSIGenerator) => SC.Property m
scprop_remakable = SC.forAll prop_remakable--unnecessary but let's get some missing instance errors?

prop_IntermediateMoveToFutureTimeIsHarmless (Ordered times) (PristineWorld world1) =
  List.length times > 1 QC.==>
    equivalentTimeStewards
      (TSI.moveToFutureTime (List.last times) world1)
      (List.foldl' (\w t -> TSI.moveToFutureTime t w) world1 times)



return []  --required just before the next line so GHC typechecks the above declarations soon enough for the below line to find the above declarations
runTests :: IO Bool
runTests = $verboseCheckAll
--runTests = $quickCheckAll

main :: IO ()
--main = runTests >>= print
main = defaultMain tests

tests :: TestTree
tests =
  localOption (mkTimeout (1*1000000)) $
  --localOption (SmallCheckDepth 3) $
  testGroup "Tests" [scProps, qcProps]

scProps = testGroup "(checked by SmallCheck)" [
  SC.testProperty "world appears(is?) the same if taken apart and remade"
    --(SC.monadic $ do
    --   timeout 1000 $ do
         prop_remakable
  ]

qcProps = testGroup "(checked by QuickCheck)" [
  QC.testProperty "maths..." (\a (b::Integer) -> a + b - b == a)
  ]

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


