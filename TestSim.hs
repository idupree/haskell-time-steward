{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables, DeriveDataTypeable, DeriveGeneric, TemplateHaskell, ViewPatterns, PatternSynonyms, TypeOperators, StandaloneDeriving, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, BangPatterns #-}

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

import Data.Bits as Bits
import Data.Ix
import Data.Data

import Data.Foldable
import Data.Monoid

import System.Timeout
import System.IO

import Control.Exception
-- hackage deepseq
import Control.DeepSeq
-- hackage async
import Control.Concurrent.Async


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
import Control.Monad.Logic.Class --hackage logict, a dep of smallcheck
-- hackage smallcheck-series:
-- I don't like its Map instance
-- import Test.SmallCheck.Series.Instances

--import InefficientFlatTimeSteward as TSI
--import FlatTimeSteward as TSI
import CrossverifiedTimeStewards as TSI

import Data.ArithEncode as AE
import MoreArithEncode as AE

--import Debug.Trace
--trace1 :: (Show a) => a -> a
--trace1 a = trace (show a) a
--trace2 :: (Show a) => String -> a -> a
--trace2 s a = trace (s ++ show a) a


type TSI = TimeStewardInstance

-- for convenience(?), make all the fields be from the same type constructor
newtype ConcreteField phantom t = ConcreteField t
  deriving (Eq, Ord, Typeable, Generic)
unConcreteField :: ConcreteField phantom t -> t
unConcreteField (ConcreteField t) = t
instance (Serialize t) => Serialize (ConcreteField phantom t)
instance (NFData t) => NFData (ConcreteField phantom t)
instance (Typeable phantom, Typeable t, Show t) => Show (ConcreteField phantom t) where
  showsPrec prec (ConcreteField t) =
    showString "CF<" . shows (typeRep (Proxy :: Proxy phantom)) .
    showString ", " . shows (typeRep (Proxy :: Proxy t)) .
    showString ">" . showsPrec prec t
instance (Eq t, Ord t, Show t, Typeable phantom, Typeable t, Serialize t, NFData t, Arbitrary t) => FieldType (ConcreteField phantom t) where
  -- TODO this better
  -- maybe use https://downloads.haskell.org/~ghc/7.10.1/docs/html/users_guide/type-level-literals.html
  -- (which exists in 7.8 as well)
  -- These constants are randomly generated.
  -- I... I think I can make a phantom integer argument to ConcreteField
  -- that is randomly generated at runtime, omg. For testing.
  defaultFieldValue = ConcreteField (unGen arbitrary (mkQCGen 0x3ba19626350be65a) 100)

encodingConcreteField :: (Encoding t) -> Encoding (ConcreteField phantom t)
encodingConcreteField enc = wraptotal unConcreteField ConcreteField enc

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

encodingUInt128 :: Encoding UInt128
encodingUInt128 = boundedint

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

encodingEntityId :: Encoding EntityId
encodingEntityId = wraptotal unEntityId EntityId encodingUInt128

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

encodingExtendedTime :: Encoding ExtendedTime
encodingExtendedTime = wraptotal
  (\(ExtendedTime a b c) -> (a, b, c))
  (\(a, b, c) -> (ExtendedTime a b c))
  (triple integral boundedint boundedint)


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
      (Eq t, Ord t, Show t, Typeable phantom, Typeable t, Serialize t, NFData t,
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
        Encoding (ConcreteField phantom t) ->
        Proxy (ConcreteField phantom t)
      -> TestFieldType
instance NFData TestFieldType where
  -- not perfect because rnf on functions doesn't exist,
  -- but in practice all instances of TestFieldType should be fine
  rnf (TestFieldType !_ !_ !_ !_) = ()
instance Show TestFieldType where
  showsPrec prec (TFT proxy) = showsPrec prec (typeRep proxy)
instance Eq TestFieldType where
  --TFT a == TFT b = cast a == Just b
  TFT a == TFT b = (typeRep a == typeRep b)
instance Ord TestFieldType where
  compare (TFT a) (TFT b) = compare (typeRep a) (typeRep b)

testedFieldTypesTuple ::
  ( 
  {-Proxy (ConcreteField () ()),
  Proxy (ConcreteField () Integer),
  Proxy (ConcreteField () [Integer]),
  Proxy (ConcreteField () BaseTime),
  Proxy (ConcreteField () ExtendedTime),-}
  Proxy (ConcreteField () UInt128),
  --Proxy (ConcreteField Bool UInt128),
  Proxy (ConcreteField () Bool)
  )
--testedFieldTypesTuple = (Proxy, Proxy, Proxy, Proxy, Proxy, Proxy, Proxy, Proxy)
testedFieldTypesTuple = (Proxy, Proxy)

testedFieldTypes :: [TestFieldType]
testedFieldTypes = case testedFieldTypesTuple of
  (a, b) -> [
    TestFieldType series coseries (encodingConcreteField encodingUInt128) a,
    TestFieldType series coseries (encodingConcreteField enum) b
    ]
{-
  (a, b, c, d, e, f, g, h) -> [
    TestFieldType series coseries a,
    TestFieldType series coseries b,
    TestFieldType series coseries c,
    TestFieldType series coseries d,
    TestFieldType series coseries e,
    TestFieldType series coseries f,
    TestFieldType series coseries g,
    TestFieldType series coseries h
    ]-}
nullestTestedFieldTypeProxy :: Proxy (ConcreteField () ())
nullestTestedFieldTypeProxy = Proxy
nullestTestedFieldType :: TestFieldType
nullestTestedFieldType = TestFieldType series coseries
  (encodingConcreteField unit) nullestTestedFieldTypeProxy
--nullestTestedFieldType = List.head testedFieldTypes

pattern TFT proxy <- (TestFieldType _ _ _ proxy)

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

encodingTestFieldType :: Encoding TestFieldType
encodingTestFieldType = fromOrdList testedFieldTypes

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
  series = List.foldr1 (\/) (List.map (\(TestFieldType series_ _ _ (_::Proxy (ConcreteField p t))) ->
      --series_ >>- \t -> cons0 (FieldValue (ConcreteField t :: ConcreteField p t))
      fmap (\t -> FieldValue (ConcreteField t :: ConcreteField p t)) series_
    ) testedFieldTypes)

--FieldValue :: forall x. (F x) => x -> FieldValue
--unFieldValue :: FieldValue -> (forall x. (F x) => x -> cont) -> cont

{-
encodingTestFieldTypeRelatedExistential ::
  forall ty.
  (forall concrete. (Typeable concrete) => concrete -> ty) ->
  (ty -> (forall concrete. (Typeable concrete) => concrete -> cont) -> cont) ->
  (forall cf. Encoding cf -> Encoding concrete)
-}
deriving instance Typeable Identity -- this doesn't exist already??
-- c__ = concrete __
-- f = field
encodingTestFieldTypeRelatedExistential ::
  forall ctycon ty. (Typeable ctycon) =>
  (forall cf. (FieldType cf) => ctycon cf -> ty) ->
  (forall cont. ty -> (forall cf. (FieldType cf) => ctycon cf -> cont) -> cont) ->
  (forall cf. (FieldType cf) => Encoding cf -> Encoding (ctycon cf)) ->
  [TestFieldType] ->
  Encoding ty
encodingTestFieldTypeRelatedExistential abstract concretize encodetycon fieldTypes =
  AE.union (fmap (\(TestFieldType _ _ fieldEncoding (_::Proxy (ConcreteField p t))) ->
    mkEncoding
      (\ty -> concretize ty (\(concrete :: ctycon cf) ->
        case eqT :: Maybe (cf :~: ConcreteField p t) of
          Nothing -> error "encodingTestFieldTypeRelatedExistential bug"
          Just Refl -> AE.encode (encodetycon fieldEncoding) concrete))
      (abstract . AE.decode (encodetycon fieldEncoding))
      (AE.size (encodetycon fieldEncoding))
      (\ty -> concretize ty (\(concrete :: ctycon cf) ->
        case eqT :: Maybe (cf :~: ConcreteField p t) of
          Nothing -> False
          Just Refl -> AE.inDomain (encodetycon fieldEncoding) concrete))
  ) fieldTypes)

encodingFieldValue :: [TestFieldType] -> Encoding FieldValue
encodingFieldValue = encodingTestFieldTypeRelatedExistential
    (FieldValue . runIdentity)
    (\(FieldValue f) cont -> cont (Identity f))
    (wraptotal runIdentity Identity)

encodingEntityFieldsOfType :: [TestFieldType] -> Encoding EntityFieldsOfType
encodingEntityFieldsOfType = encodingTestFieldTypeRelatedExistential
    (EntityFieldsOfType)
    (\(EntityFieldsOfType m) cont -> cont m)
    (AE.function (pretendinfinite encodingEntityId))

encodingEntityFields :: Encoding EntityFields
encodingEntityFields = let
  -- [EntityFieldsOfType] in these is in the type order and length of
  -- testedFieldTypes, with one with no fields represented as an empty Map
  -- (whereas in EntityFields, Maps for unused field types are omitted).
  completeEfotListToEntityFields :: [EntityFieldsOfType] -> EntityFields
  completeEfotListToEntityFields =
    (EntityFields . Map.fromList .
      Maybe.mapMaybe (\efot@(EntityFieldsOfType (m::Map EntityId f)) ->
                   if Map.null m then Nothing
                   else Just (typeRep (Proxy::Proxy f), efot)))
  validFieldTypes :: Set TypeRep
  validFieldTypes = Set.fromList (List.map (\(TFT p) -> typeRep p) testedFieldTypes)
  entityFieldsToMaybeCompleteEfotList :: EntityFields -> Maybe [EntityFieldsOfType]
  entityFieldsToMaybeCompleteEfotList (EntityFields efs) =
    if Map.keysSet efs `isSubsetOf` validFieldTypes
    then Just (
      List.map (\(TFT (p::Proxy (ConcreteField phantom f))) ->
        case Map.lookup (typeRep p) efs of
          Nothing -> EntityFieldsOfType (Map.empty :: Map EntityId (ConcreteField phantom f))
          Just efot -> efot
      ) testedFieldTypes)
    else Nothing

  completeEfotListEncoding :: Encoding [EntityFieldsOfType]
  completeEfotListEncoding =
    interleavedTuplishList (fmap (encodingEntityFieldsOfType . (:[])) testedFieldTypes)
--      (List.sortBy (comparing (\(TFT p) -> typeRep p)) testedFieldTypes)
  in
  mkEncoding
    (AE.encode completeEfotListEncoding . (\(Just x)->x) . entityFieldsToMaybeCompleteEfotList)
    (completeEfotListToEntityFields . AE.decode completeEfotListEncoding)
    (AE.size completeEfotListEncoding)
    (isJust . entityFieldsToMaybeCompleteEfotList)

   

--AE.power (length testedFieldTypes)


{-
-- the extra fancy typesystem wrangling makes this implementation longer
encodingFieldValue :: Encoding FieldValue
encodingFieldValue = AE.union (fmap (\(TestFieldType _ _ fieldEncoding (_::Proxy (ConcreteField p t))) ->
    mkEncoding
      (\(FieldValue (f :: f_t)) ->
        case cast f :: Maybe (ConcreteField p t) of
          Nothing -> error "encodingFieldValue bug"
          Just cf -> AE.encode fieldEncoding cf)
      (FieldValue . AE.decode fieldEncoding)
      (AE.size fieldEncoding)
      (\(FieldValue (f :: f_t)) ->
        case cast f :: Maybe (ConcreteField p t) of
          Nothing -> False
          Just cf -> AE.inDomain fieldEncoding cf)
  ) testedFieldTypes)
-}

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
instance (Monad m) => Serial m Word64 where
  series = fmap (fromInteger . SC.getNonNegative) series
instance (Monad m) => CoSerial m Word64 where
  coseries rs = fmap (. toInteger) (coseries rs)
instance (Monad m) => Serial m (Proxy p) where
  series = return Proxy
instance (Monad m) => CoSerial m (Proxy p) where
  coseries rs = constM rs
instance (Monad m) => Serial m Ordering where
  series = cons0 LT \/ cons0 EQ \/ cons0 GT
instance (Monad m) => CoSerial m Ordering where
  coseries rs =
    rs >>- \r1 ->
    rs >>- \r2 ->
    rs >>- \r3 ->
    return $ \x -> case x of LT -> r1; EQ -> r2; GT -> r3


-- or rather than Map.fromList here, we need instance Arbitrary Map?...
instance Arbitrary EntityFields where
  arbitrary = fmap (initializeEntityFields . Map.fromList) arbitrary
  shrink efs = fmap initializeEntityFieldsNonuniform (shrink (getAllEntityFields efs))

-- TODO the Serial Map instance from smallcheck-series looks like it only
-- generates maps of size 1. fix???

-- TODO don't waste time generating default values that this just throws away
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

--wraptotal
--  initializeEntityFieldsNonuniform getAllEntityFields (pair 


-- quickcheck and smallcheck don't agree on how to represent functions
--data FunFun a b = SCFun (a -> b) | QCFun (QC.Fun a b) | MapFun (Map a b) b
data FunFun a b where
  QCFun :: !(QC.Fun a b) -> FunFun a b
  SCFun :: (Serial Identity a) => !(a -> b) -> FunFun a b
  MapFun :: (Ord a) => !(Map a b) -> !b -> FunFun a b
--TODO: a type of fun that takes bits from keys and has recursively(?) possible results?
--deriving instance (Typeable a, Typeable b) => Typeable (FunFun a b)
deriving instance Typeable FunFun
applyFunFun :: FunFun a b -> a -> b
applyFunFun (QCFun f) = QC.apply f
applyFunFun (SCFun f) = f
applyFunFun (MapFun m d) = fromMaybe d . flip Map.lookup m
instance (NFData a, NFData b) => NFData (FunFun a b) where
  -- only works properly for MapFun and maybe QCFun
  --requires Show a and b: rnf (QCFun f) = rnf (show f)
  rnf (QCFun !_) = error "NFData QCFun unimplemented"
  rnf (SCFun !_) = error "NFData SCFun unimplemented"
  rnf (MapFun !m !d) = case rnf m of () -> case rnf d of () -> ()
instance (Function a, CoArbitrary a, Arbitrary b) => Arbitrary (FunFun a b) where
  arbitrary = fmap QCFun arbitrary
instance (Show a, Show b) => Show (FunFun a b) where
  show (QCFun f) = show f
  show (SCFun f) = show f
  show (MapFun m d) =
    --showList__ "{" ("; _ -> "++show d++"}") "; " (\(a, b) -> shows a . showString " -> " . shows b) (Map.toList m) ""
    showList__ "{" "}" "; " (\(a, b) ->
        case a of { Nothing -> showString "_"; Just a_ -> shows a } . showString " -> " . shows b)
      (fmap (\(a,b)->(Just a, b)) (Map.toList m) ++ [(Nothing, d)]) ""
    --show (Map.toList m)
    -- todo maybe a better form with "a -> b" instead of show as tuple,
    -- and maybe each on its own line?
showList__ :: String -> String -> String -> (a -> ShowS) ->  [a] -> ShowS
showList__ beg end _sep _     []     s = beg ++ end ++ s
showList__ beg end sep showx (x:xs) s = beg ++ showx x (showl xs)
  where
    showl []     = end ++ s
    showl (y:ys) = sep ++ showx y (showl ys)
--instance (CoSerial m a, Serial m b) => Serial m (FunFun a b) where
  --series = fmap SCFun series
--instance (Ord a, Serial m a, Serial m b) => Serial m (FunFun a b) where
instance (Ord a, Eq b, Serial m a, Serial m b) => Serial m (FunFun a b) where
  series = decDepth $ mkMapFun <$> (fmap Map.fromList series) <~> series
-- todo a more efficent way to do this filtering than generating+discarding everything?
mkMapFun :: (Ord a, Eq b) => (Map a b) -> b -> FunFun a b
mkMapFun m d = MapFun (Map.filter (\b -> not (b == d)) m) d

-- TODO figure out how to make the default value not appear in the map.
-- There's AE.exclude but how to thread it through AE.pair?
encodingFunFun :: (Ord a) => Encoding a -> Encoding b -> Encoding (FunFun a b)
encodingFunFun k v = wraptotal
  (\(MapFun m d) -> (m, d))
  (\(m, d) -> MapFun m d)
  (interleavedpair
    (AE.function (pretendInfiniteIfMoreThan 256 k) v)
    v)

-- this will work more usefully once the encodingFunFun TODO is solved
encodingNonConstFunFun :: (Ord a) => Encoding a -> Encoding b -> Encoding (FunFun a b)
encodingNonConstFunFun k v = wraptotal
  (\(MapFun m d) -> (m, d))
  (\(m, d) -> MapFun m d)
  (interleavedpair
    (AE.nonzero (AE.function (pretendInfiniteIfMoreThan 256 k) v))
    v)


--castFunFunArg :: (Typeable a, Typeable a') => FunFun a b -> Maybe (FunFun a' b)
--castFunFunArg (SCFun f) = 

{-
seriesMapFun ::
  forall phantom a b m0. (Monad m0) =>
  (forall m. (Monad m) => Series m a) -> -- series
  (forall m c. (Monad m) => Series m c -> Series m (a -> c)) -> -- coseries
  (forall m. (Monad m) => Series m b) -> -- series
  Series m0 (FunFun (ConcreteField phantom a) b)
-}
seriesMapFun ::
  forall phantom a b m. (Monad m, Ord a, Eq b) =>
  Series m a -> -- series
  (forall c. Series m c -> Series m (a -> c)) -> -- coseries
  Series m b -> -- series
  Series m (FunFun (ConcreteField phantom a) b)
seriesMapFun argSeries argCoseries resultSeries =
  --fmap (SCFun . (. unConcreteField)) (argCoseries resultSeries)
  decDepth $ mkMapFun
    <$> (fmap Map.fromList
          (seriesListCustomizable
            (decDepth $ (,) <$>
               fmap (ConcreteField :: a -> ConcreteField phantom a)
                 argSeries <~> resultSeries)))
    <~> resultSeries

seriesListCustomizable ::
  forall m a. (Monad m) => Series m a -> Series m [a]
seriesListCustomizable elemSeries =
  cons0 [] \/
  decDepth ((:) <$> elemSeries <~> seriesListCustomizable elemSeries)


-- Given a series of unique values, gives a series of all
-- (mathematical) sets of those value. (If elemSeries returns
-- duplicates then the set will have some duplicates.)
generateSets :: forall m a. (Monad m) => Series m a -> Series m [a]
generateSets elemSeries =
  generateSets' False elemSeries
generateSets' :: forall m a. (Monad m) => Bool -> Series m a -> Series m [a]
generateSets' skipping elemSeries =
    msplit elemSeries >>- \mAMa ->
      case mAMa of
        Nothing -> if skipping then mzero else pure []
        Just (a, ma) ->
          (if skipping then id else (pure [] \/)) $
          decDepth ((a :) <$> generateSets' False ma)
          \/
          decDepth (generateSets' True ma)

seriesSet :: forall m a. (Ord a, Monad m) => Series m a -> Series m (Set a)
seriesSet elemSeries = fmap Set.fromList (generateSets elemSeries)

seriesMap :: forall m k v. (Ord k, Monad m) => Series m k -> Series m v -> Series m (Map k v)
seriesMap keySeries valSeries = fmap Map.fromList $
    seriesWithVals (generateSets keySeries) valSeries

seriesWithVals :: forall m k v. (Monad m) => Series m [k] -> Series m v -> Series m [(k, v)]
seriesWithVals keysSeries valSeries = keysSeries >>- go
  where
    go :: [k] -> Series m [(k, v)]
    go [] = pure []
    go (k:ks) = (:) <$> (((,) k) <$> valSeries) <~> go ks

instance (Ord a, Serial m a) => Serial m (Set a) where
  series = seriesSet series

instance (Ord k, Serial m k, Serial m v) => Serial m (Map k v) where
  series = seriesMap series series
    


{-
powerset :: [a] -> [[a]]
powerset [] = [[]]
powerset (x:xs) = powerset xs ++ fmap (x:) (powerset xs)
-}

--subsetsOfSizeN

{-
powersetUpToDepth :: Depth -> [a] -> [[a]]
powersetUpToDepth _ [] = [[]]
powersetUpToDepth 0 _ = 
powersetUpToDepth n (x:xs) = powerset xs 
-}

--seriesSetExcluding :: Set


-- hack!
instance (Eq a, Eq b) => Eq (FunFun a b) where
  MapFun ma da == MapFun mb db = ma == mb && da == db
  _ == _ = error "unimplemented FunFun equality"
instance (Ord a, Ord b) => Ord (FunFun a b) where
  compare (MapFun ma da) (MapFun mb db) = compare (da, ma) (db, ma)
  compare _ _ = error "unimplemented FunFun ordering"
--deriving instance (Eq result) => Eq (VRCGenerator result)
-- OUT OF DATE COMMENT: Typeable result is not actually needed but it didn't seem important enough to refactor to avoid needing it
instance (Eq result) => Eq (VRCGenerator result) where
  VRCGet ea (fa::FunFun fa (VRCGenerator result))
      == VRCGet eb (fb::FunFun fb (VRCGenerator result))
    = ea == eb && case (eqT :: Maybe (fa :~: fb)) of Nothing -> False; Just Refl -> fa == fb
  VRCGetIgnore ea pa ga == VRCGetIgnore eb pb gb = ea == eb && cast pa == Just pb && ga == gb
  VRCResult ra == VRCResult rb = ra == rb
  _ == _ = False
instance (Ord result) => Ord (VRCGenerator result) where
  compare (VRCGet ea (fa::FunFun fa (VRCGenerator result)))
          (VRCGet eb (fb::FunFun fb (VRCGenerator result)))
    = case compare ea eb of
        GT -> GT; LT -> LT
        EQ -> case (eqT :: Maybe (fa :~: fb)) of
          Nothing -> compare (typeRep (Proxy :: Proxy fa)) (typeRep (Proxy :: Proxy fb))
          Just Refl -> compare fa fb
  compare (VRCGetIgnore ea pa ga) (VRCGetIgnore eb pb gb) =
    compare (ea, typeRep pa, ga) (eb, typeRep pb, gb)
  compare (VRCResult ra) (VRCResult rb) = compare ra rb
  compare (VRCGet _ _) _ = LT
  compare (VRCResult _) _ = GT
  compare _ (VRCGet _ _) = GT
  compare _ (VRCResult _) = LT
deriving instance Eq PredictorGenerator
deriving instance Ord PredictorGenerator
deriving instance Eq EventGenerator
deriving instance Ord EventGenerator

-- should any of the fields of this be strict fields??
-- VRC = ValueRetrievalComputation
data VRCGenerator result where
  --VRCGet :: (FieldType f, Function f, CoArbitrary f, Serial Identity f) => EntityId -> (FunFun f (VRCGenerator result)) -> VRCGenerator result
  VRCGet :: (FieldType f) => EntityId -> (FunFun f (VRCGenerator result)) -> VRCGenerator result
  VRCGetIgnore :: (FieldType f) => EntityId -> Proxy f -> VRCGenerator result -> VRCGenerator result
  VRCResult :: result -> VRCGenerator result
deriving instance Typeable VRCGenerator
instance (NFData result) => NFData (VRCGenerator result) where
  rnf (VRCGet entityId f) = rnf (entityId, f)
  rnf (VRCGetIgnore entityId !_proxy vrc) = rnf (entityId, vrc)
  rnf (VRCResult r) = rnf r
--deriving instance (Show result) => Show (VRCGenerator result)
showsEntityFieldIdentifier :: (Typeable p) => EntityId -> Proxy p -> ShowS
showsEntityFieldIdentifier entityId proxy =
  showString "\"" . shows entityId . showString "@" . shows (typeRep proxy)
   . showString "\""
instance (Show result) => Show (VRCGenerator result) where
  showsPrec _ (VRCGet entityId (f :: (FunFun arg (VRCGenerator result)))) =
    showsEntityFieldIdentifier entityId (Proxy :: Proxy arg)
     . showString " >>= " . shows f
  showsPrec _ (VRCGetIgnore entityId proxy continuation) =
    showsEntityFieldIdentifier entityId proxy
     . showString " >> " . shows continuation
  showsPrec _ (VRCResult result) = showString "return " . shows result

data IdentityVRCGet result f = IdentityVRCGet {
  unIdentityVRCGet :: (EntityId, (FunFun f (VRCGenerator result))) }
  deriving (Typeable)
data IdentityVRCGetIgnore result f = IdentityVRCGetIgnore {
  unIdentityVRCGetIgnore :: (EntityId, Proxy f, VRCGenerator result) }
  deriving (Typeable)

encodingVRCGenerator :: (Typeable result) => Encoding result -> Encoding (VRCGenerator result)
encodingVRCGenerator resultEnc =
 AE.recursive $ \recurse ->
  wraptotal
    (\vrc -> case vrc of VRCResult{} -> Left vrc; _ -> Right vrc)
    (\x -> case x of Left vrc -> vrc; Right vrc -> vrc)
    (AE.either
      (wraptotal (\(VRCResult r) -> r) (VRCResult) resultEnc)
      (wraptotal
        (\vrc -> case vrc of VRCGetIgnore{} -> Left vrc; _ -> Right vrc)
        (\x -> case x of Left vrc -> vrc; Right vrc -> vrc)
          (AE.either
            -- this takes up more lines than it should, because:
            -- - encodingTestFieldTypeRelatedExistential should put the wraptotal runIdentity Identity itself??
            -- - not using type classes for default encoding
            -- - having to specify the proxy type(?)
            -- - being both coarbitrary and arbitrary all the time!
            (encodingTestFieldTypeRelatedExistential
              (\(unIdentityVRCGetIgnore -> (entityId, proxy, vrc)) ->
                 VRCGetIgnore entityId proxy vrc)
              (\(VRCGetIgnore entityId proxy vrc) cont ->
                  cont (IdentityVRCGetIgnore (entityId, proxy, vrc)))
              (\(_cfEnc :: Encoding cf) ->
                  wraptotal unIdentityVRCGetIgnore IdentityVRCGetIgnore $
                  interleavedtriple
                    encodingEntityId
                    (AE.singleton (Proxy::Proxy cf))
                    recurse)
              testedFieldTypes)
            (encodingTestFieldTypeRelatedExistential
              (\(unIdentityVRCGet -> (entityId, f)) -> VRCGet entityId f)
              (\(VRCGet entityId f) cont -> cont (IdentityVRCGet (entityId, f)))
              (\(cfEnc :: Encoding cf) ->
                  wraptotal unIdentityVRCGet IdentityVRCGet $
                  interleavedpair
                    encodingEntityId
                    -- nonconst to distinguish from VRCGetIgnore...
                    -- alternatively, we could encodingFunFUn and generate
                    -- a different constructor depending whether it is const.
                    -- (Or it might be good to test with const ones here too?)
                    (encodingNonConstFunFun
                      cfEnc
                      recurse)
              )
              testedFieldTypes)
          )))

getMoreFieldTypeDictionaries ::
  forall cf result.
  (Typeable cf) =>
  Proxy cf ->
  ((FieldType cf, Function cf, Arbitrary cf, CoArbitrary cf, Serial Identity cf) => Proxy cf -> result) ->
  --forall cf0 result.
  --(Typeable cf0) =>
  --(forall cf. (cf ~ cf0, FieldType cf, Function cf, Arbitrary cf, CoArbitrary cf, Serial Identity cf) => Proxy cf -> result) ->
  result
getMoreFieldTypeDictionaries proxyArg continuation = case
  Maybe.mapMaybe
    (\(TFT (proxy::Proxy (ConcreteField p t))) ->
      fmap (\Refl -> continuation proxy)
           (eqT :: Maybe (cf :~: ConcreteField p t)))
    testedFieldTypes
  of
    [x] -> x

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
    getMoreFieldTypeDictionaries (Proxy :: Proxy f) $ \_ ->
    -- is it possible to shrink a "Fun" function's argument type?
    -- to shrink the result of the function? probably at least that...
    [VRCGet se f_g | se <- shrink entityId] ++
    [VRCGetIgnore entityId (Proxy::Proxy f) (applyFunFun f_g defaultFieldValue)] ++
    [VRCGet entityId s_f_g | s_f_g <- shrink f_g]

-- Eq result is only so-so necessary for more efficient seriesMapFun..,
instance (Monad m, Serial m result, Eq result) => Serial m (VRCGenerator result) where
  series =
    cons1 VRCResult \/
    List.foldr1 (\/) (
    List.concatMap (\(TestFieldType series_ coseries_ _ (proxy::Proxy (ConcreteField p t))) ->
        [
        cons3 (VRCGetIgnore :: EntityId -> Proxy (ConcreteField p t) -> VRCGenerator result -> VRCGenerator result),
        --cons2 (VRCGet :: EntityId -> (FunFun (ConcreteField p t) (VRCGenerator result)) -> VRCGenerator result)
        decDepth $
          (VRCGet :: EntityId -> (FunFun (ConcreteField p t) (VRCGenerator result)) -> VRCGenerator result)
          <$> series <~> seriesMapFun series_ coseries_ series
        ]
      ) testedFieldTypes
    )

newtype EventGenerator = EventGenerator
    (VRCGenerator [(EntityId, FieldValue)])
  deriving (Show, Typeable, Generic)
-- Do I want to use GeneralizedNewtypeDeriving? I forget whether it is sound yet.
-- Probably depends on whether I'd want to use it in more than a couple places.
-- deriving (Show, Arbitrary)
instance NFData EventGenerator

instance Arbitrary EventGenerator where --newtypederivable
  arbitrary = fmap EventGenerator arbitrary
  shrink (EventGenerator g) = fmap EventGenerator (shrink g)

instance (Monad m) => Serial m EventGenerator where
  series = newtypeCons EventGenerator

encodingEventGenerator :: Encoding EventGenerator
encodingEventGenerator = wraptotal
  (\(EventGenerator vrc) -> vrc)
  EventGenerator
  (encodingVRCGenerator (AE.seq (interleavedpair
    encodingEntityId (encodingFieldValue testedFieldTypes))))

data PredictorGenerator = PredictorGenerator
    TestFieldType
    (FunFun EntityId (VRCGenerator (Maybe (BaseTime, EventGenerator))))
  deriving (Show, Typeable, Generic)
instance NFData PredictorGenerator

instance Arbitrary PredictorGenerator where
  arbitrary = liftM2 PredictorGenerator arbitrary arbitrary
  shrink (PredictorGenerator t f) =
    [PredictorGenerator t' f | t' <- shrink t] ++
    [PredictorGenerator t f' | f' <- shrink f]

instance (Monad m) => Serial m PredictorGenerator where
  series = cons2 PredictorGenerator

encodingPredictorGenerator :: Encoding PredictorGenerator
encodingPredictorGenerator = wraptotal
  (\(PredictorGenerator t f) -> (t, f))
  (\(t, f) -> PredictorGenerator t f)
  (interleavedpair encodingTestFieldType
    (encodingFunFun encodingEntityId (encodingVRCGenerator (AE.optional
      (interleavedpair integral encodingEventGenerator)))))

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
-- testing duplicate predictors would be good, but not at the cost
-- of almost ONLY testing duplicate predictors :P
--    ExtendedTime EntityFields [(ExtendedTime, EventGenerator)] [PredictorGenerator]
    ExtendedTime EntityFields (Map ExtendedTime EventGenerator) (Set PredictorGenerator)
  deriving (Show, Typeable, Generic)
instance NFData PristineTSIGenerator

instance Arbitrary PristineTSIGenerator where
  arbitrary = liftM4 PristineTSIGenerator arbitrary arbitrary arbitrary arbitrary
  shrink = genericShrink

instance (Monad m) => Serial m PristineTSIGenerator where
  series = cons4 PristineTSIGenerator

encodingPristineTSIGenerator :: Encoding PristineTSIGenerator
encodingPristineTSIGenerator = wraptotal
  (\(PristineTSIGenerator now efs fiat predictors) -> (now, efs, fiat, predictors))
  (\(now, efs, fiat, predictors) -> (PristineTSIGenerator now efs fiat predictors))
  (interleavedquad
    encodingExtendedTime 
    encodingEntityFields
    (AE.function encodingExtendedTime encodingEventGenerator)
    (AE.set encodingPredictorGenerator))

pristineTSIGeneratorToTSI :: PristineTSIGenerator -> TimeStewardInstance
pristineTSIGeneratorToTSI (PristineTSIGenerator now efs fiat predictors) =
  tSIpat now efs (Map.map eventGeneratorToEvent fiat)
    (List.map predictorGeneratorToPredictor (Set.toList predictors))
--  tSIpat now efs (Map.map eventGeneratorToEvent $ Map.fromList fiat)
--    (List.map predictorGeneratorToPredictor predictors)

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

dropEvery :: Int -> [x] -> [x]
dropEvery _ [] = []
dropEvery n (x:xs) = x : dropEvery n (List.drop n xs)

main :: IO ()
--main = runTests >>= print
main = defaultMain tests
--main = print (List.length (list 4 series :: [PristineTSIGenerator]))

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


