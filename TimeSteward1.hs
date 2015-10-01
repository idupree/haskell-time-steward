{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables, DeriveDataTypeable, DeriveGeneric #-}
--{-# LANGUAGE GADTs, RankNTypes, ConstraintKinds, ImpredicativeTypes, ScopedTypeVariables, DeriveDataTypeable, DeriveGeneric #-}

module TimeSteward1 where

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

-- A Time Steward is a tuple of a time-type, an arbitrary tuple of entity field types, and an arbitrary tuple of predictors




data UInt128 = UInt128 {-#UNPACK#-}!Word64 {-#UNPACK#-}!Word64
  deriving (Eq, Ord, Generic)
instance Serialize UInt128
-- allow some numeric literals but any other Num operation is an error
-- (we don't need to bother implementing the rest)
-- TODO implement them by wrapping toInteger/fromIn
instance Num UInt128 where
  fromInteger n | n >= 0 && n <= 0xffffffffffffffffffffffffffffffff =
    case n `divMod` 0x10000000000000000 of
      (hi, lo) -> UInt128 (fromInteger hi) (fromInteger lo)
  fromInteger _ = error "UInt128: fromInteger: out of range"
  a + b = fromInteger (toInteger a + toInteger b)
  a - b = fromInteger (toInteger a - toInteger b)
  a * b = fromInteger (toInteger a * toInteger b)
  abs = id
  signum = fromInteger . signum . toInteger
  negate = fromInteger . negate . toInteger
instance Real UInt128 where
  toRational i = fromInteger (toInteger i)
instance Enum UInt128 where
  succ = fromInteger . succ . toInteger
  pred = fromInteger . pred . toInteger
  toEnum = fromIntegral
  fromEnum = fromIntegral
  enumFrom = List.map fromInteger . enumFrom . toInteger
  enumFromThen a b = List.map fromInteger (enumFromThen (toInteger a) (toInteger b))
  enumFromTo a b = List.map fromInteger (enumFromTo (toInteger a) (toInteger b))
  enumFromThenTo a b c = List.map fromInteger (enumFromThenTo (toInteger a) (toInteger b) (toInteger c))
instance Integral UInt128 where
  toInteger (UInt128 hi lo) = toInteger hi * 0x10000000000000000 + toInteger lo
  a `quot` b = fromInteger (toInteger a `quot` toInteger b)
  a `rem` b = fromInteger (toInteger a `rem` toInteger b)
  a `quotRem` b = case (toInteger a `quotRem` toInteger b) of (c, d) -> (fromInteger c, fromInteger d)
  a `div` b = fromInteger (toInteger a `div` toInteger b)
  a `mod` b = fromInteger (toInteger a `mod` toInteger b)
  a `divMod` b = case (toInteger a `divMod` toInteger b) of (c, d) -> (fromInteger c, fromInteger d)

instance Show UInt128 where
  --show (UInt128 hi lo) = show (toInteger hi * 0x10000000000000000 + toInteger lo)
  show i = printf "0x%016x" (toInteger i)

-- generated by crypto random number generator, although
-- they maybe don't even have to be random given they are
-- not secret
sipkey1, sipkey2 :: SipKey
sipkey1 = SipKey 0xb82a9426fd1a574f 0x9d9d5b703dcb1bcc
sipkey2 = SipKey 0x03e0d6037ff980a4 0x65b790a0825b83bd
collisionResistantHash :: (Serialize a) => a -> UInt128
collisionResistantHash a = let
  b :: ByteString
  b = encode a
  SipHash h1 = sipHash sipkey1 b
  SipHash h2 = sipHash sipkey2 b
  in UInt128 h1 h2

data EntityId = EntityId UInt128
  deriving (Eq, Ord, Generic)
instance Serialize EntityId
instance Show EntityId where
  show (EntityId n) = "entity:" ++ show n

--data Distinguisher = Distinguisher UInt128 -- normally a hash and therefore statistically never zero or maximum, which matters for beginningOfTime being clear
type Distinguisher = UInt128

type NumberOfTimesTheComputerCanDoSomething = Word64
data ExtendedTime = ExtendedTime {
  etBaseTime :: !BaseTime,
  etIterationNumber :: !NumberOfTimesTheComputerCanDoSomething,
  etDistinguisher :: !Distinguisher
  }
  deriving (Eq, Ord, Generic)
instance Serialize ExtendedTime
instance {-(Show BaseTime) =>-} Show ExtendedTime where
  show et = show (etBaseTime et) ++ "::" ++ show (etIterationNumber et) ++ "::" ++ show (etDistinguisher et)

createExtendedTime :: (Serialize d) => BaseTime -> d -> ExtendedTime
createExtendedTime t d = ExtendedTime t 0 (collisionResistantHash ("createExtendedTime", d))

beginningOfMoment :: BaseTime -> ExtendedTime
beginningOfMoment t = ExtendedTime t 0 0


class (Typeable f, Serialize f) => FieldType f where
  defaultFieldValue :: f

--type ValueRetriever m = (forall f. (FieldType f) => EntityId -> Proxy f -> m f)
--type EntityValueTuple = (forall f. (FieldType f) => (EntityId, Proxy f, f))

type ValueRetriever m = (forall f. (FieldType f) => EntityId -> m f)

-- the Dynamic must be one of the entity field types...
type EntityValueTuple = (EntityId, Dynamic)


-- is there some way we can make a visualizer of entanglement?


-- It's common for predictors to return one thing.
-- It would be fine if they return a maximum of one thing, because you never would get to the second thing unless the first thing is in the past.
-- Predictors usually get the time from the data of one/some of the entities they access. For example if you have a
-- bubble wand that emits bubbles every second then the wand could store the time at which it last emitted a bubble.
-- Predictors maybe have to return nothing for entities with all default/null values.
--type Predictor = forall m. (Monad m) => EntityId -> (forall f. (FieldType f) => EntityId -> Proxy f -> m f) -> m [(Time, Event)]
newtype Predictor where
  Predictor :: (forall m. (Monad m) => ValueRetriever m -> EntityId -> m (Maybe (BaseTime, Event))) -> Predictor
  --Predictor :: (forall m. (Monad m) => ValueRetriever m -> EntityId -> m [(Time, Event)]) -> Predictor

--type Event = forall m. (Monad m) => ValueRetriever m -> m [EntityValueTuple]
newtype Event where
  Event :: (forall m. (Monad m) => ValueRetriever m -> m [EntityValueTuple]) -> Event




-- For now so the haskell compiles with less work, i'll
type BaseTime = Integer



