{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables, DeriveDataTypeable, DeriveGeneric #-}

module InefficientFlatTimeSteward (
  InefficientFlatTimeStewardInstance,
  TimeStewardInstance,
  moveToFutureTime,
  makeTimeStewardInstance,
  getNow,
  getFiatEvents,
  setFiatEvents,
  getEntityFieldStates
  ) where

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

type TimeStewardInstance = InefficientFlatTimeStewardInstance

--An Inefficient Flat Time Steward Instance is (a time "now", x a set of non-default entity field states ((entity-id x field-type) -> value : field-type), x a collection of fiat event (Event, Time, distinguisher), x a function from a time >= "now" to a Inefficient Flat Time Steward Instance)  Also a way to alter the collection of fiat events, though that might be implied by it being a data structuer

--data EntityFieldState where
--  EntityFieldState :: (CanBeAnEntityFieldType f) => EntityId -> f -> EntityFieldState

data InefficientFlatTimeStewardInstance = InefficientFlatTimeStewardInstance {
  iftsiNow :: !ExtendedTime, --BaseTime, -- All events before and during[?] this time have been executed
  iftsiEntityFieldStates :: !EntityFields,
  -- iftsiFiatEvents may contain events in the past, but they don't do anything,
  -- so it's the same whether they are present or not.
  -- The key is like an ExtendedTime where the second part (iteration number) is implicitly zero.
  -- TODO make sure the distinguisher is a hash
  --iftsiFiatEvents = Map (BaseTime, Distinguisher) Event -- may not be needed to order them this much but it is ok to unique them and order like this
  iftsiFiatEvents :: !(Map ExtendedTime Event),
  -- this is supposed to be immutable:
  iftsiPredictors :: ![Predictor]
  }
--  deriving (Generic)
--instance Serialize InefficientFlatTimeStewardInstance

makeTimeStewardInstance :: ExtendedTime -> EntityFields -> [Predictor] -> InefficientFlatTimeStewardInstance
makeTimeStewardInstance now states predictors =
  InefficientFlatTimeStewardInstance {
    iftsiNow = now,
    iftsiEntityFieldStates = states,
    iftsiFiatEvents = Map.empty,
    iftsiPredictors = predictors
  }

getNow :: InefficientFlatTimeStewardInstance -> ExtendedTime
getNow = iftsiNow

getFiatEvents :: InefficientFlatTimeStewardInstance -> Map ExtendedTime Event
getFiatEvents = iftsiFiatEvents

-- setFiatEvents deletes any ones that are in the past before storing them
-- TODO: do that in the inefficient time steward when events are executed too
setFiatEvents :: Map ExtendedTime Event -> InefficientFlatTimeStewardInstance -> InefficientFlatTimeStewardInstance
setFiatEvents events iftsi = iftsi {
    iftsiFiatEvents = snd (Map.split (iftsiNow iftsi) events)
  }

getEntityFieldStates :: InefficientFlatTimeStewardInstance -> EntityFields
getEntityFieldStates = iftsiEntityFieldStates

-- this is the inefficient time steward so we don't need
-- to store which things were accessed by predictors
valueRetriever :: forall f. (FieldType f) => InefficientFlatTimeStewardInstance -> EntityId -> Identity f
valueRetriever iftsi entityId = Identity $ getEntityField entityId (iftsiEntityFieldStates iftsi)

nextEvent :: InefficientFlatTimeStewardInstance -> Maybe (ExtendedTime, Event)
nextEvent iftsi = let
  now = iftsiNow iftsi
  firstFiatEvent :: Maybe (ExtendedTime, Event)
  firstFiatEvent = Map.lookupGT now (iftsiFiatEvents iftsi)
    --do{-Maybe monad-}
    --((baseTime, distinguisher), event) <- (Map.lookupGT now (iftsiFiatEvents iftsi)
    --return (ExtendedTime baseTime 0 distinguisher, event)
  valueRetrieverNow :: forall f. (FieldType f) => EntityId -> Identity f
  valueRetrieverNow = valueRetriever iftsi
  -- here's the inefficient part
  predictedEvents :: [(ExtendedTime, Event)]
  predictedEvents = do{-List monad-}
    (predictorNum, predictor) <- List.zip [(1::Word32) ..] (iftsiPredictors iftsi)
    -- Can't be a 'let' because it binds a GADT type variable:
    -- needs to be structurally obvious to GHC that it is a strict binding.
    Predictor (_ :: Proxy fieldType) p <- return predictor
    entityId <- Map.keys (getEntityFieldsOfType (iftsiEntityFieldStates iftsi) :: Map EntityId fieldType)
    -- This line is hopefully redundant now because default field values
    -- are not stored:
    Monad.guard (runIdentity (valueRetrieverNow entityId) /= (defaultFieldValue :: fieldType))
    (eventBaseTime, event) <- maybeToList (runIdentity (p valueRetrieverNow entityId))
    let eventTimeDistinguisher = collisionResistantHash (predictorNum, entityId)
    eventTimeIterationNumber <- case compare eventBaseTime (etBaseTime now) of
      LT -> []
      EQ -> -- eli thinks it's important to place it at the soonest possible iteration, rather than any future iteration in this base time?
            if eventTimeDistinguisher > etDistinguisher now
            then [etIterationNumber now]
            else [etIterationNumber now + 1]
      GT -> [0]
    let eventExtendedTime = ExtendedTime eventBaseTime eventTimeIterationNumber eventTimeDistinguisher
    return (eventExtendedTime, event)
  events = maybeToList firstFiatEvent ++ predictedEvents
  -- sortOn not defined in older GHC
  timeOrderedEvents = sortBy (comparing fst) events
  in
  listToMaybe timeOrderedEvents

executeEvent :: ExtendedTime -> Event -> InefficientFlatTimeStewardInstance -> InefficientFlatTimeStewardInstance
-- unchecked precondition: the event is the next event
executeEvent eventTime (Event event) iftsi = let
  --now = iftsiNow iftsi
  valueRetrieverNow :: forall f. (FieldType f) => EntityId -> Identity f
  valueRetrieverNow = valueRetriever iftsi
  changedEntityFields = runIdentity (event valueRetrieverNow)
  in
  iftsi {
    iftsiNow = eventTime,
    iftsiEntityFieldStates = setEntityFieldsNonuniform changedEntityFields (iftsiEntityFieldStates iftsi),
    -- (if it's not a fiat event, the deletion will have no effect)
    iftsiFiatEvents = Map.delete eventTime (iftsiFiatEvents iftsi)
  }




moveToFutureTime :: ExtendedTime -> InefficientFlatTimeStewardInstance -> InefficientFlatTimeStewardInstance
moveToFutureTime futureT iftsi
  | futureT >= iftsiNow iftsi =
    case nextEvent iftsi of
      Nothing -> iftsi { iftsiNow = futureT }
      Just (eventTime, event)
        | eventTime > futureT -> iftsi { iftsiNow = futureT }
        | otherwise ->
          let iftsi' = executeEvent eventTime event iftsi
          in moveToFutureTime futureT iftsi'
  | otherwise = error "not defined for past times"


--data Buggy = Buggy | Okay
--testPredictorForObviousBugs :: Predictor -> Buggy
--testPredictorForObviousBugs (Predictor p) =




