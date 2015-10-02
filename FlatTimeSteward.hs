{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables, DeriveDataTypeable, DeriveGeneric #-}

module FlatTimeSteward (
  FlatTimeStewardInstance,
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

import qualified Control.Monad.Trans.Writer.Strict as WriterMonad

--An  Flat Time Steward Instance is (a time "now", x a set of non-default entity field states ((entity-id x field-type) -> value : field-type), x a collection of fiat event (Event, Time, distinguisher), x a function from a time >= "now" to a  Flat Time Steward Instance)  Also a way to alter the collection of fiat events, though that might be implied by it being a data structuer

--data EntityFieldState where
--  EntityFieldState :: (CanBeAnEntityFieldType f) => EntityId -> f -> EntityFieldState

type TimeStewardInstance = FlatTimeStewardInstance

data Prediction = Prediction {
  pPredictor :: !Predictor,
  pPredictorId :: !Word32,
  pAbout :: !EntityId,
  pDistinguisher :: !Distinguisher,
  pPredictorAccessed :: !(Set (EntityId, TypeRep)),
  pWhatWillHappen :: !(Maybe (ExtendedTime, Event))
  }

makeTimeStewardInstance :: ExtendedTime -> Map EntityId [Dynamic] -> [Predictor] -> FlatTimeStewardInstance
makeTimeStewardInstance now states predictors =
  initializePredictions $ FlatTimeStewardInstance {
    ftsiNow = now,
    ftsiEntityFieldStates = states,
    ftsiPredictedEvents = Map.empty,
    ftsiPredictionDependencies = Map.empty,
    ftsiFiatEvents = Map.empty,
    ftsiPredictors = predictors
  }

getNow :: FlatTimeStewardInstance -> ExtendedTime
getNow = ftsiNow

getFiatEvents :: FlatTimeStewardInstance -> Map ExtendedTime Event
getFiatEvents = ftsiFiatEvents

-- setFiatEvents deletes any ones that are in the past before storing them
setFiatEvents :: Map ExtendedTime Event -> FlatTimeStewardInstance -> FlatTimeStewardInstance
setFiatEvents events ftsi = ftsi {
    ftsiFiatEvents = snd (Map.split (ftsiNow ftsi) events)
  }

getEntityFieldStates :: FlatTimeStewardInstance -> Map EntityId [Dynamic]
getEntityFieldStates = ftsiEntityFieldStates


data FlatTimeStewardInstance = FlatTimeStewardInstance {
  ftsiNow :: !ExtendedTime, --BaseTime, -- All events before and during[?] this time have been executed
  ftsiEntityFieldStates :: !(Map EntityId [Dynamic]), --inefficient
  --ftsiPredictorResultCaches
  -- caches of results of predictors
  --ftsiPredictions :: ExtendedTime, collection of entityid+types, Event
  --key by field AND time order
  --we need to be able to id 

  -- Only the predictions that predict something.
  ftsiPredictedEvents :: !(Map ExtendedTime Prediction),
  -- all predictions even if they predict nothing, for each thing they access.
  -- 'Map Distinguisher' keys on the distinguisher in the Prediction.
  ftsiPredictionDependencies :: !(Map (EntityId, TypeRep) (Map Distinguisher Prediction)),

  ftsiFiatEvents :: !(Map ExtendedTime Event),

  -- this is supposed to be immutable:
  ftsiPredictors :: ![Predictor]
  }
--  deriving (Generic)
--instance Serialize FlatTimeStewardInstance

-- TODO: abstract this so the person using this module can't mess with the writer contents?
type ValueRetrieverMonad = WriterMonad.Writer (Set (EntityId, TypeRep))
-- TODO: think about what happens when the time steward client tries to
-- stow away a value-retriever and use it later in a context when one is
-- expected at a different time.  One way to prevent this is at the
-- type system using the ST monad's phantom 's' type variable hack.
-- If we don't prevent this, it makes a difference whether we're using
-- the old or new value retriever from the predictor or from the event :/
-- Also, we probably shouldn't leave old FlatTimeStewardInstance around
-- in the closure of something that's going to stick around for a while,
-- preventing the old world states from being garbage collected...
-- so maybe a Reader+Writer monad would make sense?

valueRetriever :: forall f. (FieldType f) => FlatTimeStewardInstance -> EntityId -> ValueRetrieverMonad f
valueRetriever ftsi entityId = do{-ValueRetrieverMonad-}
  WriterMonad.tell (Set.singleton (entityId, typeRep ([]::[f])))
  return $ fromMaybe (defaultFieldValue :: f) $ do{-Maybe monad-}
    fields <- Map.lookup entityId (ftsiEntityFieldStates ftsi)
    listToMaybe (Maybe.mapMaybe fromDynamic fields)

type NumberedPredictor = (Word32, Predictor)

--composeListOfEndomorphisms :: [a -> a] -> a -> a
-- = flip (foldl (flip id))
-- = appEndo . mconcat . map Endo
-- = Prelude.foldr (.) id

-- 'initializePredictions' is idempotent.
-- Also, for any complete FlatTimeStewardInstance, it should have no effect.
-- (TODO: define "complete" usefully, by using the word in any other
--  documentation.)
initializePredictions :: FlatTimeStewardInstance -> FlatTimeStewardInstance
initializePredictions ftsi = List.foldr (.) id
  [makePrediction numberedPredictor entityId |
    numberedPredictor <- List.zip [(1::Word32) ..] (ftsiPredictors ftsi),
    entityId <- Map.keys (ftsiEntityFieldStates ftsi)]
  ftsi

-- If the Predictor returns something in the past, it should
-- have the same result as a predictor that returns Nothing.
makePredictionObject :: FlatTimeStewardInstance -> NumberedPredictor -> EntityId -> Prediction
makePredictionObject ftsi (predictorNum, p@(Predictor pf)) entityId = let
  now = ftsiNow ftsi
  eventDistinguisher = collisionResistantHash (predictorNum, entityId)
  (maybeProtoWhatWillHappen, accessed) =
    WriterMonad.runWriter (pf (valueRetriever ftsi) entityId)
  maybeWhatWillHappen = do{-Maybe monad-}
    (eventBaseTime, event) <- maybeProtoWhatWillHappen
    eventTimeIterationNumber <- case compare eventBaseTime (etBaseTime now) of
      LT -> Nothing
      EQ -> -- As soon as possible that's in the future
            -- It is safe that this varies based on when the prediction is made
            -- because:
            -- [hopefully there will be a proof that uses some visualizations
            --  of timelines here]
            Just $
            if eventDistinguisher > etDistinguisher now
            then etIterationNumber now
            else etIterationNumber now + 1
      GT -> Just 0
    let eventExtendedTime = ExtendedTime eventBaseTime eventTimeIterationNumber eventDistinguisher
    return (eventExtendedTime, event)
  in
  Prediction {
    pPredictor = p,
    pPredictorId = predictorNum,
    pAbout = entityId,
    pDistinguisher = eventDistinguisher,
    pPredictorAccessed = accessed,
    pWhatWillHappen = maybeWhatWillHappen
  }

-- Used as part of the implementation of sounder things.
-- 'insertPrediction p' is idempotent.
insertPrediction :: Prediction -> FlatTimeStewardInstance -> FlatTimeStewardInstance
insertPrediction p ftsi = ftsi {
    ftsiPredictedEvents = (case pWhatWillHappen p of
      Nothing -> id
      Just (t, _) -> Map.insert t p) (ftsiPredictedEvents ftsi),
    ftsiPredictionDependencies =
      Map.unionWith Map.union
        (Map.fromSet (const (Map.singleton (pDistinguisher p) p)) (pPredictorAccessed p))
        (ftsiPredictionDependencies ftsi)
  }

-- Used as part of the implementation of sounder things.
-- 'deletePrediction p' is idempotent.
deletePrediction :: Prediction -> FlatTimeStewardInstance -> FlatTimeStewardInstance
deletePrediction p ftsi = let
  deleteTime = case pWhatWillHappen p of
    Just (t, _) -> Map.delete t
    Nothing -> id
  deleteAccessed = \m -> Map.differenceWith (\predictions _ ->
      case Map.delete (pDistinguisher p) predictions of
        ps | Map.null ps -> Nothing
           | otherwise -> Just ps
    ) m (Map.fromSet (const ()) (pPredictorAccessed p))
  in
  ftsi {
    ftsiPredictedEvents = deleteTime (ftsiPredictedEvents ftsi),
    ftsiPredictionDependencies = deleteAccessed (ftsiPredictionDependencies ftsi)
  }

-- 'makePrediction np entityId' is idempotent.
makePrediction :: NumberedPredictor -> EntityId -> FlatTimeStewardInstance -> FlatTimeStewardInstance
makePrediction np entityId ftsi =
  insertPrediction (makePredictionObject ftsi np entityId) ftsi

remakePrediction :: Prediction -> FlatTimeStewardInstance -> FlatTimeStewardInstance
remakePrediction p =
  makePrediction (pPredictorId p, pPredictor p) (pAbout p) . deletePrediction p

nextEvent :: FlatTimeStewardInstance -> Maybe (ExtendedTime, Event)
nextEvent ftsi = let
  -- the first, if any, of ftsiPredictedEvents and ftsiFiatEvents
  -- (that are in the future)
  now = ftsiNow ftsi
  firstFiatEvent = Map.lookupGT now (ftsiFiatEvents ftsi)
  firstPredictedEvent = fmap (\(_t, p) ->
      case pWhatWillHappen p of
        Just e -> e   -- assert (_t == fst e)
        Nothing -> error "bug: events that don't happen shouldn't be in ftsiPredictedEvents"
    ) $ Map.lookupGT now (ftsiPredictedEvents ftsi)
  events = Maybe.catMaybes [firstFiatEvent, firstPredictedEvent]
  timeOrderedEvents = sortBy (comparing fst) events
  in listToMaybe timeOrderedEvents

executeEvent :: ExtendedTime -> Event -> FlatTimeStewardInstance -> FlatTimeStewardInstance
-- unchecked precondition: the event is the next event
executeEvent eventTime (Event event) ftsi = let
  --now = ftsiNow ftsi
  valueRetrieverNow :: forall f. (FieldType f) => EntityId -> ValueRetrieverMonad f
  valueRetrieverNow = valueRetriever ftsi
  (changedEntityFields, _accessed) = WriterMonad.runWriter (event valueRetrieverNow)
  eventPrediction = Map.lookup eventTime (ftsiPredictedEvents ftsi)
  {-
  -- redundant with the fact that we decided to always recompute
  -- the current event (aside from deleting the fiat event, which we
  -- can do separately)
  deleteExecutedEventPrediction = case eventPrediction of
    Nothing -> --id  --not a predicted event, a fiat event
               --delete the past fiat event
      \f -> f { ftsiFiatEvents = Map.delete eventTime (ftsiFiatEvents f) }
    Just p -> deletePrediction p
  -}
  changedFieldIds = Map.fromSet (const ()) $
    entityFieldChangesToSetOfFieldIdsChanged changedEntityFields
  predictionsToRecompute :: Map Distinguisher Prediction
  predictionsToRecompute =
    Map.unions $ Map.elems $
    Map.intersection (ftsiPredictionDependencies ftsi) changedFieldIds
  predictionsToRecompute_list = Map.elems predictionsToRecompute
  remakePredictions =
    List.foldr (.) id (List.map remakePrediction predictionsToRecompute_list)
  --nonRecomputedPredictions =
  --  Map.difference (ftsiPredictionDependencies ftsi) changedFieldIds
  in
  -- Eli says you have to recompute the current prediction always
  -- Which could be implemented, or we could ban the corner case
  -- to make it easier to debug some accidental infinite loops:
  case eventPrediction of
    Just p | Map.notMember (pDistinguisher p) predictionsToRecompute
      -> error "maybe this is an error to have a prediction that keeps happening?"
    _ ->
      remakePredictions $
      -- deleteExecutedEventPrediction $
      ftsi {
        ftsiNow = eventTime,
        ftsiEntityFieldStates = updateEntityFields changedEntityFields
                                  (ftsiEntityFieldStates ftsi),
        -- (if it's not a fiat event, the deletion will have no effect)
        ftsiFiatEvents = Map.delete eventTime (ftsiFiatEvents ftsi)
      }




moveToFutureTime :: ExtendedTime -> FlatTimeStewardInstance -> FlatTimeStewardInstance
moveToFutureTime futureT ftsi
  | futureT >= ftsiNow ftsi =
    case nextEvent ftsi of
      Nothing -> ftsi { ftsiNow = futureT }
      Just (eventTime, event)
        | eventTime > futureT -> ftsi { ftsiNow = futureT }
        | otherwise ->
          let ftsi' = executeEvent eventTime event ftsi
          in moveToFutureTime futureT ftsi'
  | otherwise = error "not defined for past times"


--data Buggy = Buggy | Okay
--testPredictorForObviousBugs :: Predictor -> Buggy
--testPredictorForObviousBugs (Predictor p) =




