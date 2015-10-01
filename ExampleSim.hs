{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables, DeriveDataTypeable, DeriveGeneric #-}
--{-# LANGUAGE GADTs, RankNTypes, ConstraintKinds, ImpredicativeTypes, ScopedTypeVariables, DeriveDataTypeable, DeriveGeneric #-}

module ExampleSim where

import TimeSteward1
import InefficientFlatTimeSteward

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


newtype Location = Location (Int, Int)
  deriving (Eq, Ord, Typeable, Generic)
instance Serialize Location
instance FieldType Location where
  defaultFieldValue = Location (-1,-1)

newtype LastMove = LastMove BaseTime
  deriving (Eq, Ord, Typeable, Generic)
instance Serialize LastMove
instance FieldType LastMove where
  defaultFieldValue = LastMove 0

predictor1, wander :: forall m. (Monad m) => ValueRetriever m -> EntityId -> m (Maybe (BaseTime, Event))
predictor1 _valueRetriever _entityId = return Nothing

wander valueRetriever entityId = do
  Location (loc@(x,y)) <- valueRetriever entityId
  if (Location loc == defaultFieldValue)
    then return Nothing
    else do
      LastMove t <- valueRetriever entityId
      let nextMoveTime = t + 3
      --return $ Just $ (,) nextMoveTime $ \valueRetriever' -> do
      return (Just ((,) nextMoveTime (Event (\valueRetriever' -> do
        -- TODO: maybe retrieve the location here rather than
        -- when the event is predicted?
        return [
            (entityId, toDyn $ LastMove nextMoveTime),
            (entityId, toDyn $ Location (x, (y + 1) `mod` 7))
          ]))))


  --return (Just (t + 3, \valueRetriever' -> do
  

predictors :: [Predictor]
predictors = [Predictor predictor1, Predictor wander]

-- TODO should the user get a collisionResistantHash function
-- with different SipKey so that they don't accidentally make the same
-- hash as an internally derived thing? hmm

initialWorld :: InefficientFlatTimeStewardInstance
initialWorld = InefficientFlatTimeStewardInstance {
  iftsiNow = beginningOfMoment 2,
  -- Haskell shares with C++ the lack of a nice literal syntax for maps
  iftsiEntityFieldStates = Map.fromList [
    (EntityId $ collisionResistantHash "your guy", [toDyn $ Location (3,3), toDyn $ LastMove 1])
    ],
  iftsiFiatEvents = Map.fromList [],
  iftsiPredictors = predictors
  }

showWorld :: InefficientFlatTimeStewardInstance -> String
showWorld iftsi = let
  places :: Map Location ()
  places = Map.fromList . List.map (\loc -> (loc, ())) .
             Maybe.mapMaybe Dynamic.fromDynamic .
             List.concat . Map.elems $ (iftsiEntityFieldStates iftsi)
  -- Not [[Char]] because some single-width grapheme clusters are
  -- multiple codepoints
  board :: [[String]]
  board = flip List.map [0..6] $ \y ->
    flip List.map [0..6] $ \x ->
      case Map.lookup (Location (x,y)) places of
        Nothing -> "·"
        Just _ -> "é"
  boardString :: String
  boardString = List.concat . List.intersperse "\n" . List.map List.concat . List.reverse $ board
  in
  "Time: " ++ show (iftsiNow iftsi) ++ "\n" ++ boardString ++ "\n"

main = do
  Prelude.putStrLn $ showWorld initialWorld
  forM_ [3..15] $ \t ->
    Prelude.putStrLn $ showWorld $ moveIFTSIToFutureTime (beginningOfMoment t) $ initialWorld


