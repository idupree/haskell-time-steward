{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables, DeriveDataTypeable, DeriveGeneric #-}
--{-# LANGUAGE GADTs, RankNTypes, ConstraintKinds, ImpredicativeTypes, ScopedTypeVariables, DeriveDataTypeable, DeriveGeneric #-}

module ExampleSim where

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

--import InefficientFlatTimeSteward as TSI
--import FlatTimeSteward as TSI
import CrossverifiedTimeStewards as TSI

type TSI = TimeStewardInstance

newtype Location = Location (Int, Int)
  deriving (Eq, Ord, Show, Typeable, Generic)
instance Serialize Location
instance FieldType Location where
  defaultFieldValue = Location (-1,-1)

newtype LastMove = LastMove BaseTime
  deriving (Eq, Ord, Show, Typeable, Generic)
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
      return (Just ((,) nextMoveTime (Event (\_valueRetriever' -> do
        -- TODO: maybe retrieve the location here rather than
        -- when the event is predicted?
        return [
            (entityId, FieldValue $ LastMove nextMoveTime),
            (entityId, FieldValue $ Location (x, (y + 1) `mod` 7))
          ]))))


  --return (Just (t + 3, \valueRetriever' -> do
  

predictors :: [Predictor]
predictors = [
    Predictor (Proxy::Proxy Location) predictor1,
    Predictor (Proxy::Proxy Location) wander
  ]

-- TODO should the user get a collisionResistantHash function
-- with different SipKey so that they don't accidentally make the same
-- hash as an internally derived thing? hmm

initialWorld :: TSI
initialWorld = TSI.makeTimeStewardInstance
  (beginningOfMoment 2)
  -- Haskell shares with C++ the lack of a nice literal syntax for maps
  (initializeEntityFields $ Map.fromList [
    (EntityId $ collisionResistantHash "your guy", [
        FieldValue $ Location (3,3),
        FieldValue $ LastMove 1
        ])
    ])
  predictors

showWorld :: TSI -> String
showWorld tsi = let
  places :: Map Location ()
  places = Map.fromList . List.map (\loc -> (loc, ())) . Map.elems $
    getEntityFieldsOfType (TSI.getEntityFieldStates tsi)
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
  "Time: " ++ show (TSI.getNow tsi) ++ "\n" ++ boardString ++ "\n"

main :: IO ()
main = do
  Prelude.putStrLn $ showWorld initialWorld
  forM_ [3..15] $ \t ->
    Prelude.putStrLn $ showWorld $ TSI.moveToFutureTime (beginningOfMoment t) $ initialWorld


{-
Things we can test:

Whether different TSIs do the same thing

Whether functions I claimed are "idempotent" do actually seem to be

Whether TSI.moveToFutureTime more or less frequently does a different thing (it shouldn't)
(plz include testing moves by less than a BaseTime tick)

Whether FTSI does the same thing if you do remakePrediction and/or initializePredictions
on it sporadically

Also: make the test sim have some fiat events and interacting actors


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


