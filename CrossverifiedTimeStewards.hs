{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables, DeriveDataTypeable, DeriveGeneric #-}

module CrossverifiedTimeStewards (
  CrossverifiedTimeStewardsInstance,
  TimeStewardInstance,
  moveToFutureTime,
  makeTimeStewardInstance,
  getNow,
  getFiatEvents,
  setFiatEvents,
  getEntityFieldStates,
  getPredictors
  ) where

import TimeSteward1
import qualified InefficientFlatTimeSteward as IFTSI
import qualified FlatTimeSteward as FTSI

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

type TimeStewardInstance = CrossverifiedTimeStewardsInstance

data CrossverifiedTimeStewardsInstance = CrossverifiedTimeStewardsInstance {
  ctsiCurrentIFTSI :: !IFTSI.TimeStewardInstance,
  ctsiCurrentFTSI :: !FTSI.TimeStewardInstance
  -- todo: more stuff
  }

allEqual :: (Eq a) => [a] -> Bool
allEqual [] = True
allEqual (x:xs) = List.all (x ==) xs

-- throws exception if inconsistent
crossverify :: CrossverifiedTimeStewardsInstance -> CrossverifiedTimeStewardsInstance
crossverify ctsi = if
  allEqual [
    IFTSI.getEntityFieldStates (ctsiCurrentIFTSI ctsi),
    FTSI.getEntityFieldStates (ctsiCurrentFTSI ctsi)
  ] &&
  -- Events have functions, so they can't be compared
  -- Luckily they are mostly just whatever the user supplies
  -- We can compare the comparable parts, though, to make sure
  -- they are getting deleted at the same consistent rate.
  allEqual [
    Map.keys (IFTSI.getFiatEvents (ctsiCurrentIFTSI ctsi)),
    Map.keys (FTSI.getFiatEvents (ctsiCurrentFTSI ctsi))
  ] &&
  allEqual [
    IFTSI.getNow (ctsiCurrentIFTSI ctsi),
    FTSI.getNow (ctsiCurrentFTSI ctsi)
  ]
  then ctsi
  else error "time steward instance crossverification failed"


makeTimeStewardInstance :: ExtendedTime -> EntityFields -> [Predictor] -> CrossverifiedTimeStewardsInstance
makeTimeStewardInstance now states predictors =
  crossverify $ CrossverifiedTimeStewardsInstance {
    ctsiCurrentIFTSI = IFTSI.makeTimeStewardInstance now states predictors,
    ctsiCurrentFTSI = FTSI.makeTimeStewardInstance now states predictors
  }

getNow :: CrossverifiedTimeStewardsInstance -> ExtendedTime
getNow = FTSI.getNow . ctsiCurrentFTSI

getFiatEvents :: CrossverifiedTimeStewardsInstance -> Map ExtendedTime Event
getFiatEvents = FTSI.getFiatEvents . ctsiCurrentFTSI

getPredictors :: CrossverifiedTimeStewardsInstance -> [Predictor]
getPredictors = FTSI.getPredictors . ctsiCurrentFTSI

setFiatEvents :: Map ExtendedTime Event -> CrossverifiedTimeStewardsInstance -> CrossverifiedTimeStewardsInstance
setFiatEvents events ctsi = crossverify $ ctsi {
    ctsiCurrentIFTSI = IFTSI.setFiatEvents events (ctsiCurrentIFTSI ctsi),
    ctsiCurrentFTSI = FTSI.setFiatEvents events (ctsiCurrentFTSI ctsi)
  }

getEntityFieldStates :: CrossverifiedTimeStewardsInstance -> EntityFields
getEntityFieldStates = FTSI.getEntityFieldStates. ctsiCurrentFTSI

moveToFutureTime :: ExtendedTime -> CrossverifiedTimeStewardsInstance -> CrossverifiedTimeStewardsInstance
moveToFutureTime futureT ctsi = crossverify $ ctsi {
    ctsiCurrentIFTSI = IFTSI.moveToFutureTime futureT (ctsiCurrentIFTSI ctsi),
    ctsiCurrentFTSI = FTSI.moveToFutureTime futureT (ctsiCurrentFTSI ctsi)
  }



