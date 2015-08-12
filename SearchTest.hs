{-# LANGUAGE NamedFieldPuns, LambdaCase #-}
module Main where

import Prelude hiding (Word)

import System.TimeIt
import Scratch
import Type
import Mote.Types
import Mote.Util
import Control.Monad.Error
import GHC
import Mote.ReadType
import qualified Search.Types
import Mote.Search.NatTransData
import Mote.Search.WrappedType
import qualified Search.Types.Word as Word
import Search.Types.Word (Word)
import Search.Graph
import qualified Mote.Init
import System.Directory
import System.IO
import System.FilePath
import           GHC.Paths
import UniqSupply
import qualified Mote.LoadFile
import qualified Data.HashSet as HashSet
import qualified Mote.Search.ChooseAType as ChooseAType

data RunInfo
  = RunInfo
  { numberOfMoveSequences :: Int
  , numberOfGraphs :: Int
  , moveSequencesTime :: Double
  , deduplicationTime :: Double
  , graphsTime :: Double
  , searchType :: String
  , depth :: Int
  }
  deriving (Show)

data TestCase
  = TestCase
  { source :: Word SyntacticFunctor WrappedType
  , target :: Word SyntacticFunctor WrappedType
  , testCaseDepth :: Int
  }

searchTypes =
  [ "Either String (IO Int) -> IO (Maybe String)"
  , "[ErrorT String Ghc (Maybe a)] -> IO [a]"
  ]

searchDepths = [1..4]

runWithTestRef' x = do
  home <- getHomeDirectory
  withFile (home </> "testlog") WriteMode $ \logFile -> do
    r <- newRef =<< initialState logFile
    runGhc (Just libdir) $ do { Mote.Init.initializeWithCabal r; x r }
  where
  initialState :: Handle -> IO MoteState
  initialState logFile = mkSplitUniqSupply 'x' >>| \uniq -> MoteState
    { fileData = Nothing
    , currentHole = Nothing
    , argHoles = mempty
    , loadErrors = []
    , logFile
    , uniq
    }


main =
  runWithTestRef' $ \ref -> do
    Right () <- runErrorT $ Mote.LoadFile.loadFile ref "Test.hs"
    Right (chooseAType, innerVar) <- runErrorT (chooseATypeData <$> getFileDataErr ref)
    -- Just to force chooseAType
    liftIO . print . length . ChooseAType.allData $ chooseAType

    forM_ searchTypes $ \tyStr -> do
      forM_ searchDepths $ \testCaseDepth -> do
        runErrorT (interpretType =<< readType tyStr) >>= \case
          Right (source, target) -> do
            (graphsTime, gs) <- liftIO . timeItT $
              let gs = searchGraphs chooseAType innerVar (TestCase source target testCaseDepth) in
              gs `seq` return gs

            (moveSequencesTime, (mss, gsFromMoveSeqs)) <- liftIO . timeItT $
              let mss = searchMoveSeqs chooseAType innerVar (TestCase source target testCaseDepth)
                  gs = HashSet.toList (HashSet.fromList (map moveListToGraph mss))
              in
              gs `seq` return (mss, gs)

            (deduplicationTime, gs') <- liftIO . timeItT $
              let gs' = HashSet.toList (HashSet.fromList (map moveListToGraph mss)) in
              gs' `seq` return gs'

            liftIO . print $
              RunInfo
              { numberOfMoveSequences = length mss
              , numberOfGraphs = length gsFromMoveSeqs
              , deduplicationTime
              , moveSequencesTime
              , graphsTime
              , searchType = tyStr
              , depth = testCaseDepth
              }

          Left err -> liftIO (print err)


searchGraphs chooseAType innerVar (TestCase {source, target, testCaseDepth}) =
  let
    matchesForWord
      :: Word SyntacticFunctor WrappedType
      -> [(Word SyntacticFunctor WrappedType, Search.Types.Move SyntacticFunctor WrappedType)]
    matchesForWord =
      concatMap (matchesInView' innerVar chooseAType) . Word.views
  in
  graphsOfSizeAtMostMemo' matchesForWord testCaseDepth source target

searchMoveSeqs chooseAType innerVar (TestCase {source, target, testCaseDepth}) =
  let
    matchesForWord
      :: Word SyntacticFunctor WrappedType
      -> [(Word SyntacticFunctor WrappedType, Search.Types.Move SyntacticFunctor WrappedType)]
    matchesForWord =
      concatMap (matchesInView' innerVar chooseAType) . Word.views
  in
  moveSequencesOfSizeAtMostMemoNotTooHoley' matchesForWord testCaseDepth source target

--TODO: heuristic: never permit > 2 of the same letter in a row
