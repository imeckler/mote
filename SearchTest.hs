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
import qualified Data.List as List
import Data.Function (on)
import qualified Mote.Search

data RunInfo
  = RunInfo
  { numberOfMoveSequences :: Int
  , numberOfGraphs :: Int
  , moveSequencesTime :: Double
  , deduplicationTime :: Double
  , graphsTime :: Double
  , searchType :: String
  , depth :: Int
  , fileName :: String
  , terms :: [String]
  , moveSeqTerms :: [String]
  , top20ShrunkSize :: Int
  }
  deriving (Show, Read)

data TestCase
  = TestCase
  { source :: Word SyntacticFunctor WrappedType
  , target :: Word SyntacticFunctor WrappedType
  , testCaseDepth :: Int
  }

tests =
  [ ( "testmodules/Test1.hs"
    , [ "Either String (IO Int) -> IO (Maybe String)"
      , "[FakeFilePath] -> IO Data.ByteString.ByteString"
      , "[Maybe FakeFilePath] -> IO [Data.ByteString.ByteString]"
      , "[Maybe (Either String a)] -> Maybe a"
      , "[Maybe (Either String a)] -> [a]"
      , "[Maybe (ErrorT String IO a)] -> IO (Maybe a)"
      , "ErrorT String Ghc Int -> IO (Maybe Int)"
      , "(Bool, [Maybe a]) -> [(Bool, a)]"
      , "TcRn a -> IO a"
      ]
    )
    {-
  , ( "testmodules/MuchInScope.hs"
    , [ "Either String (IO Int) -> IO (Maybe String)"
      , "[ErrorT String Ghc (Maybe a)] -> IO [a]"
      ]
    ) -}
  ]

searchDepths = [3..5]

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
    forM_ tests $ \(fileName, searchTypes) -> do
      runErrorT (Mote.LoadFile.loadFile ref fileName) >>= \case
        Left err -> do
          error (show err)

        Right () -> do
          Right (chooseAType, innerVar) <- runErrorT (chooseATypeData <$> getFileDataErr ref)
          -- Just to force chooseAType
          length (ChooseAType.allData chooseAType) `seq` return ()

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

                  let
                    terms = 
                      take 20
                      . map (\(_,(t,_)) -> Search.Graph.renderAnnotatedTerm t)
                      . List.sortBy (compare `on` fst)
                      . map (\g ->
                          let
                            pr = (Search.Graph.toTerm g, g)
                          in
                          (Mote.Search.score pr, pr))
                      $ gsFromMoveSeqs

                    moveSeqTerms =
                      map (\(_, (t, _)) -> Search.Graph.renderAnnotatedTerm t) $ take 20 moveSeqPairs

                    topMoveSeqs = map (\(_, (_, seq)) -> seq) moveSeqPairs

                    wouldBeTopMoveSeqGraphs =
                      take 20
                      . map (\(_,(_,g)) -> g)
                      . List.sortBy (compare `on` fst)
                      . map (\g ->
                          let
                            pr = (Search.Graph.toTerm g, g)
                          in
                          (Mote.Search.score pr, pr))
                      . map moveListToGraph
                      $ mss

                    moveSeqPairs =
                    {-
                      take 20
                      . map (\(_, (t, _)) -> Search.Graph.renderAnnotatedTerm t) -}
                      List.sortBy (compare `on` fst)
                      . map (\moveSeq ->
                          let pr = (Search.Graph.moveSequenceToAnnotatedTerm moveSeq, moveSeq)
                          in (Mote.Search.moveSequenceScore pr, pr))
                      $ mss

                  liftIO . print $
                    RunInfo
                    { numberOfMoveSequences = length mss
                    , numberOfGraphs = length gsFromMoveSeqs
                    , deduplicationTime
                    , moveSequencesTime
                    , graphsTime
                    , searchType = tyStr
                    , depth = testCaseDepth
                    , fileName
                    , terms
                    , moveSeqTerms
                    , top20ShrunkSize =
                        HashSet.size  (HashSet.fromList wouldBeTopMoveSeqGraphs)
                        -- HashSet.size (HashSet.fromList (map moveListToGraph topMoveSeqs))
                    }

                Left err -> liftIO (print err)


searchGraphs chooseAType innerVar (TestCase {source, target, testCaseDepth}) =
  let
    matchesForWord
      :: Word SyntacticFunctor WrappedType
      -> [(Word SyntacticFunctor WrappedType, Search.Types.Move SyntacticFunctor WrappedType)]
    matchesForWord =
      concatMap (matchesInView' innerVar chooseAType) . either (map Left) (map Right) . Word.suffixViews
  in
  graphsOfSizeAtMostMemo' matchesForWord testCaseDepth source target

searchMoveSeqs chooseAType innerVar (TestCase {source, target, testCaseDepth}) =
  let
    matchesForWord
      :: Word SyntacticFunctor WrappedType
      -> [(Word SyntacticFunctor WrappedType, Search.Types.Move SyntacticFunctor WrappedType)]
    matchesForWord =
      concatMap (matchesInView' innerVar chooseAType) . either (map Left) (map Right) . Word.suffixViews
  in
  moveSequencesOfSizeAtMostMemoNotTooHoley' matchesForWord testCaseDepth source target

--TODO: heuristic: never permit > 2 of the same letter in a row
