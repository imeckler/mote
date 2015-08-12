{-# LANGUAGE LambdaCase, NamedFieldPuns #-}
module Main where

import Scratch
import Mote.LoadFile
import Text.Parsec.String
import Text.Parsec
import Control.Applicative hiding ((<|>))
import qualified HsExpr
import HsExpr (HsExpr(..))
import qualified Type
import TypeRep
import RdrName (RdrName)
import qualified RdrName
import qualified Name
import qualified OccName
import qualified FastString
import Search.Types
import GHC
import Control.Monad.Error
import System.Exit
import GHC.Paths
import Mote.Types
import Mote.Util
import System.Directory
import System.IO
import System.FilePath
import Data.Maybe
import qualified System.Console.Readline as Readline
import qualified Mote.LoadFile as LoadFile
import UniqSupply
import qualified Mote.Search
import qualified Search.Graph
import qualified Mote.Init
import qualified Data.List as List
import Data.Function (on)
import qualified Data.HashSet as HashSet

data Command
  = Load FilePath
  | Search Int String
  | Reduce (HsExpr RdrName)
  | Exit

data Expr
  = Simple
  | FMap RdrName
  | Compose [RdrName]

parseCommand cmd =
  case words cmd of
    ["load", path] ->
      return (Just (Load path))

    ("search" : nstr : ":" : _rest) -> do
      let tyStr = tail (dropWhile (/= ':') cmd)
      liftIO $ print tyStr
      return (Just (Search (read nstr) tyStr))

    ws -> do
      liftIO (print ws)
      return Nothing

interpretCommand ref cmd =
  case cmd of
    Exit ->
      liftIO exitSuccess

    Load file ->
      runErrorT (LoadFile.loadFile ref file) >>= \case
        Right _ -> return ()
        Left err -> liftIO (print err)

    Search depthLimit tyStr ->
      runErrorT (Scratch.search ref tyStr depthLimit) >>= \case
        Left err ->
          liftIO (print err)
        Right gs ->
          liftIO $ putStrLn (showResults gs)
      where
      showResults =
        unlines
        . map (\(_,(t,_)) -> Search.Graph.renderAnnotatedTerm t)
        . List.sortBy (compare `on` fst)
        . map (\g ->
            let
              pr = (Search.Graph.toTerm g, g)
            in
            (Mote.Search.score pr, pr))
        . HashSet.toList
        . HashSet.fromList
        . map Search.Graph.moveListToGraph

    Reduce _ ->
      liftIO (putStrLn "Error. Reduce not implemented")

main = runWithTestRef main'

main' :: Ref MoteState -> Ghc ()
main' ref = do
  liftIO (Readline.readline "Λ > ") >>= \case
    Nothing -> do
      liftIO (putStr "\n")
      return ()

    Just str -> do
      liftIO (Readline.addHistory str)
      parseCommand str >>= \case
        Nothing -> return ()
        Just cmd -> interpretCommand ref cmd
      main' ref

runWithTestRef x = do
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
{-
hsExprToMoveSequence :: GhcMonad m => HsExpr RdrName -> m [Move () ()]
hsExprToMoveSequence hsExpr =
  case hsExpr of
    OpApp (L ss he) (L _ (HsVar op)) _ (L _ he') ->
      if rdrNameToString op == "."
      then liftA2 (++) (hsExprToMoveSequence he) (hsExprToMoveSequence he')
      else throwError "Unknown operator"

    HsVar rn ->
      _

    HsIPVar hipn -> _
    HsOverLit hol -> _
    HsLit hl -> _
    HsLam mg -> _
    HsLamCase pt mg -> _
    HsApp lhe lhe' -> _
    NegApp lhe se -> _
    HsPar lhe -> _
    SectionL lhe lhe' -> _
    SectionR lhe lhe' -> _
    ExplicitTuple lhtas b -> _
    HsCase lhe mg -> _
    HsIf m lhe lhe' lhe'' -> _
    HsMultiIf pt lgrhss -> _
    HsLet hlb lhe -> _
    HsDo hsc elss pt -> _
    ExplicitList pt m lhes -> _
    ExplicitPArr pt lhes -> _
    RecordCon l pte hrb -> _
    RecordUpd lhe hrb dcs pts pts' -> _
    ExprWithTySig lhe lht pr -> _
    ExprWithTySigOut lhe lht -> _
    ArithSeq pte m asi -> _
    PArrSeq pte asi -> _
    HsSCC st fs lhe -> _
    HsCoreAnn st fs lhe -> _
    HsBracket hb -> _
    HsRnBracketOut hb prss -> _
    HsTcBracketOut hb ptss -> _
    HsSpliceE b hs -> _
    HsQuasiQuoteE hqq -> _
    HsProc lp lhct -> _
    HsStatic lhe -> _
    HsArrApp lhe lhe' pt haat b -> _
    HsArrForm lhe m lhcts -> _
    HsTick t lhe -> _
    HsBinTick i i' lhe -> _
    HsTickPragma st fs_and_i_and_i_and_i_and_i lhe -> _
    EWildPat -> _
    EAsPat l lhe -> _
    EViewPat lhe lhe' -> _
    ELazyPat lhe -> _
    HsType lht -> _
    HsWrap hw he -> _
    HsUnboundVar rn -> _
  where
  rdrNameToString = FastString.unpackFS . OccName.occNameFS . Name.getOccName
-}
