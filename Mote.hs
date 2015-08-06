{-# LANGUAGE LambdaCase, NamedFieldPuns, OverloadedStrings, RecordWildCards,
             ScopedTypeVariables, TupleSections #-}
module Main where

import           Control.Applicative        ((<$>))
import           Control.Concurrent         (forkIO)
import           Control.Monad.Error
import           Data.Aeson                 (decodeStrict, encode, (.=))
import qualified Data.Aeson                 as Aeson
import qualified Data.ByteString            as B
import qualified Data.ByteString.Lazy.Char8 as LB8
import qualified Data.List                  as List
import qualified Data.Map                   as M
import qualified Data.Set                   as S
import Data.Function (on)


import qualified DynFlags
import           FastString                 (fsLit)
import           GHC                        hiding (exprType)
import           GHC.Paths
import           Name
import           Outputable
import           UniqSupply                 (mkSplitUniqSupply)

import           System.Directory           (getHomeDirectory)
import           System.Exit                (ExitCode (..), exitWith)
import           System.FilePath
import           System.IO

import           Mote.Case
import           Mote.GhcUtil
import           Mote.Holes
import qualified Mote.Init
import           Mote.LoadFile             (loadFile)
import           Mote.Protocol
import           Mote.Refine
import           Mote.Suggest              (getAndMemoizeSuggestions)
import           Mote.Types
import           Mote.Util
import qualified Mote.Search
import qualified Search.Graph
import qualified Search.Graph.Types

-- TODO: DEBUG
import Scratch

getEnclosingHole :: Ref MoteState -> (Int, Int) -> M (Maybe AugmentedHoleInfo)
getEnclosingHole stRef pos =
  M.foldrWithKey (\k hi r -> if k `spans` pos then Just hi else r) Nothing
  . holesInfo
  <$> getFileDataErr stRef
-- TODO: access ghci cmomands from inside vim too. e.g., kind

srcLocPos :: SrcLoc -> (Int, Int)
srcLocPos (RealSrcLoc l)  = (srcLocLine l, srcLocCol l)
srcLocPos UnhelpfulLoc {} = error "srcLocPos: unhelpful loc"

respond :: Ref MoteState -> FromClient -> Ghc ToClient
respond stRef msg = either (Error . show) id <$> runErrorT (respond' stRef msg)

respond' :: Ref MoteState -> FromClient -> M ToClient
respond' stRef = \case
  Load p -> do
    loadFile stRef p
    liftIO . forkIO $ do
      fmap fileData (gReadRef stRef) >>= \case
        Nothing -> return ()
        Just (FileData {holesInfo=_}) ->
          return ()
          -- no idea if this is kosher
          -- void . runGhc (Just libdir) $ runErrorT (mapM_ (getAndMemoizeSuggestions stRef) (M.elems holesInfo))
    return Ok

  NextHole (ClientState {path, cursorPos=(line,col)}) ->
    getHoles stRef >>= \holes ->
      let mh =
            case dropWhile ((currPosLoc >=) . srcSpanStart) holes of
              [] -> case holes of {[] -> Nothing; (h:_) -> Just h }
              (h:_) -> Just h
      in
      maybe (throwError NoHole) (return . SetCursor . srcLocPos . srcSpanStart) mh
    where
    currPosLoc = mkSrcLoc (fsLit path) line col

  -- inefficient
  PrevHole (ClientState {path, cursorPos=(line, col)}) ->
    getHoles stRef >>= \holes ->
      let mxs = case takeWhile (< currPosSpan) holes of
                  [] -> case holes of {[] -> Nothing; _ -> Just holes}
                  xs -> Just xs
      in
      maybe (throwError NoHole) (return . SetCursor . srcLocPos . srcSpanStart . last) mxs
    where
    currPosSpan = srcLocSpan (mkSrcLoc (fsLit path) line col)

  EnterHole (ClientState {..}) -> do
    FileData {path=p} <- getFileDataErr stRef
    when (p /= path) (loadFile stRef path)

    mh <- getEnclosingHole stRef cursorPos
    gModifyRef stRef (\st -> st { currentHole = mh })
    return $ case mh of
      Nothing -> SetInfoWindow "No Hole found"
      Just _  -> Ok

  GetHoleInfo (ClientState {..}) (HoleInfoOptions{..}) -> do
    ahi@(AugmentedHoleInfo {holeInfo=hi}) <- getCurrentHoleErr stRef
    fs <- lift getSessionDynFlags
    let env = map (\(id,t) -> (occNameToString (getOccName id), showType fs t)) (holeEnv hi)
    case sendOutputAsData of
      True -> do
        suggsJSON <-
          if withSuggestions
          then mkSuggsJSON <$> Mote.Suggest.getAndMemoizeSuggestions stRef ahi
          else return []
        return $
          JSON . Aeson.object $
            [ "environment" .= map (\(x, t) -> Aeson.object ["name" .= x, "type" .= t]) env
            , "goal" .= Aeson.object ["name" .= holeNameString hi, "type" .= showType fs (holeType hi) ]
            ]
            ++ suggsJSON
        where
        mkSuggJSON (n, t) = Aeson.object ["name" .= occNameToString (occName n), "type" .= showType fs t]
        mkSuggsJSON suggs = [ "suggestions" .= map mkSuggJSON suggs ]

      False -> do
        suggsStr <-
          if withSuggestions
          then mkSuggsStr <$> Mote.Suggest.getAndMemoizeSuggestions stRef ahi
          else return ""

        let goalStr = "Goal: " ++ holeNameString hi ++ " :: " ++ showType fs (holeType hi)
                    ++ "\n" ++ replicate 40 '-'
            envStr =
              -- TODO: Wow, this is total for the strangest reason. If env
              -- is empty then maxIdentLength never gets used to pad so
              -- maximum doesn't fail.
              let maxIdentLength = maximum $ map (\(x,_) -> length x) env in
              unlines $ map (\(x, t) ->
                take maxIdentLength (x ++ repeat ' ') ++ " :: " ++ t) env
        return . SetInfoWindow $ unlines [goalStr, envStr, "", suggsStr]
        where
        mkSuggsStr suggs = 
          let heading = "Suggestions:\n" ++ replicate 40 '-' in
          unlines (heading : map (\(n, t) -> (occNameToString . occName) n ++ " :: " ++ showType fs t) suggs)

  Refine exprStr (ClientState {..}) -> do
    hi    <- getCurrentHoleErr stRef
    expr' <- refine stRef exprStr
    fs    <- lift getSessionDynFlags
    unqual <- lift getPrintUnqual
    return $
      Replace (toSpan . holeSpan $ holeInfo hi) path
        (showSDocForUser fs unqual (ppr expr'))


  SendStop -> return Stop 

  -- Precondition here: Hole has already been entered
  CaseFurther var ClientState {} -> do
    logS stRef "casefurther:0"
    MoteState {..} <- gReadRef stRef
    FileData {path, hsModule} <- getFileDataErr stRef
    hi@(HoleInfo {holeEnv})   <- holeInfo <$> getCurrentHoleErr stRef

    logS stRef "casefurther:1"
    (id, ty) <- maybeThrow (NoVariable var) $
      List.find (\(id,_) -> var == occNameToString (getOccName id)) holeEnv

    expansions stRef (occNameToString (getOccName id)) ty (holeSpan hi) hsModule >>= \case
      Nothing                        -> return (Error "Variable not found")
      Just ((L sp _mg, mi), matches) -> do
        logS stRef "casefurther:2"
        fs <- lift getSessionDynFlags
        unqual <- lift getPrintUnqual
        let span              = toSpan sp
            indentLevel       = subtract 1 . snd . fst $ span
            indentTail []     = error "indentTail got []"
            indentTail (s:ss) = s : map (replicate indentLevel ' ' ++) ss

            showMatch :: HsMatchContext RdrName -> Match RdrName (LHsExpr RdrName) -> String
            showMatch ctx = showSDocForUser fs unqual . pprMatch ctx
        return $ case mi of
          Equation (L _l name) ->
            Replace (toSpan sp) path . unlines . indentTail $
              map (showMatch (FunRhs name False)) matches

          CaseBranch ->
            -- TODO shouldn't always unlines. sometimes should be ; and {}
            Replace (toSpan sp) path . unlines . indentTail $
              map (showMatch CaseAlt) matches

          SingleLambda _loc ->
            Error "SingleLambda case expansion not yet implemented"

  CaseOn exprStr (ClientState {..}) -> do
    expr <- parseExpr exprStr
    -- Should actually have general mechanism for getting the scope at
    -- a point...
    FileData {..} <- getFileDataErr stRef
    ty <- getEnclosingHole stRef cursorPos >>= \case
      Nothing -> hsExprType expr
      Just hi -> inHoleEnv typecheckedModule (holeInfo hi) $ tcRnExprTc expr
    let (line, col) = cursorPos
    ms <- matchesForTypeAt stRef ty (mkSrcLoc (fsLit "") line col)

    indentLevel <- liftIO $
      LB8.length . LB8.takeWhile (== ' ') . (!! (line - 1)) . LB8.lines <$> LB8.readFile path

    fs <- lift getSessionDynFlags
    unqual <- lift getPrintUnqual
    let indent n  = (replicate n ' ' ++)
        showMatch = showSDocForUser fs unqual . pprMatch (CaseAlt :: HsMatchContext RdrName)
    return
      . Insert cursorPos path
      . unlines
      $ ("case " ++ exprStr ++ " of") : map (indent (2 + fromIntegral indentLevel) . showMatch) ms

  -- every message should really send current file name (ClientState) and
  -- check if it matches the currently loaded file
  GetType e -> do
    fs <- lift getSessionDynFlags
    x  <- exprType e
    unqual <- lift getPrintUnqual
    return . SetInfoWindow . showSDocForUser fs unqual $ ppr x

  Search src trg -> do
    gs <- Mote.Search.search src trg 5
    return (SetInfoWindow (showResults gs)) 
    where
    -- TODO:uncomment showResults :: [Search.Graph.Types.NaturalGraph f o] -> String
    showResults =
      unlines
      . map (\(_,(t,_)) -> Search.Graph.renderAnnotatedTerm t)
      . take 5
      . List.sortBy (compare `on` fst)
      . map (\g ->
        let pr = (Search.Graph.toTerm g, g) in (Mote.Search.score pr, pr))

showM :: (GhcMonad m, Outputable a) => a -> m String
showM = showSDocM . ppr

main :: IO ()
main = do
  home <- getHomeDirectory
  withFile (home </> ".moteserverlog") WriteMode $ \logFile -> do
    stRef <- newRef =<< initialState logFile
    hSetBuffering logFile NoBuffering
    hSetBuffering stdout NoBuffering
    hPutStrLn logFile "Testing, testing"
    runGhc (Just libdir) $ do
      -- ghcInit stRef
      Mote.Init.initializeWithCabal stRef >>= \case
        Left err -> liftIO $ do
          LB8.putStrLn (encode (Error err))
          exitWith (ExitFailure 1)
        Right () -> return ()

      logS stRef "init'd"
      forever $ do
        ln <- liftIO B.getLine
        case decodeStrict ln of
          Nothing  ->
            liftIO . LB8.putStrLn . encode $ Error "Could not parse message JSON"
          Just msg -> do
            liftIO $ hPutStrLn logFile ("Got: " ++ show msg)
            resp <- respond stRef msg
            liftIO $ hPutStrLn logFile ("Giving: " ++ show resp)
            liftIO $ LB8.putStrLn (encode resp)

initialState :: Handle -> IO MoteState
initialState logFile = mkSplitUniqSupply 'x' >>| \uniq -> MoteState
  { fileData = Nothing
  , currentHole = Nothing
  , argHoles = S.empty
  , loadErrors = []
  , logFile
  , uniq
  }

runWithTestRef :: (Ref MoteState -> Ghc b) -> IO b
runWithTestRef x = do
  home <- getHomeDirectory
  withFile (home </> "testlog") WriteMode $ \logFile -> do
    r <- newRef =<< initialState logFile
    run $ do { ghcInit r; x r }
  where
  ghcInit _ = do
    dfs <- getSessionDynFlags
    void . setSessionDynFlags . withFlags [DynFlags.Opt_DeferTypeErrors] $ dfs
      { hscTarget  = HscInterpreted
      , ghcLink    = LinkInMemory
      , ghcMode    = CompManager
      , traceLevel = 10
      }
    where
    withFlags fs dynFs = foldl DynFlags.gopt_set dynFs fs

runWithTestRef' x = do
  home <- getHomeDirectory
  withFile (home </> "testlog") WriteMode $ \logFile -> do
    r <- newRef =<< initialState logFile
    run $ do { Mote.Init.initializeWithCabal r; x r }

runWithTestRef'' :: a -> IO ()
runWithTestRef'' x = do
  print 0

run :: Ghc a -> IO a
run = runGhc (Just libdir)

