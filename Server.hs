{-# LANGUAGE LambdaCase,
             NamedFieldPuns,
             RecordWildCards #-}
module Main where

import Control.Monad
import Protocol
import GhcMonad
import GHC
import Data.List (find)
import qualified Holes.

type Hole = SrcSpan

data SlickState = SlickState
  { holes       :: [Hole]
  , fileData    :: Maybe (FilePath, HsModule RdrName)
  , currentHole :: Maybe Hole
  }

readModule p = fmap (unLoc . parsedSource) $
  parseModule =<< (getModSummary . mkModuleName $ takeBaseName p)

type M = Ghc

ghcInit = do
  dfs <- getSessionDynFlags
  setSessionDynFlags . withFlags [DynFlags.Opt_DeferTypeErrors] $ dfs
    { hscTarget  = HscInterpreted
    , ghcLink    = LinkInMemory
    , ghcMode    = CompManager
    , log_action = \_ _ _ _ _ -> return ()
    }
  where
  withFlags fs dynFs = foldl DynFlags.gopt_set dynFs fs

findEnclosingHole :: (Int, Int) -> [Hole] -> Maybe Hole
findEnclosingHole pos = find (`spans` pos)

loadModule p = do
  -- TODO: Clear old names and stuff
  setTargets . (:[]) =<< guessTarget p Nothing
  load LoadAllTargets
  setContext [IIModule $ mkModuleName (takeBaseName p)]
  readModule p

loadFile :: GhcMonad m => IORef SlickState -> FilePath -> m ()
loadFile stRef p = loadModule p >>= setStateForData stRef p

setStateForData :: GhcMonad m => IORef SlickState -> FilePath -> HsModule RdrName -> m ()
setStateForData stRef p mod = gModifyIORef stRef (\st -> st 
  { fileData    = Just (p, mod)
  , holes       = Holes.holes mod
  , currentHole = Nothing
  })

gReadIORef = lift . readIORef
gModifyIORef = lift . modifyIORef

loadModuleAndSetupState :: GhcMonad m => IORef SlickState -> FilePath -> m (HsModule RdrName)
loadModuleAndSetupState stRef p = do
  mod <- loadModule p
  mod <$ setStateForData stRef p mod

respond :: IORef SlickState -> FromClient -> M ToClient
respond stRef = \case
  Load p ->
    loadFile p
    return Ok

  EnterHole (ClientState {..}) -> do
    mod <- gReadIORef stRef >>= \st -> case fileData st of
      Nothing       -> loadModuleAndSetupState stRef path
      Just (p, mod) ->
        if p == path
        then return mod
        else loadModuleAndSetupState stRef path -- maybe shouldn't autoload

    SlickState {holes} <- gReadIORef stRef

    mh <- findEnclosingHole holes cursorPos
    gModifyIORef stRef (\st -> st { currentHole = mh })
    case mf of
      Nothing -> return (Error "No Hole found")
      Just h  -> Ok <$ Holes.setupContext h

  GetEnv (ClientState {..}) -> do
    fmap currentHole gReadIORef >>= \case
      Just h -> undefined

-- map from PID to State


test = do
  ghcInit
  loadFile "Foo.hs"
  runStmt "let g = f" RunToCompletion
  showSDocM . ppr =<< exprType "g"

