{-# LANGUAGE LambdaCase, RecordWildCards #-}
module Init where

import qualified ParseHoleMessage
import Outputable
import Data.List (intercalate)
import Types
import Util
import GHC
import Data.IORef
import Language.Haskell.GhcMod.Internal hiding (getCompilerOptions)
-- I had to write my own "getCompilerOptions" and "parseCabalFile"
-- since the ghcmod versions die on new binary format cabal files.
import Language.Haskell.GhcMod
import DynFlags
import Control.Applicative
import Control.Monad
import qualified Data.Map as M
import qualified Data.Set as S
import GhcMonad
import Control.Monad.Error
import qualified Control.Exception

import qualified Distribution.PackageDescription as P
import Distribution.Simple.Compiler (CompilerId(..), CompilerFlavor(..))
import qualified Distribution.Package as C
import Distribution.Simple.Program as C (ghcProgram)
import Distribution.PackageDescription.Configuration (finalizePackageDescription)
import Distribution.PackageDescription.Parse (readPackageDescription)
import Distribution.Verbosity as Verbosity
import Distribution.System (buildPlatform)
import Distribution.Simple.LocalBuildInfo (configFlags)
import Data.Version(Version)
import Distribution.Simple.Program.Types (programName, programFindVersion)

-- Imports for setupConfigFile
import Distribution.Simple.BuildPaths (defaultDistPref)
import Distribution.Simple.Configure (localBuildInfoFile)
import Distribution.Text (display)

import System.Directory
import System.FilePath ((</>))
import System.Process
import System.Exit
import Exception
{- The following code is adapted from ghc-mod -}
{- Copyright (c) 2009, IIJ Innovation Institute Inc.
All rights reserved.
Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions
are met:
* Redistributions of source code must retain the above copyright
notice, this list of conditions and the following disclaimer.
* Redistributions in binary form must reproduce the above copyright
notice, this list of conditions and the following disclaimer in
the documentation and/or other materials provided with the
distribution.
* Neither the name of the copyright holders nor the names of its
contributors may be used to endorse or promote products derived
from this software without specific prior written permission.
THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
POSSIBILITY OF SUCH DAMAGE. -}

-- init :: IORef SlickState -> m ()
init stRef = initializeWithCabal stRef defaultOptions

initializeWithCabal stRef opt = do
  c <- liftIO findCradle
  logS stRef "Found cradle"
  case cradleCabalFile c of
    Nothing ->
      let wdir       = cradleCurrentDir c
          rdir       = cradleRootDir c
          pkgOpts    = ghcDbStackOpts $ cradlePkgDbStack c
          importDirs = [".","..","../..","../../..","../../../..","../../../../.."]
          compOpts   =
            CompilerOptions (ghcOpts ++ pkgOpts)
              (if null pkgOpts then importDirs else [wdir, rdir]) []
      in
      setOptions stRef opt compOpts

    Just cab -> do
      logS stRef "Cabal file was found"
      (compOptsErr, _) <- liftIO . runGhcModT opt $
        getCompilerOptions ghcOpts c =<< parseCabalFile c cab
      case compOptsErr of
        Left err -> logS stRef $ "initializeWithCabal error: " ++ show err
        Right compOpts -> setOptions stRef opt compOpts

  where
  ghcOpts = ghcUserOptions opt

ghcDbStackOpts = concatMap ghcDbOpt
-- This should be called once per run.
-- what to do about different files...
setOptions stRef (Options {..}) (CompilerOptions{..}) = do
  df <- getSessionDynFlags
  let df' = df
        { hscTarget  = HscInterpreted
        , ghcLink    = LinkInMemory
        , ghcMode    = CompManager
        , log_action = \fs sev span sty msg -> do
            -- Here be hacks
            let s = showSDoc fs (withPprStyle sty msg)
            logS stRef s
            case ParseHoleMessage.parseHoleInfo s of
              Nothing   -> return ()
              Just info -> modifyIORef stRef (\s ->
                s { holesInfo = M.insert span info (holesInfo s) })
        }

  void $ setSessionDynFlags =<< addCmdOpts ghcOptions
    ( setFlags
    . setIncludeDirs includeDirs
    $ addPackageFlags depPackages df')
  where
  addCmdOpts cmdOpts df =
    (\(a,_,_) -> a) <$> parseDynamicFlags df (map noLoc cmdOpts)

  -- TODO: setBuildEnv (GhcMod.DynFlags.hs) doesn't do much but it does
  -- add warnings about hidden packages. Consider using it.
  setIncludeDirs idirs df = df { importPaths = idirs }

  setFlags df = (df `gopt_unset` Opt_SpecConstr) `gopt_set` Opt_DeferTypeErrors

  addPackageFlags pkgs df =
    df { packageFlags = packageFlags df ++ expose `map` pkgs }
    where
    expose pkg = ExposePackageId $ showPkgId pkg
    showPkgId (n,v,i) = intercalate "-" [n,v,i]

ghcDbOpt :: GhcPkgDb -> [String]
ghcDbOpt db
  | s == "GlobalDb"                    = ["-global-package-db"]
  | s == "UserDb"                      = ["-user-package-db"]
  | ("PackageDb ",s') <-  splitAt 10 s = ["-no-user-package-db", "-package-db", read s']
  where s = show db

-- begin implementation of parseCabalFile
-- The offending function
getConfig cradle = do
  outOfDate <- liftIO $ isSetupConfigOutOfDate cradle
  when outOfDate configure
  liftIO (readFile file) `catchError` \_ ->
    -- TODO: A lovely hack can be seen here
    readProcess "cabalparse" [file] ""
  where
  file   = setupConfigFile cradle
  prjDir = cradleRootDir cradle

  configure :: (IOish m, MonadError GhcModError m) => m ()
  configure = withDirectory_ prjDir $ void $ readProcess' "cabal" ["configure"]

  withDirectory_ :: (MonadIO m, ExceptionMonad m) => FilePath -> m a -> m a
  withDirectory_ dir action =
      gbracket (liftIO getCurrentDirectory) (liftIO . setCurrentDirectory)
                  (\_ -> liftIO (setCurrentDirectory dir) >> action)

  readProcess' :: (MonadIO m, MonadError GhcModError m)
              => String
              -> [String]
              -> m String
  readProcess' cmd opts = do
    (rv,output,err) <- liftIO (readProcessWithExitCode cmd opts "")
        `modifyError'` GMEProcess ([cmd] ++ opts)
    case rv of
      ExitFailure val -> do
          throwError $ GMEProcess ([cmd] ++ opts) $ strMsg $
            cmd ++ " " ++ unwords opts ++ " (exit " ++ show val ++ ")"
                ++ "\n" ++ err
      ExitSuccess ->
          return output

  modifyError :: MonadError e m => (e -> e) -> m a -> m a
  modifyError f action = action `catchError` \e -> throwError $ f e

  infixr 0 `modifyError'`
  modifyError' :: MonadError e m => m a -> (e -> e) -> m a
  modifyError' = flip modifyError

-- adapted from Language.Haskell.GhcMod.World
isSetupConfigOutOfDate :: Cradle -> IO Bool
isSetupConfigOutOfDate crdl =
  case cradleCabalFile crdl of
    Nothing  -> return False
    Just cab -> doesFileExist cab >>= \case
      False -> return False
      True  -> doesFileExist (setupConfigFile crdl) >>= \case
        False -> True
        True  ->
          (<) <$> getModificationTime (setupConfigFile cab)
              <*> getModificationTime cab

-- begin implementation of getCompilerOptions
getCompilerOptions ghcopts cradle pkgDesc = do
  gopts <- liftIO $ getGHCOptions ghcopts cradle rdir $ head buildInfos
  depPkgs <- cabalConfigDependencies cradle (C.packageId pkgDesc)
  return $ CompilerOptions gopts idirs depPkgs
  where
  wdir       = cradleCurrentDir cradle
  rdir       = cradleRootDir    cradle
  buildInfos = cabalAllBuildInfo pkgDesc
  idirs      = includeDirectories rdir wdir $ cabalSourceDirs buildInfos
    where
    includeDirectories :: FilePath -> FilePath -> [FilePath] -> [FilePath]
    includeDirectories cdir wdir dirs = uniqueAndSort (extdirs ++ [cdir,wdir])
      where
        extdirs = map expand $ dirs ++ cabalBuildDirs
        expand "."    = cdir
        expand subdir = cdir </> subdir
        uniqueAndSort = S.toList . S.fromList
        cabalBuildDirs = ["dist/build", "dist/build/autogen"]


getGHCOptions :: [GHCOption] -> Cradle -> FilePath -> P.BuildInfo -> IO [GHCOption]
getGHCOptions ghcopts cradle rdir binfo = do
  cabalCpp <- cabalCppOptions rdir
  let cpps = map ("-optP" ++) $ P.cppOptions binfo ++ cabalCpp
  return $ ghcopts ++ pkgDb ++ exts ++ [lang] ++ libs ++ libDirs ++ cpps
  where
  pkgDb = ghcDbStackOpts $ cradlePkgDbStack cradle
  lang = maybe "-XHaskell98" (("-X" ++) . display) $ P.defaultLanguage binfo
  libDirs = map ("-L" ++) $ P.extraLibDirs binfo
  exts = map (("-X" ++) . display) $ P.usedExtensions binfo
  libs = map ("-l" ++) $ P.extraLibs binfo

  cabalCppOptions :: FilePath -> IO [String]
  cabalCppOptions dir = do
      exist <- doesFileExist cabalMacro
      return $ if exist then
          ["-include", cabalMacro]
        else
          []
    where
      cabalMacro = dir </> "dist/build/autogen/cabal_macros.h"

cabalConfigDependencies cradle thisPkg =
  configDependencies thisPkg <$> getConfig cradle

setupConfigFile :: Cradle -> FilePath
setupConfigFile crdl = cradleRootDir crdl </> setupConfigPath

setupConfigPath :: FilePath
setupConfigPath = localBuildInfoFile defaultDistPref

-- end implementation of getCompilerOptions

configDependencies :: PackageIdentifier -> CabalConfig -> [Package]
configDependencies thisPkg config = map fromInstalledPackageId deps
 where
    deps :: [InstalledPackageId]
    deps = case deps21 `mplus` deps18 `mplus` deps16 of
        Right ps -> ps
        Left msg -> error msg

    -- True if this dependency is an internal one (depends on the library
    -- defined in the same package).
    internal pkgid = pkgid == thisPkg

    -- Cabal >= 1.21
    deps21 :: Either String [InstalledPackageId]
    deps21 =
        map fst
      <$> filterInternal21
      <$> (readEither =<< extractField config "componentsConfigs")

    filterInternal21
        :: [(ComponentName, C21.ComponentLocalBuildInfo, [ComponentName])]
        -> [(InstalledPackageId, C21.PackageIdentifier)]

    filterInternal21 ccfg = [ (ipkgid, pkgid)
                          | (_,clbi,_)      <- ccfg
                          , (ipkgid, pkgid) <- C21.componentPackageDeps clbi
                          , not (internal . packageIdentifierFrom21 $ pkgid) ]

    packageIdentifierFrom21 :: C21.PackageIdentifier -> PackageIdentifier
    packageIdentifierFrom21 (C21.PackageIdentifier (C21.PackageName myName) myVersion) =
        PackageIdentifier (PackageName myName) myVersion

    -- Cabal >= 1.18 && < 1.21
    deps18 :: Either String [InstalledPackageId]
    deps18 =
          map fst
      <$> filterInternal
      <$> (readEither =<< extractField config "componentsConfigs")

    filterInternal
        :: [(ComponentName, C18.ComponentLocalBuildInfo, [ComponentName])]
        -> [(InstalledPackageId, PackageIdentifier)]

    filterInternal ccfg = [ (ipkgid, pkgid)
                          | (_,clbi,_)      <- ccfg
                          , (ipkgid, pkgid) <- C18.componentPackageDeps clbi
                          , not (internal pkgid) ]

    -- Cabal 1.16 and below
    deps16 :: Either String [InstalledPackageId]
    deps16 = map fst <$> filter (not . internal . snd) . nub <$> do
        cbi <- concat <$> sequence [ extract "executableConfigs"
                                   , extract "testSuiteConfigs"
                                   , extract "benchmarkConfigs" ]
                        :: Either String [(String, C16.ComponentLocalBuildInfo)]

        return $ maybe [] C16.componentPackageDeps libraryConfig
              ++ concatMap (C16.componentPackageDeps . snd) cbi
     where
       libraryConfig :: Maybe C16.ComponentLocalBuildInfo
       libraryConfig = do
         field <- find ("libraryConfig" `isPrefixOf`) (tails config)
         clbi <- stripPrefix " = " field
         if "Nothing" `isPrefixOf` clbi
             then Nothing
             else case readMaybe =<< stripPrefix "Just " clbi of
                    Just x -> x
                    Nothing -> error $ "reading libraryConfig failed\n" ++ show (stripPrefix "Just " clbi)

       extract :: String -> Either String [(String, C16.ComponentLocalBuildInfo)]
       extract field = readConfigs field <$> extractField config field

       readConfigs :: String -> String -> [(String, C16.ComponentLocalBuildInfo)]
       readConfigs f s = case readEither s of
           Right x -> x
           Left msg -> error $ "reading config " ++ f ++ " failed ("++msg++")"

