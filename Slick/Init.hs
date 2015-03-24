{-# LANGUAGE ConstraintKinds, FlexibleContexts, LambdaCase, RecordWildCards,
             ScopedTypeVariables #-}
module Slick.Init where

import           Data.IORef
import           Data.List                                     (intercalate)
import           GHC
import           Language.Haskell.GhcMod.Internal              hiding (getCompilerOptions,
                                                                parseCabalFile)
import           Outputable
import           Slick.Protocol (ToClient(Error))
import           Slick.Types
import           Slick.Util
-- I had to write my own "getCompilerOptions" and "parseCabalFile"
-- since the ghcmod versions die on new binary format cabal files.
import           Control.Applicative
import qualified Control.Exception
import           Control.Monad
import           Control.Monad.Error
import           Data.Aeson                                    (encode)
import qualified Data.ByteString.Lazy.Char8 as LB8
import qualified Data.Map                                      as M
import qualified Data.Set                                      as S
import           DynFlags
import           GhcMonad
import           Language.Haskell.GhcMod
import ErrUtils

import qualified Distribution.Package                          as C
import qualified Distribution.PackageDescription               as P
import           Distribution.PackageDescription.Configuration (finalizePackageDescription)
import           Distribution.PackageDescription.Parse         (readPackageDescription)
import           Distribution.Simple.Compiler                  (CompilerFlavor (..),
                                                                CompilerId (..))
import           Distribution.Simple.Program                   as C (ghcProgram)
import           Distribution.System                           (buildPlatform)
import           Distribution.Verbosity                        as Verbosity
-- import Distribution.Simple.LocalBuildInfo (configFlags)
import           Data.Version                                  (Version)
import           Distribution.PackageDescription               (FlagAssignment)
import           Distribution.Simple.Program.Types             (programFindVersion,
                                                                programName)

import qualified System.IO.Strict

-- Imports for setupConfigFile
import           Distribution.Simple.BuildPaths                (defaultDistPref)
import           Distribution.Simple.Configure                 (localBuildInfoFile)
import           Distribution.Text                             (display)

import           Exception
import           System.Directory
import           System.Exit
import           System.FilePath                               ((</>))
import           System.Process

-- Imports for cabalConfigDependencies
import qualified CabalVersions.Cabal16                         as C16
import qualified CabalVersions.Cabal18                         as C18
import qualified CabalVersions.Cabal21                         as C21
import qualified CabalVersions.Cabal22                         as C22
import           Data.List                                     (find, isInfixOf,
                                                                isPrefixOf, nub,
                                                                splitAt,
                                                                stripPrefix,
                                                                tails)
import           Data.List.Split                               (splitOn)
import           Distribution.Package                          (InstalledPackageId (..), PackageIdentifier (..), PackageName (..))
import           Distribution.Simple.LocalBuildInfo            (ComponentName)
import           Text.Read                                     (readEither,
                                                                readMaybe)

-- TODO: I really should have just copied to ghcmod source to this
-- directory and used it directly. God willing I will never have
-- to touch this module again.

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

init :: GhcMonad m => IORef SlickState -> m (Either String ())
init stRef = initializeWithCabal stRef defaultOptions

runGhcModT'' opt mx = do
  env <- newGhcModEnv opt =<< getCurrentDirectory
  (orErr, _log) <- runGhcModT' env defaultState mx
  return $ fmap fst orErr

initializeWithCabal :: GhcMonad m => IORef SlickState -> Options -> m (Either String ())
initializeWithCabal stRef opt = do
  c <- liftIO findCradle
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
      setOptions stRef opt compOpts >> return (Right ())

    Just cab -> do
      compOptsErr <- liftIO . runGhcModT'' opt $ do
        getCompilerOptions ghcOpts c =<< parseCabalFile c cab

      case compOptsErr of
        Left err       -> return . Left $ "initializeWithCabal error: " ++ show err
        Right compOpts -> setOptions stRef opt compOpts >> return (Right ())

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
        , log_action = \dfs sev span pprsty msgdoc ->
            let msg =
                  showSDocForUser dfs neverQualify
                  $ mkLocMessage sev span msgdoc
                isHoleMsg = and . zipWith (==) "Found hole" $ showSDoc dfs msgdoc
                isError = case sev of { SevError -> True; SevFatal -> True; _ -> False }
            in
            if isHoleMsg || not isError
            then return ()
            else
              gModifyIORef stRef (\s ->
                s { loadErrors = msg : loadErrors s })
        {- TODO: Debug
        , traceLevel = 2
        , log_action = \dfs sev span pprsty msgdoc ->
            logS stRef $ showSDoc dfs msgdoc
        -}
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
parseCabalFile :: (IOish m, MonadError GhcModError m)
               => Cradle
               -> FilePath
               -> m P.PackageDescription
parseCabalFile cradle file = do
    cid <- liftIO getGHCId
    epgd <- liftIO $ readPackageDescription silent file
    flags <- cabalConfigFlags cradle
    case toPkgDesc cid flags epgd of
        Left deps    -> fail $ show deps ++ " are not installed"
        Right (pd,_) -> if nullPkg pd
                        then fail $ file ++ " is broken"
                        else return pd
  where
    toPkgDesc cid flags =
        finalizePackageDescription flags (const True) buildPlatform cid []
    nullPkg pd = name == ""
      where
        PackageName name = C.pkgName (P.package pd)

getGHCId :: IO CompilerId
getGHCId = CompilerId GHC <$> getGHC

getGHC :: IO Version
getGHC = do
    mv <- programFindVersion C.ghcProgram silent (programName C.ghcProgram)
    case mv of
      -- TODO: MonadError it up
        Nothing -> throwIO $ userError "ghc not found"
        Just v  -> return v

cabalConfigFlags :: (IOish m, MonadError GhcModError m)
                 => Cradle
                 -> m FlagAssignment
cabalConfigFlags cradle = do
  config <- getConfig cradle
  case configFlags config of
    Right x  -> return x
    Left msg -> throwError (GMECabalFlags (GMEString msg))

configFlags :: CabalConfig -> Either String FlagAssignment
configFlags config = readEither =<< flip extractField "configConfigurationsFlags" =<< extractField config "configFlags"

-- The offending function
getConfig :: (IOish m, MonadError GhcModError m)
          => Cradle
          -> m CabalConfig
getConfig cradle = do
  outOfDate <- liftIO $ isSetupConfigOutOfDate cradle
  when outOfDate configure
  liftIO (System.IO.Strict.readFile file `catch` \(_ :: SomeException) ->
    readProcessWithExitCode "cabalparse" [file] "" >>= \case
      (ExitSuccess, stdout, _)   -> return stdout
      (ExitFailure _, _, stderr) -> throwIO (ErrorCall stderr))
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
        False -> return True
        True  ->
          (<) <$> getModificationTime (setupConfigFile crdl)
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

type CabalConfig = String
configDependencies :: PackageIdentifier -> CabalConfig -> [Package]
configDependencies thisPkg config = map fromInstalledPackageId deps
 where
    deps :: [InstalledPackageId]
    deps = case deps22 `mplus` deps21 `mplus` deps18 `mplus` deps16 of
        Right ps -> ps
        Left msg -> error msg

    -- True if this dependency is an internal one (depends on the library
    -- defined in the same package).
    internal pkgid = pkgid == thisPkg

    deps22 :: Either String [InstalledPackageId]
    deps22 = do
      (xs :: [(ComponentName, C22.ComponentLocalBuildInfo, [ComponentName])]) <- 
        readEither =<< extractField config "componentsConfigs"
      return (map fst $ filterInternal22 xs)

    filterInternal22 ccfg =
      [ (ipkgid, pkgid)
      | (_,clbi,_)      <- ccfg
      , (ipkgid, pkgid) <- C22.componentPackageDeps clbi
      , not (internal . packageIdentifierFrom22 $ pkgid)
      ]
      

    packageIdentifierFrom22 (C22.PackageIdentifier (C22.PackageName myName) myVersion) =
        PackageIdentifier (PackageName myName) myVersion

    -- Cabal >= 1.21 && < 1.22
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

fromInstalledPackageId' :: InstalledPackageId -> Maybe Package
fromInstalledPackageId' pid = let
    InstalledPackageId pkg = pid
    in case reverse $ splitOn "-" pkg of
      i:v:rest -> Just (intercalate "-" (reverse rest), v, i)
      _ -> Nothing

fromInstalledPackageId :: InstalledPackageId -> Package
fromInstalledPackageId pid =
    case fromInstalledPackageId' pid of
      Just p -> p
      Nothing -> error $
        "fromInstalledPackageId: `"++show pid++"' is not a valid package-id"

extractField :: CabalConfig -> String -> Either String String
extractField config field =
    case extractParens <$> find (field `isPrefixOf`) (tails config) of
        Just f -> Right f
        Nothing -> Left $ "extractField: failed extracting "++field++" from input, input contained `"++field++"'? " ++ show (field `isInfixOf` config)

extractParens :: String -> String
extractParens str = extractParens' str 0
 where
   extractParens' :: String -> Int -> String
   extractParens' [] _ = []
   extractParens' (s:ss) level
       | s `elem` "([{" = s : extractParens' ss (level+1)
       | level == 0 = extractParens' ss 0
       | s `elem` "}])" && level == 1 = [s]
       | s `elem` "}])" = s : extractParens' ss (level-1)
       | otherwise = s : extractParens' ss level

