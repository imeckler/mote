module Mote.Cradle where

import Config (cProjectVersion)
import Distribution.Helper (buildPlatform)

import System.Directory (getCurrentDirectory, setCurrentDirectory, doesFileExist,
                         getTemporaryDirectory, canonicalizePath, removeDirectoryRecursive,
                         getDirectoryContents)
import System.FilePath (splitDrive, takeDirectory, takeFileName, pathSeparators,
                        takeExtension, normalise, dropTrailingPathSeparator, joinDrive,
                        splitDirectories, isAbsolute, joinPath, (</>))
import System.IO.Temp (createTempDirectory)

import System.IO.Unsafe (unsafePerformIO)

import Data.Char (isAlphaNum)
import Data.List (find)
import Data.Maybe (fromJust)
import Data.Traversable (traverse)

import Control.Applicative ((<$>))
import Control.Monad.IO.Class (liftIO, MonadIO)
import Control.Monad
import Control.Monad.Trans.Maybe

{- The following code is based on Language.Haskell.GhcMod.Cradle
so I included the copyright notice -}

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

data GhcPkgDb
  = GlobalDb
  | UserDb
  | PackageDb String
  deriving (Eq, Show)

data Cradle =
  Cradle
  { currentDir :: FilePath
  , rootDir    :: FilePath
  , tempDir    :: FilePath
  , cabalFile  :: Maybe FilePath
  , pkgDbStack :: [GhcPkgDb]
  }
  deriving (Eq, Show)

findCradle :: IO Cradle
findCradle = findCradleFrom =<< getCurrentDirectory

findCradleFrom :: FilePath -> IO Cradle
findCradleFrom dir = run $ do
    (customCradle dir `mplus` cabalCradle dir `mplus`  sandboxCradle dir `mplus` plainCradle dir)
 where run a = fillTempDir =<< (fromJust <$> runMaybeT a)

customCradle :: FilePath -> MaybeT IO Cradle
customCradle wdir = do
    cabalFile <- MaybeT $ findCabalFile wdir
    let cabalDir = takeDirectory cabalFile
    cradleFile <- MaybeT $ findCradleFile cabalDir
    pkgDbStack <- liftIO $ parseCradle cradleFile
    return Cradle {
        currentDir = wdir
      , rootDir    = cabalDir
      , tempDir    = error "tmpDir"
      , cabalFile  = Just cabalFile
      , pkgDbStack = pkgDbStack
      }

  where
  parseCradle :: FilePath -> IO [GhcPkgDb]
  parseCradle path = do
      source <- readFile path
      return $ parseCradle' source
    where
      parseCradle' source = map parsePkgDb $ filter (not . null) $ lines source

      parsePkgDb "global" = GlobalDb
      parsePkgDb "user" = UserDb
      parsePkgDb s = PackageDb s

cabalCradle :: FilePath -> MaybeT IO Cradle
cabalCradle wdir = do
    cabalFile <- MaybeT $ findCabalFile wdir

    let cabalDir = takeDirectory cabalFile
    pkgDbStack <- liftIO $ getPackageDbStack cabalDir

    return Cradle {
        currentDir = wdir
      , rootDir    = cabalDir
      , tempDir    = error "tmpDir"
      , cabalFile  = Just cabalFile
      , pkgDbStack = pkgDbStack
      }

sandboxCradle :: FilePath -> MaybeT IO Cradle
sandboxCradle wdir = do
    sbDir <- MaybeT $ findCabalSandboxDir wdir
    pkgDbStack <- liftIO $ getPackageDbStack sbDir
    return Cradle {
        currentDir = wdir
      , rootDir    = sbDir
      , tempDir    = error "tmpDir"
      , cabalFile  = Nothing
      , pkgDbStack = pkgDbStack
      }

plainCradle :: FilePath -> MaybeT IO Cradle
plainCradle wdir = do
    return $ Cradle {
        currentDir = wdir
      , rootDir    = wdir
      , tempDir    = error "tmpDir"
      , cabalFile  = Nothing
      , pkgDbStack = [GlobalDb, UserDb]
      }

getPackageDbStack :: FilePath -- ^ Project Directory (where the
                                 -- cabal.sandbox.config file would be if it
                                 -- exists)
                  -> IO [GhcPkgDb]
getPackageDbStack cdir =
    ([GlobalDb] ++) . maybe [UserDb] return <$> getSandboxDb cdir

-- The following is for creating a temporary directory and was taken from
-- Language.Haskell.GhcMod.Utils
--
newTempDir :: FilePath -> IO FilePath
newTempDir dir =
  flip createTempDirectory (uniqTempDirName dir) =<< getTemporaryDirectory

uniqTempDirName :: FilePath -> FilePath
uniqTempDirName dir =
  "ghc-mod" ++ map escapeDriveChar drive ++ map escapePathChar path
  where
    (drive, path) = splitDrive dir
    escapeDriveChar :: Char -> Char
    escapeDriveChar c
      | isAlphaNum c = c
      | otherwise     = '-'
    escapePathChar :: Char -> Char
    escapePathChar c
      | c `elem` pathSeparators = '-'
      | otherwise               = c

fillTempDir :: MonadIO m => Cradle -> m Cradle
fillTempDir crdl = do
  tmpDir <- liftIO $ newTempDir (rootDir crdl)
  return crdl { tempDir = tmpDir }

-- The following is taken from Language.Haskell.GhcMod.PathsAndFiles
findCabalFile :: FilePath -> IO (Maybe FilePath)
findCabalFile dir = do
    -- List of directories and all cabal file candidates
    dcs <- findFileInParentsP  isCabalFile dir :: IO ([(FilePath, [String])])
    let css = uncurry appendDir `map` dcs :: [[FilePath]]
    case find (not . null) css of
      Nothing -> return Nothing
      Just cfs@(_:_:_) -> error "Too many cabal files" -- TODO: Make real error
      Just (a:_)       -> return (Just a)
      Just []          -> error "findCabalFile"
  where
  appendDir :: FilePath -> [String] -> [FilePath]
  appendDir d fs = (d </>) `map` fs

  isCabalFile :: FilePath -> Bool
  isCabalFile f = takeExtension' f == ".cabal"
    where
    takeExtension' :: FilePath -> String
    takeExtension' p =
        if takeFileName p == takeExtension p
          then "" -- just ".cabal" is not a valid cabal file
          else takeExtension p

findFileInParentsP :: (FilePath -> Bool) -> FilePath
                   -> IO [(FilePath, [String])]
findFileInParentsP p dir =
  getFilesP p `zipMapM` parents dir
  where
  zipMapM f as = mapM (\a -> liftM ((,) a) $ f a) as

  getFilesP :: (FilePath -> Bool) -> FilePath -> IO [String]
  getFilesP p dir = filterM p' =<< getDirectoryContents dir
    where
      p' fn = do
        (p fn && ) <$> doesFileExist (dir </> fn)

  parents :: FilePath -> [FilePath]
  parents "" = []
  parents dir' =
    let (drive, dir) = splitDrive $ normalise $ dropTrailingPathSeparator dir'
    in map (joinDrive drive) $ parents' $ filter (/=".") $ splitDirectories dir
    where
    parents' :: [String] -> [FilePath]
    parents' [] | isAbsolute dir' = "":[]
    parents' [] = []
    parents' dir = [joinPath dir] ++ parents' (init dir)

findCradleFile :: FilePath -> IO (Maybe FilePath)
findCradleFile directory = do
    let path = directory </> "ghc-mod.cradle"
    mightExist path


findCabalSandboxDir :: FilePath -> IO (Maybe FilePath)
findCabalSandboxDir dir = do
  dss <- findFileInParentsP isSandboxConfig dir
  return $ case find (not . null . snd) $ dss of
             Just (sbDir, _:_) -> Just sbDir
             _ -> Nothing
 where
   isSandboxConfig = (=="cabal.sandbox.config")


-- | Get path to sandbox config file
getSandboxDb :: FilePath -- ^ Path to the cabal package root directory
                         -- (containing the @cabal.sandbox.config@ file)
             -> IO (Maybe GhcPkgDb)
getSandboxDb d = do
  mConf <- traverse readFile =<< mightExist (d </> "cabal.sandbox.config")
  return $ PackageDb . fixPkgDbVer <$> (extractSandboxDbDir =<< mConf)

  where
  fixPkgDbVer dir =
     case takeFileName dir == ghcSandboxPkgDbDir of
       True -> dir
       False -> takeDirectory dir </> ghcSandboxPkgDbDir

  ghcSandboxPkgDbDir =
    cabalBuildPlatform ++ "-ghc-" ++ cProjectVersion ++ "-packages.conf.d"

  cabalBuildPlatform :: String
  cabalBuildPlatform = unsafePerformIO $ buildPlatform

-- | Extract the sandbox package db directory from the cabal.sandbox.config file.
--   Exception is thrown if the sandbox config file is broken.
extractSandboxDbDir :: String -> Maybe FilePath
extractSandboxDbDir conf = extractValue <$> parse conf
  where
    key = "package-db:"
    keyLen = length key

    parse = listToMaybe . filter (key `isPrefixOf`) . lines
    extractValue = U.dropWhileEnd isSpace . dropWhile isSpace . drop keyLen

mightExist :: FilePath -> IO (Maybe FilePath)
mightExist f = do
  exists <- doesFileExist f
  return $ if exists then (Just f) else (Nothing)
