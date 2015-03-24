module CabalVersions.Cabal22 where

import Distribution.Package (InstalledPackageId)
import Data.Version (Version)
import Distribution.ModuleName (ModuleName)
import Data.Map (Map)

data ModuleRenaming = ModuleRenaming Bool [(ModuleName, ModuleName)]
  deriving (Show, Read, Eq, Ord)

data OriginalModule
   = OriginalModule {
       originalPackageId :: InstalledPackageId,
       originalModuleName :: ModuleName
     }
  deriving (Eq, Read, Show)

data ExposedModule
   = ExposedModule {
       exposedName      :: ModuleName,
       exposedReexport  :: Maybe OriginalModule,
       exposedSignature :: Maybe OriginalModule -- This field is unused for now.
     }
  deriving (Read, Show)

data LibraryName = LibraryName String
    deriving (Read, Show)

newtype PackageName = PackageName { unPackageName :: String }
  deriving (Read, Show, Eq, Ord)

data PackageIdentifier
  = PackageIdentifier {
    pkgName :: PackageName,
    pkgVersion :: Version
  }
  deriving (Read, Show)

type PackageId = PackageIdentifier

data ComponentLocalBuildInfo
  = LibComponentLocalBuildInfo {
    componentPackageDeps :: [(InstalledPackageId, PackageId)],
    componentExposedModules :: [ExposedModule],
    componentPackageRenaming :: Map PackageName ModuleRenaming,
    componentLibraries :: [LibraryName]
  }
  | ExeComponentLocalBuildInfo {
    componentPackageDeps :: [(InstalledPackageId, PackageId)],
    componentPackageRenaming :: Map PackageName ModuleRenaming
  }
  | TestComponentLocalBuildInfo {
    componentPackageDeps :: [(InstalledPackageId, PackageId)],
    componentPackageRenaming :: Map PackageName ModuleRenaming
  }
  | BenchComponentLocalBuildInfo {
    componentPackageDeps :: [(InstalledPackageId, PackageId)],
    componentPackageRenaming :: Map PackageName ModuleRenaming
  }
  deriving (Read, Show)

