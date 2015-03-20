module Slick.Util where

import           Control.Applicative    ((<$>))
import           Control.Monad          ((<=<))
import           Control.Monad.IO.Class (MonadIO, liftIO)
import           Data.IORef             (IORef, modifyIORef, readIORef)
import qualified Data.Map               as M
import           GHC                    ()
import           DynFlags (DynFlags)
import           GhcMonad               (GhcMonad, getSessionDynFlags)
import           Outputable             (Outputable, SDoc, ppr, showSDoc, showSDocForUser, neverQualify)
import OccName
import Type (Type)
import           System.IO

-- PARSE IMPORTS
import           Control.Monad.Error    (MonadError, throwError)
import           FastString             (fsLit, unpackFS)
import           Lexer                  (P, ParseResult (..), mkPState, unP)
import           SrcLoc                 (GenLocated (..), SrcSpan, isSubspanOf,
                                         mkRealSrcLoc)
import           StringBuffer           (stringToStringBuffer)

import           Slick.Types

runParserM :: GhcMonad m => Lexer.P a -> String -> m (Either String a)
runParserM parser str = do
  fs <- getSessionDynFlags
  let buf = stringToStringBuffer str
      loc = mkRealSrcLoc (fsLit "<slick>") 1 1
  return $ case unP parser (mkPState fs buf loc) of
    PFailed _span err -> Left (showSDoc fs err)
    POk _pst x        -> Right x


(>>|) :: Functor f => f a -> (a -> b) -> f b
(>>|) x f = fmap f x

showPprM :: (Outputable a, GhcMonad m) => a -> m String
showPprM = showSDocM . ppr

output :: (Outputable a, GhcMonad m) => a -> m ()
output = liftIO . putStrLn <=< showSDocM . ppr

showSDocM :: GhcMonad m => SDoc -> m String
showSDocM x = getSessionDynFlags >>| \fs -> showSDoc fs x

gReadIORef :: MonadIO m => IORef a -> m a
gReadIORef = liftIO . readIORef

gModifyIORef :: MonadIO m => IORef a -> (a -> a) -> m ()
gModifyIORef x = liftIO . modifyIORef x

logS :: MonadIO m => IORef SlickState -> String -> m ()
logS stRef s = liftIO $ flip hPutStrLn s . logFile =<< readIORef stRef

nextSubexpr :: SrcSpan -> [GenLocated SrcSpan b] -> b
nextSubexpr  hole       = foldr (\(L l x) r -> if hole `isSubspanOf` l then x else r) (error "nextSubexpr failure")

nextLocatedSubexpr :: SrcSpan -> [GenLocated SrcSpan b] -> b
nextLocatedSubexpr hole = foldr (\(L l x) r -> if hole `isSubspanOf` l then x else r) (error "nextLocatedSubexpr failure")

nextSubexpr' :: SrcSpan -> [GenLocated SrcSpan a] -> Maybe a
nextSubexpr' hole       = foldr (\(L l x) r -> if hole `isSubspanOf` l then Just x else r) Nothing

-- foldExprs :: ([s] -> s) -> (LHsExpr id -> s -> Maybe s) -> HsModule id ->

eitherThrow :: MonadError e m => Either e a -> m a
eitherThrow = either throwError return

maybeThrow :: MonadError e m => e -> Maybe a -> m a
maybeThrow err = maybe (throwError err) return

getCurrentHoleInfoErr :: IORef SlickState -> M HoleInfo
getCurrentHoleInfoErr r = do
  h <- getCurrentHoleErr r
  infos <- holesInfo <$> gReadIORef r
  maybeThrow NotInMap $ M.lookup h infos


getCurrentHoleErr :: IORef SlickState -> M Hole
getCurrentHoleErr r = maybe (throwError NoHole) return . currentHole =<< gReadIORef r

getFileDataErr :: IORef SlickState -> M FileData
getFileDataErr = maybe (throwError NoFile) return . fileData <=< gReadIORef

getHoles :: IORef SlickState -> M [Hole]
getHoles = fmap (M.keys . holesInfo) . gReadIORef

occNameToString :: OccName -> String
occNameToString = unpackFS . occNameFS

showType :: DynFlags -> Type -> String
showType fs = showSDocForUser fs neverQualify . ppr

