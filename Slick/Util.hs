{-# LANGUAGE FlexibleContexts #-}
module Slick.Util where

import           Control.Applicative    ((<$>))
import           Control.Monad          ((<=<), liftM)
import           Control.Monad.IO.Class (MonadIO, liftIO)
import           Control.Concurrent.MVar(modifyMVar_, readMVar, newMVar)
import qualified Data.Map               as M
import           Data.Maybe             (catMaybes)
import           DynFlags               (DynFlags)
import           GHC                    ()
import           GhcMonad               (GhcMonad, getSessionDynFlags)
import           Name                   (Name, occName)
import           OccName
import           Outputable             (Outputable, SDoc, neverQualify, ppr,
                                         showSDoc, showSDocForUser)
import           System.IO
import           Type                   (Type)

-- PARSE IMPORTS
import           Control.Monad.Error    (MonadError, throwError)
import           FastString             (fsLit, unpackFS)
import           Lexer                  (P, ParseResult (..), mkPState, unP)
import           SrcLoc                 (GenLocated (..), SrcSpan(..), isSubspanOf,
                                         mkRealSrcLoc, RealSrcSpan)
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

newRef :: MonadIO m => a -> m (Ref a)
newRef = liftIO . newMVar

gReadRef :: MonadIO m => Ref a -> m a
gReadRef = liftIO . readMVar

gModifyRef :: MonadIO m => Ref a -> (a -> a) -> m ()
gModifyRef x f = liftIO $ modifyMVar_ x (return . f)

logS :: MonadIO m => Ref SlickState -> String -> m ()
logS stRef s = liftIO $ flip hPutStrLn s . logFile =<< readMVar stRef

nextSubexpr :: SrcSpan -> [GenLocated SrcSpan b] -> b
nextSubexpr  hole       = foldr (\(L l x) r -> if hole `isSubspanOf` l then x else r) (error "nextSubexpr failure")

nextLocatedSubexpr :: SrcSpan -> [GenLocated SrcSpan b] -> b
nextLocatedSubexpr hole = foldr (\(L l x) r -> if hole `isSubspanOf` l then x else r) (error "nextLocatedSubexpr failure")

nextSubexpr' :: SrcSpan -> [GenLocated SrcSpan a] -> Maybe a
nextSubexpr' hole       = foldr (\(L l x) r -> if hole `isSubspanOf` l then Just x else r) Nothing

toRealSrcSpan :: SrcSpan -> RealSrcSpan
toRealSrcSpan (UnhelpfulSpan _) = error "toRealSrcSpan: Got UnhelpfulSpan"
toRealSrcSpan (RealSrcSpan x0) = x0
-- foldExprs :: ([s] -> s) -> (LHsExpr id -> s -> Maybe s) -> HsModule id ->

eitherThrow :: MonadError e m => Either e a -> m a
eitherThrow = either throwError return

maybeThrow :: MonadError e m => e -> Maybe a -> m a
maybeThrow err = maybe (throwError err) return

getCurrentHoleErr :: Ref SlickState -> M AugmentedHoleInfo
getCurrentHoleErr r = maybe (throwError NoHole) return . currentHole =<< gReadRef r

getFileDataErr :: Ref SlickState -> M FileData
getFileDataErr = maybe (throwError NoFile) return . fileData <=< gReadRef

getHoles :: Ref SlickState -> M [Hole]
getHoles = fmap (M.keys . holesInfo) . getFileDataErr

occNameToString :: OccName -> String
occNameToString = unpackFS . occNameFS

nameToString :: Name -> String
nameToString = occNameToString . occName

showType :: DynFlags -> Type -> String
showType fs = showSDocForUser fs neverQualify . ppr

mapMaybeM :: Monad m => (a -> m (Maybe b)) -> [a] -> m [b]
mapMaybeM f = liftM catMaybes . mapM f

headErr :: MonadError ErrorType m => [a] -> m a
headErr xs = case xs of
  [] -> throwError $ OtherError "headErr: Empty list"
  x : xs -> return x
