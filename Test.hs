module Test where

import Prelude hiding (Word)
import Data.Traversable
import qualified Data.List as List
import qualified Data.Maybe as Maybe
import Var
import qualified Search.Types.Word as Word
import Search.Types.Word (Word(..))
import qualified Search.Types
import qualified Mote.Search.ChooseAType as ChooseAType
import Mote.Search.NatTransData
import qualified Type
import TypeRep
import Mote.Search.WrappedType
import qualified VarEnv
import Scratch
import Data.Monoid
import GHC (Ghc)
import Control.Monad.Error

eitherToMaybe :: Either String a -> Maybe a
eitherToMaybe = either (const Nothing) Just

matchesInView'
  :: Var
  -> ChooseAType.ChooseAType [NatTransData () Type]
  -> Word.View SyntacticFunctor WrappedType
  -> [(Word SyntacticFunctor WrappedType, Search.Types.Move SyntacticFunctor WrappedType)]
matchesInView' innerVar chooseAType wv =
  concatMap
    (\(subst, nds) ->
        map
          _
          -- (newWordAndMove . natTransDataToTrans . closedSubstNatTransData (Type.mkTvSubst VarEnv.emptyInScopeSet subst))
          nds)
    (ChooseAType.lookup _ chooseAType)
  where
  (focus, newWordAndMove) = case wv of
    Word.NoO pre foc post ->
      ( stitchUp (TyVarTy innerVar) foc 
      -- TODO: Should take subst as argument
      , \t ->
        (Word pre Nothing <> Search.Types.to t <> Word post Nothing, Word.Middle pre t (Word post Nothing))
      )

    -- YesOMid and NoO can be unified with Middle, but it is a bit confusing.
    Word.YesOMid pre foc post o ->
      ( stitchUp (TyVarTy innerVar) foc
      , \t ->
        (Word pre Nothing <> Search.Types.to t <> Word post (Just o), Word.Middle pre t (Word post (Just o)))
      )

    Word.YesOEnd pre (foc, WrappedType o) ->
      ( stitchUp o foc
      , \t ->
        (Word pre Nothing <> Search.Types.to t, Word.End pre t)
      )
