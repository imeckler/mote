{-# LANGUAGE LambdaCase #-}
module ScratchRepl where

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
-- import qualified System.Console.Readline as Readline

data Command
  = Load FilePath
  | Search Type
  | Reduce (HsExpr RdrName)

data Expr
  = Simple
  | FMap RdrName
  | Compose [RdrName]

{-
parseExpr :: Parser Expr
parseExpr =
  between (token "(") parseExpr (token ")")
  <|> try (string "fmap" *> spaces *> fmap FMap parseExpr)
  <|> _
  <|> Compose <$> sepBy parseExpr (token ".")
  where
  token :: String -> Parser ()
  token x = fmap (\_ -> ()) (string x *> spaces) -}

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

