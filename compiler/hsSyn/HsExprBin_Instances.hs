-- too noisy during development...
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
module HsExprBin_Instances where

import Control.Applicative
import Control.Monad

import BasicTypes
import Binary
import CoreSyn ( Tickish(..) )
import GhcPrelude
import HsBinds
import HsDecls
import HsExpr
import HsExtension
import HsLit
import HsPat
import HsTypes
import Name
import Outputable
import RdrName
import SeName
import SrcLoc
import TcEvidence (HsWrapper(WpHole))

-- * Utilities

putPanic :: String -> String -> a
putPanic tyName conName =
  panic ("Binary " ++ tyName ++ ".put: " ++ conName ++ " not supported")

getPanic :: String -> a
getPanic tyName =
  panic ("Binary " ++ tyName ++ ".get: unknown (or unsupported) tag")

-- * Binary instances

instance Binary (HsExpr GhcSe) where
  put_ bh e = case e of
    HsVar a b ->
      putByte bh 0 >> put_ bh a >> put_ bh b
    HsUnboundVar a b ->
      putByte bh 1 >> put_ bh a >> put_ bh b
    HsRecFld a b ->
      putByte bh 2 >> put_ bh a >> put_ bh b
    HsOverLabel a b c ->
      putByte bh 3 >> put_ bh a >> put_ bh b >> put_ bh c
    HsIPVar a b ->
      putByte bh 4 >> put_ bh a >> put_ bh b
    HsOverLit a b ->
      putByte bh 5 >> put_ bh a >> put_ bh b
    HsLit a b ->
      putByte bh 6 >> put_ bh a >> put_ bh b
    HsLam a b ->
      putByte bh 7 >> put_ bh a >> put_ bh b
    HsLamCase a b ->
      putByte bh 8 >> put_ bh a >> put_ bh b
    HsApp a b c ->
      putByte bh 9 >> put_ bh a >> put_ bh b >> put_ bh c
    HsAppType a b ->
      putByte bh 10 >> put_ bh a >> put_ bh b
    OpApp a b c d ->
      putByte bh 11 >> put_ bh a >> put_ bh b >> put_ bh c
                    >> put_ bh d
    NegApp a b c ->
      putByte bh 12 >> put_ bh a >> put_ bh b >> put_ bh c
    HsPar a b ->
      putByte bh 13 >> put_ bh a >> put_ bh b
    SectionL a b c ->
      putByte bh 14 >> put_ bh a >> put_ bh b >> put_ bh c
    SectionR a b c ->
      putByte bh 15 >> put_ bh a >> put_ bh b >> put_ bh c
    ExplicitTuple a b c ->
      putByte bh 16 >> put_ bh a >> put_ bh b >> put_ bh c
    ExplicitSum a b c d ->
      putByte bh 17 >> put_ bh a >> put_ bh b >> put_ bh c
                    >> put_ bh d
    HsCase a b c ->
      putByte bh 18 >> put_ bh a >> put_ bh b >> put_ bh c
    HsIf a b c d e ->
      putByte bh 19 >> put_ bh a >> put_ bh b >> put_ bh c
                    >> put_ bh d >> put_ bh e
    HsMultiIf a b ->
      putByte bh 20 >> put_ bh a >> put_ bh b
    HsLet a b c ->
      putByte bh 21 >> put_ bh a >> put_ bh b >> put_ bh c
    HsDo a b c ->
      putByte bh 22 >> put_ bh a >> put_ bh b >> put_ bh c
    ExplicitList a b c ->
      putByte bh 23 >> put_ bh a >> put_ bh b >> put_ bh c
    RecordCon a b c ->
      putByte bh 24 >> put_ bh a >> put_ bh b >> put_ bh c
    RecordUpd a b c ->
      putByte bh 25 >> put_ bh a >> put_ bh b >> put_ bh c
    ExprWithTySig a b ->
      putByte bh 26 >> put_ bh a >> put_ bh b
    ArithSeq a b c ->
      putByte bh 27 >> put_ bh a >> put_ bh b >> put_ bh c
    EWildPat a ->
      putByte bh 28 >> put_ bh a
    EAsPat a b c ->
      putByte bh 29 >> put_ bh a >> put_ bh b >> put_ bh c
    EViewPat a b c ->
      putByte bh 30 >> put_ bh a >> put_ bh b >> put_ bh c
    ELazyPat a b ->
      putByte bh 31 >> put_ bh a >> put_ bh b
    HsStatic a b ->
      putByte bh 32 >> put_ bh a >> put_ bh b
    HsProc a b c ->
      putByte bh 33 >> put_ bh a >> put_ bh b >> put_ bh c
    HsBinTick a b c d ->
      putByte bh 34 >> put_ bh a >> put_ bh b >> put_ bh c
                    >> put_ bh d
    HsTickPragma a b c d e ->
      putByte bh 35 >> put_ bh a >> put_ bh b >> put_ bh c
                    >> put_ bh d >> put_ bh e
    HsSpliceE a b ->
      putByte bh 36 >> put_ bh a >> put_ bh b
    HsSCC a b c d ->
      putByte bh 37 >> put_ bh a >> put_ bh b >> put_ bh c
                    >> put_ bh d
    HsCoreAnn a b c d ->
      putByte bh 38 >> put_ bh a >> put_ bh b >> put_ bh c
                    >> put_ bh d
    HsBracket a b ->
      putByte bh 39 >> put_ bh a >> put_ bh b
    XExpr a ->
      putByte bh 40 >> put_ bh a
    HsConLikeOut {} -> putPanic "HsExpr" "HsConLikeOut"
    HsRnBracketOut {} -> putPanic "HsExpr" "HsRnBracketOut"
    HsTcBracketOut {} -> putPanic "HsExpr" "HsTcBracketOut"
    HsArrApp {} -> putPanic "HsExpr" "HsArrApp"
    HsArrForm {} -> putPanic "HsExpr" "HsArrForm"
    HsTick {} -> putPanic "HsExpr" "HsTick"
    HsWrap {} -> putPanic "HsExpr" "HsWrap"
  get bh = do
    tag <- getByte bh
    case tag of
      0  -> HsVar <$> get bh <*> get bh
      1  -> HsUnboundVar <$> get bh <*> get bh
      2  -> HsRecFld <$> get bh <*> get bh
      3  -> HsOverLabel <$> get bh <*> get bh <*> get bh
      4  -> HsIPVar <$> get bh <*> get bh
      5  -> HsOverLit <$> get bh <*> get bh
      6  -> HsLit <$> get bh <*> get bh
      7  -> HsLam <$> get bh <*> get bh
      8  -> HsLamCase <$> get bh <*> get bh
      9  -> HsApp <$> get bh <*> get bh <*> get bh
      10 -> HsAppType <$> get bh <*> get bh
      11 -> OpApp <$> get bh <*> get bh <*> get bh <*> get bh
      12 -> NegApp <$> get bh <*> get bh <*> get bh
      13 -> HsPar <$> get bh <*> get bh
      14 -> SectionL <$> get bh <*> get bh <*> get bh
      15 -> SectionR <$> get bh <*> get bh <*> get bh
      16 -> ExplicitTuple <$> get bh <*> get bh <*> get bh
      17 -> ExplicitSum <$> get bh <*> get bh <*> get bh <*> get bh
      18 -> HsCase <$> get bh <*> get bh <*> get bh
      19 -> HsIf <$> get bh <*> get bh <*> get bh <*> get bh <*> get bh
      20 -> HsMultiIf <$> get bh <*> get bh
      21 -> HsLet <$> get bh <*> get bh <*> get bh
      22 -> HsDo <$> get bh <*> get bh <*> get bh
      23 -> ExplicitList <$> get bh <*> get bh <*> get bh
      24 -> RecordCon <$> get bh <*> get bh <*> get bh
      25 -> RecordUpd <$> get bh <*> get bh <*> get bh
      26 -> ExprWithTySig <$> get bh <*> get bh
      27 -> ArithSeq <$> get bh <*> get bh <*> get bh
      28 -> EWildPat <$> get bh
      29 -> EAsPat <$> get bh <*> get bh <*> get bh
      30 -> EViewPat <$> get bh <*> get bh <*> get bh
      31 -> ELazyPat <$> get bh <*> get bh
      32 -> HsStatic <$> get bh <*> get bh
      33 -> HsProc <$> get bh <*> get bh <*> get bh
      34 -> HsBinTick <$> get bh <*> get bh <*> get bh <*> get bh
      35 -> HsTickPragma <$> get bh <*> get bh <*> get bh
                         <*> get bh <*> get bh
      36 -> HsSpliceE <$> get bh <*> get bh
      37 -> HsSCC <$> get bh <*> get bh <*> get bh <*> get bh
      38 -> HsCoreAnn <$> get bh <*> get bh <*> get bh <*> get bh
      39 -> HsBracket <$> get bh <*> get bh
      40 -> XExpr <$> get bh
      _  -> getPanic "HsExpr"

instance Binary (HsBracket GhcSe) where
  put_ bh b = case b of
    ExpBr a b ->
      putByte bh 0 >> put_ bh a >> put_ bh b
    PatBr a b ->
      putByte bh 1 >> put_ bh a >> put_ bh b
    DecBrL a b ->
      putByte bh 2 >> put_ bh a >> put_ bh b
    DecBrG a b ->
      putByte bh 3 >> put_ bh a >> put_ bh b
    TypBr a b ->
      putByte bh 4 >> put_ bh a >> put_ bh b
    VarBr a b c ->
      putByte bh 5 >> put_ bh a >> put_ bh b >> put_ bh c
    TExpBr a b ->
      putByte bh 6 >> put_ bh a >> put_ bh b
    XBracket a ->
      putByte bh 7 >> put_ bh a
  get bh = do
    tag <- getByte bh
    case tag of
      0 -> ExpBr <$> get bh <*> get bh
      1 -> PatBr <$> get bh <*> get bh
      2 -> DecBrL <$> get bh <*> get bh
      3 -> DecBrG <$> get bh <*> get bh
      4 -> TypBr <$> get bh <*> get bh
      5 -> VarBr <$> get bh <*> get bh <*> get bh
      6 -> TExpBr <$> get bh <*> get bh
      7 -> XBracket <$> get bh
      _ -> getPanic "HsBracket"

instance Binary SeName where
  put_ bh (SeName n) = put_ bh n
  get bh = mkSeName <$> get bh

instance Binary UnboundVar where
  put_ bh v = case v of
    OutOfScope a b -> putByte bh 0 >> put_ bh a >> put_ bh b
    TrueExprHole a -> putByte bh 1 >> put_ bh a
  get bh = do
    tag <- getByte bh
    case tag of
      0 -> OutOfScope <$> get bh <*> get bh
      1 -> TrueExprHole <$> get bh
      _ -> getPanic "UnboundVar"

instance Binary a => Binary (StmtLR GhcSe GhcSe a) where
  put_ bh s = case s of
    LastStmt a b c d ->
      putByte bh 0 >> put_ bh a >> put_ bh b >> put_ bh c >> put_ bh d
    BindStmt a b c d e ->
      putByte bh 1 >> put_ bh a >> put_ bh b >> put_ bh c >> put_ bh d
                   >> put_ bh e
    ApplicativeStmt a b c ->
      putByte bh 2 >> put_ bh a >> put_ bh b >> put_ bh c
    BodyStmt a b c d ->
      putByte bh 3 >> put_ bh a >> put_ bh b >> put_ bh c >> put_ bh d
    LetStmt a b ->
      putByte bh 4 >> put_ bh a >> put_ bh b
    ParStmt a b c d ->
      putByte bh 5 >> put_ bh a >> put_ bh b >> put_ bh c >> put_ bh d
    RecStmt a b c d e f g ->
      putByte bh 6 >> put_ bh a >> put_ bh b >> put_ bh c >> put_ bh d
                   >> put_ bh e >> put_ bh f >> put_ bh g
    TransStmt a b c d e f g h i ->
      putByte bh 7 >> put_ bh a >> put_ bh b >> put_ bh c >> put_ bh d
                   >> put_ bh e >> put_ bh f >> put_ bh g >> put_ bh h
                   >> put_ bh i
    XStmtLR a ->
      putByte bh 8 >> put_ bh a

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> LastStmt <$> get bh <*> get bh <*> get bh <*> get bh
      1 -> BindStmt <$> get bh <*> get bh <*> get bh <*> get bh <*> get bh
      2 -> ApplicativeStmt <$> get bh <*> get bh <*> get bh
      3 -> BodyStmt <$> get bh <*> get bh <*> get bh <*> get bh
      4 -> LetStmt <$> get bh <*> get bh
      5 -> ParStmt <$> get bh <*> get bh <*> get bh <*> get bh
      6 -> RecStmt <$> get bh <*> get bh <*> get bh <*> get bh <*> get bh
                   <*> get bh <*> get bh
      7 -> TransStmt <$> get bh <*> get bh <*> get bh <*> get bh
                     <*> get bh <*> get bh <*> get bh <*> get bh
                     <*> get bh
      8 -> XStmtLR <$> get bh
      _ -> getPanic "StmtLR"

instance Binary (HsGroup GhcSe) where
  put_ bh x = case x of
    HsGroup a b c d e f g h i j k l ->
      putByte bh 0 >> put_ bh a >> put_ bh b >> put_ bh c >> put_ bh d
                   >> put_ bh e >> put_ bh f >> put_ bh g >> put_ bh h
                   >> put_ bh i >> put_ bh j >> put_ bh k >> put_ bh l
    XHsGroup a ->
      putByte bh 1 >> put_ bh a

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> HsGroup <$> get bh <*> get bh <*> get bh <*> get bh
                   <*> get bh <*> get bh <*> get bh <*> get bh
                   <*> get bh <*> get bh <*> get bh <*> get bh
      1 -> XHsGroup <$> get bh
      _ -> getPanic "HsGroup"

instance Binary (TyClGroup GhcSe) where
  put_ bh g = case g of
    TyClGroup a b c d ->
      putByte bh 0 >> put_ bh a >> put_ bh b >> put_ bh c >> put_ bh d
    XTyClGroup a ->
      putByte bh 1 >> put_ bh a

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> TyClGroup <$> get bh <*> get bh <*> get bh <*> get bh
      1 -> XTyClGroup <$> get bh
      _ -> getPanic "TyClGroup"

instance Binary (HsCmdTop GhcSe) where
  put_ bh c = case c of
    HsCmdTop a b ->
      putByte bh 0 >> put_ bh a >> put_ bh b
    XCmdTop a ->
      putByte bh 1 >> put_ bh a

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> HsCmdTop <$> get bh <*> get bh
      1 -> XCmdTop <$> get bh
      _ -> getPanic "HsCmdTop"

instance Binary (HsCmd GhcSe) where
  put_ bh c = case c of
    HsCmdArrApp a b c d e ->
      putByte bh 0 >> put_ bh a >> put_ bh b >> put_ bh c
                   >> put_ bh d >> put_ bh e
    HsCmdArrForm a b c d e ->
      putByte bh 1 >> put_ bh a >> put_ bh b >> put_ bh c
                   >> put_ bh d >> put_ bh e
    HsCmdApp a b c ->
      putByte bh 2 >> put_ bh a >> put_ bh b >> put_ bh c
    HsCmdLam a b ->
      putByte bh 3 >> put_ bh a >> put_ bh b
    HsCmdPar a b ->
      putByte bh 4 >> put_ bh a >> put_ bh b
    HsCmdCase a b c ->
      putByte bh 5 >> put_ bh a >> put_ bh b >> put_ bh c
    HsCmdIf a b c d e ->
      putByte bh 6 >> put_ bh a >> put_ bh b >> put_ bh c
                   >> put_ bh d >> put_ bh e
    HsCmdLet a b c ->
      putByte bh 7 >> put_ bh a >> put_ bh b >> put_ bh c
    HsCmdDo a b ->
      putByte bh 8 >> put_ bh a >> put_ bh b
    XCmd a ->
      putByte bh 9 >> put_ bh a
    HsCmdWrap {} ->
      putPanic "HsCmdWrap" "HsCmd"

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> HsCmdArrApp <$> get bh <*> get bh <*> get bh
                       <*> get bh <*> get bh
      1 -> HsCmdArrForm <$> get bh <*> get bh <*> get bh
                        <*> get bh <*> get bh
      2 -> HsCmdApp <$> get bh <*> get bh <*> get bh
      3 -> HsCmdLam <$> get bh <*> get bh
      4 -> HsCmdPar <$> get bh <*> get bh
      5 -> HsCmdCase <$> get bh <*> get bh <*> get bh
      6 -> HsCmdIf <$> get bh <*> get bh <*> get bh <*> get bh <*> get bh
      7 -> HsCmdLet <$> get bh <*> get bh <*> get bh
      8 -> HsCmdDo <$> get bh <*> get bh
      9 -> XCmd <$> get bh
      _ -> getPanic "HsCmd"

instance Binary HsArrAppType where
  put_ bh t = putByte bh $ case t of
    HsHigherOrderApp -> 0
    HsFirstOrderApp  -> 1
  get bh = do
    tag <- getByte bh
    case tag of
      0 -> pure HsHigherOrderApp
      1 -> pure HsFirstOrderApp
      _ -> getPanic "HsArrAppType"

instance Binary TransForm where
  put_ bh f = putByte bh $ case f of
    ThenForm  -> 0
    GroupForm -> 1
  get bh = do
    tag <- getByte bh
    case tag of
      0 -> pure ThenForm
      1 -> pure GroupForm
      _ -> getPanic "TransForm"

instance Binary (ApplicativeArg GhcSe) where
  put_ bh a = case a of
    ApplicativeArgOne a b c d ->
      putByte bh 0 >> put_ bh a >> put_ bh b >> put_ bh c >> put_ bh d
    ApplicativeArgMany a b c d ->
      putByte bh 1 >> put_ bh a >> put_ bh b >> put_ bh c >> put_ bh d
    XApplicativeArg a ->
      putByte bh 2 >> put_ bh a
  get bh = do
    tag <- getByte bh
    case tag of
      0 -> ApplicativeArgOne <$> get bh <*> get bh <*> get bh <*> get bh
      1 -> ApplicativeArgMany <$> get bh <*> get bh <*> get bh <*> get bh
      2 -> XApplicativeArg <$> get bh
      _ -> getPanic "ApplicativeArg"

instance Binary (ParStmtBlock GhcSe GhcSe) where
  put_ bh b = case b of
    ParStmtBlock a b c d ->
      putByte bh 0 >> put_ bh a >> put_ bh b >> put_ bh c >> put_ bh d
    XParStmtBlock a ->
      putByte bh 1 >> put_ bh a

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> ParStmtBlock <$> get bh <*> get bh <*> get bh <*> get bh
      1 -> XParStmtBlock <$> get bh
      _ -> getPanic "ParStmtBlock"

instance Binary (SyntaxExpr GhcSe) where
  put_ bh (SyntaxExpr a [] WpHole) = put_ bh a
  put_ _ _ = panic "Binary SyntaxExpr.put: wrappers should be empty"
  get bh = SyntaxExpr <$> get bh <*> pure [] <*> pure WpHole

instance Binary a => Binary (GRHSs GhcSe a) where
  put_ bh g = case g of
    GRHSs a b c -> putByte bh 0 >> put_ bh a >> put_ bh b >> put_ bh c
    XGRHSs a -> putByte bh 1 >> put_ bh a

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> GRHSs <$> get bh <*> get bh <*> get bh
      1 -> XGRHSs <$> get bh
      _ -> getPanic "GRHSs"

instance Binary a => Binary (GRHS GhcSe a) where
  put_ bh g = case g of
    GRHS a b c -> putByte bh 0 >> put_ bh a >> put_ bh b >> put_ bh c
    XGRHS a -> putByte bh 1 >> put_ bh a

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> GRHS <$> get bh <*> get bh <*> get bh
      1 -> XGRHS <$> get bh
      _ -> getPanic "GRHS"

instance Binary a => Binary (MatchGroup GhcSe a) where
  put_ bh g = case g of
    MG a b c -> putByte bh 0 >> put_ bh a >> put_ bh b >> put_ bh c
    XMatchGroup a -> putByte bh 1 >> put_ bh a

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> MG <$> get bh <*> get bh <*> get bh
      1 -> XMatchGroup <$> get bh
      _ -> getPanic "MatchGroup"

instance Binary a => Binary (Match GhcSe a) where
  put_ bh m = case m of
    Match a b c d ->
      putByte bh 0 >> put_ bh a >> put_ bh b >> put_ bh c >> put_ bh d
    XMatch a ->
      putByte bh 1 >> put_ bh a

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> Match <$> get bh <*> get bh <*> get bh <*> get bh
      1 -> XMatch <$> get bh
      _ -> getPanic "Match"

instance Binary (HsMatchContext SeName) where
  put_ bh c = case c of
    FunRhs a b c ->
      putByte bh 0 >> put_ bh a >> put_ bh b >> put_ bh c
    LambdaExpr ->
      putByte bh 1
    CaseAlt ->
      putByte bh 2
    IfAlt ->
      putByte bh 3
    ProcExpr ->
      putByte bh 4
    PatBindRhs ->
      putByte bh 5
    RecUpd ->
      putByte bh 6
    StmtCtxt a ->
      putByte bh 7 >> put_ bh a
    ThPatSplice ->
      putByte bh 8
    ThPatQuote ->
      putByte bh 9
    PatSyn ->
      putByte bh 10
    PatBindGuards ->
      putByte bh 11
  get bh = do
    tag <- getByte bh
    case tag of
      0  -> FunRhs <$> get bh <*> get bh <*> get bh
      1  -> pure LambdaExpr
      2  -> pure CaseAlt
      3  -> pure IfAlt
      4  -> pure ProcExpr
      5  -> pure PatBindRhs
      6  -> pure RecUpd
      7  -> StmtCtxt <$> get bh
      8  -> pure ThPatSplice
      9  -> pure ThPatQuote
      10 -> pure PatSyn
      11 -> pure PatBindGuards
      _  -> getPanic "HsMatchContext"

instance Binary (HsStmtContext SeName) where
  put_ bh c = case c of
    ListComp        -> putByte bh 0
    MonadComp       -> putByte bh 1
    DoExpr          -> putByte bh 3
    MDoExpr         -> putByte bh 4
    ArrowExpr       -> putByte bh 5
    GhciStmtCtxt    -> putByte bh 6
    PatGuard a      -> putByte bh 7 >> put_ bh a
    ParStmtCtxt a   -> putByte bh 8 >> put_ bh a
    TransStmtCtxt a -> putByte bh 9 >> put_ bh a
  get bh = do
    tag <- getByte bh
    case tag of
      0 -> pure ListComp
      1 -> pure MonadComp
      3 -> pure DoExpr
      4 -> pure MDoExpr
      5 -> pure ArrowExpr
      6 -> pure GhciStmtCtxt
      7 -> PatGuard <$> get bh
      8 -> ParStmtCtxt <$> get bh
      9 -> TransStmtCtxt <$> get bh
      _ -> getPanic "HsStmtContext"

instance Binary (ArithSeqInfo GhcSe) where
  put_ bh i = case i of
    From a ->
      putByte bh 0 >> put_ bh a
    FromThen a b ->
      putByte bh 1 >> put_ bh a >> put_ bh b
    FromTo a b ->
      putByte bh 2 >> put_ bh a >> put_ bh b
    FromThenTo a b c ->
      putByte bh 3 >> put_ bh a >> put_ bh b >> put_ bh c
  get bh = do
    tag <- getByte bh
    case tag of
      0 -> From <$> get bh
      1 -> FromThen <$> get bh <*> get bh
      2 -> FromTo <$> get bh <*> get bh
      3 -> FromThenTo <$> get bh <*> get bh <*> get bh
      _ -> getPanic "ArithSeqInfo"

instance Binary (HsTupArg GhcSe) where
  put_ bh a = case a of
    Present a b -> putByte bh 0 >> put_ bh a >> put_ bh b
    Missing a -> putByte bh 1 >> put_ bh a
    XTupArg a -> putByte bh 2 >> put_ bh a
  get bh = do
    tag <- getByte bh
    case tag of
      0 -> Present <$> get bh <*> get bh
      1 -> Missing <$> get bh
      2 -> XTupArg <$> get bh
      _ -> getPanic "HsTupArg"

instance Binary (Pat GhcSe) where
  put_ bh p = case p of
    WildPat a ->
      putByte bh 0 >> put_ bh a
    VarPat a b ->
      putByte bh 1 >> put_ bh a >> put_ bh b
    LazyPat a b ->
      putByte bh 2 >> put_ bh a >> put_ bh b
    AsPat a b c ->
      putByte bh 3 >> put_ bh a >> put_ bh b >> put_ bh c
    ParPat a b ->
      putByte bh 4 >> put_ bh a >> put_ bh b
    BangPat a b ->
      putByte bh 5 >> put_ bh a >> put_ bh b
    ListPat a b ->
      putByte bh 6 >> put_ bh a >> put_ bh b
    TuplePat a b c ->
      putByte bh 7 >> put_ bh a >> put_ bh b >> put_ bh c
    SumPat a b c d ->
      putByte bh 8 >> put_ bh a >> put_ bh b >> put_ bh c >> put_ bh d
    ConPatIn a b ->
      putByte bh 9 >> put_ bh a >> put_ bh b
    ViewPat a b c ->
      putByte bh 10 >> put_ bh a >> put_ bh b >> put_ bh c
    LitPat a b ->
      putByte bh 11 >> put_ bh a >> put_ bh b
    NPat a b c d ->
      putByte bh 12 >> put_ bh a >> put_ bh b >> put_ bh c >> put_ bh d
    NPlusKPat a b c d e f ->
      putByte bh 13 >> put_ bh a >> put_ bh b >> put_ bh c >> put_ bh d
                    >> put_ bh e >> put_ bh f
    SigPat a b ->
      putByte bh 14 >> put_ bh a >> put_ bh b
    SplicePat a b ->
      putByte bh 15 >> put_ bh a >> put_ bh b
    XPat a ->
      putByte bh 16 >> put_ bh a
    ConPatOut {} -> putPanic "Pat" "ConPatOut"
    CoPat {} -> putPanic "Pat" "CoPat"
  get bh = do
    tag <- getByte bh
    case tag of
      0 -> WildPat <$> get bh
      1 -> VarPat <$> get bh <*> get bh
      2 -> LazyPat <$> get bh <*> get bh
      3 -> AsPat <$> get bh <*> get bh <*> get bh
      4 -> ParPat <$> get bh <*> get bh
      5 -> BangPat <$> get bh <*> get bh
      6 -> ListPat <$> get bh <*> get bh
      7 -> TuplePat <$> get bh <*> get bh <*> get bh
      8 -> SumPat <$> get bh <*> get bh <*> get bh <*> get bh
      9 -> ConPatIn <$> get bh <*> get bh
      10 -> ViewPat <$> get bh <*> get bh <*> get bh
      11 -> LitPat <$> get bh <*> get bh
      12 -> NPat <$> get bh <*> get bh <*> get bh <*> get bh
      13 -> NPlusKPat <$> get bh <*> get bh <*> get bh <*> get bh
                      <*> get bh <*> get bh
      14 -> SigPat <$> get bh <*> get bh
      15 -> SplicePat <$> get bh <*> get bh
      16 -> XPat <$> get bh
      _ -> getPanic "HsPat"

instance Binary NoExt where
  put_ _ NoExt = return ()
  get _ = pure NoExt

instance (Binary (FieldOcc a), Binary b) => Binary (HsRecFields a b) where
  put_ bh (HsRecFields a b) = put_ bh a >> put_ bh b
  get bh = HsRecFields <$> get bh <*> get bh

instance (Binary id, Binary arg) => Binary (HsRecField' id arg) where
  put_ bh (HsRecField a b c) = put_ bh a >> put_ bh b >> put_ bh c
  get bh = HsRecField <$> get bh <*> get bh <*> get bh

instance Binary (HsType GhcSe) where
  put_ bh t = case t of
    HsForAllTy a b c ->
      putByte bh 0 >> put_ bh a >> put_ bh b >> put_ bh c
    HsQualTy a b c ->
      putByte bh 1 >> put_ bh a >> put_ bh b >> put_ bh c
    HsTyVar a b c ->
      putByte bh 2 >> put_ bh a >> put_ bh b >> put_ bh c
    HsAppTy a b c ->
      putByte bh 3 >> put_ bh a >> put_ bh b >> put_ bh c
    HsFunTy a b c ->
      putByte bh 4 >> put_ bh a >> put_ bh b >> put_ bh c
    HsListTy a b ->
      putByte bh 5 >> put_ bh a >> put_ bh b
    HsTupleTy a b c ->
      putByte bh 6 >> put_ bh a >> put_ bh b >> put_ bh c
    HsSumTy a b ->
      putByte bh 7 >> put_ bh a >> put_ bh b
    HsOpTy a b c d ->
      putByte bh 8 >> put_ bh a >> put_ bh b >> put_ bh c >> put_ bh d
    HsParTy a b ->
      putByte bh 9 >> put_ bh a >> put_ bh b
    HsIParamTy a b c ->
      putByte bh 10 >> put_ bh a >> put_ bh b >> put_ bh c
    HsKindSig a b c ->
      putByte bh 11 >> put_ bh a >> put_ bh b >> put_ bh c
    HsBangTy a b c ->
      putByte bh 12 >> put_ bh a >> put_ bh b >> put_ bh c
    HsRecTy a b ->
      putByte bh 13 >> put_ bh a >> put_ bh b
    HsExplicitListTy a b c ->
      putByte bh 14 >> put_ bh a >> put_ bh b >> put_ bh c
    HsExplicitTupleTy a b ->
      putByte bh 15 >> put_ bh a >> put_ bh b
    HsTyLit a b ->
      putByte bh 16 >> put_ bh a >> put_ bh b
    HsWildCardTy a ->
      putByte bh 17 >> put_ bh a
    HsDocTy a b c ->
      putByte bh 18 >> put_ bh a >> put_ bh b >> put_ bh c
    HsSpliceTy a b ->
      putByte bh 19 >> put_ bh a >> put_ bh b
    HsStarTy a b ->
      putByte bh 20 >> put_ bh a >> put_ bh b
    XHsType _ ->
      putPanic "XHsType" "HsType"

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> HsForAllTy <$> get bh <*> get bh <*> get bh
      1 -> HsQualTy <$> get bh <*> get bh <*> get bh
      2 -> HsTyVar <$> get bh <*> get bh <*> get bh
      3 -> HsAppTy <$> get bh <*> get bh <*> get bh
      4 -> HsFunTy <$> get bh <*> get bh <*> get bh
      5 -> HsListTy <$> get bh <*> get bh
      6 -> HsTupleTy <$> get bh <*> get bh <*> get bh
      7 -> HsSumTy <$> get bh <*> get bh
      8 -> HsOpTy <$> get bh <*> get bh <*> get bh <*> get bh
      9 -> HsParTy <$> get bh <*> get bh
      10 -> HsIParamTy <$> get bh <*> get bh <*> get bh
      11 -> HsKindSig <$> get bh <*> get bh <*> get bh
      12 -> HsBangTy <$> get bh <*> get bh <*> get bh
      13 -> HsRecTy <$> get bh <*> get bh
      14 -> HsExplicitListTy <$> get bh <*> get bh <*> get bh
      15 -> HsExplicitTupleTy <$> get bh <*> get bh
      16 -> HsTyLit <$> get bh <*> get bh
      17 -> HsWildCardTy <$> get bh
      18 -> HsDocTy <$> get bh <*> get bh <*> get bh
      19 -> HsSpliceTy <$> get bh <*> get bh
      20 -> HsStarTy <$> get bh <*> get bh
      _  -> getPanic "HsType"

instance Binary HsTyLit where
  put_ bh l = case l of
    HsNumTy a b -> putByte bh 0 >> put_ bh a >> put_ bh b
    HsStrTy a b -> putByte bh 1 >> put_ bh a >> put_ bh b
  get bh = do
    tag <- getByte bh
    case tag of
      0 -> HsNumTy <$> get bh <*> get bh
      1 -> HsStrTy <$> get bh <*> get bh
      _ -> getPanic "HsTyLit"

instance Binary a => Binary (HsWildCardBndrs GhcSe a) where
  put_ bh w = case w of
    HsWC a b ->
      putByte bh 0 >> put_ bh a >> put_ bh b
    XHsWildCardBndrs a ->
      putByte bh 1 >> put_ bh a
  get bh = do
    tag <- getByte bh
    case tag of
      0 -> HsWC <$> get bh <*> get bh
      1 -> XHsWildCardBndrs <$> get bh
      _ -> getPanic "HsWildCardBndrs"

instance Binary a => Binary (HsImplicitBndrs GhcSe a) where
  put_ bh b = case b of
    HsIB a b ->
      putByte bh 0 >> put_ bh a >> put_ bh b
    XHsImplicitBndrs a ->
      putByte bh 1 >> put_ bh a
  get bh = do
    tag <- getByte bh
    case tag of
      0 -> HsIB <$> get bh <*> get bh
      1 -> XHsImplicitBndrs <$> get bh
      _ -> getPanic "HsImplicitBndrs"

instance Binary HsTupleSort where
  put_ bh s = putByte bh (case s of
    HsUnboxedTuple -> 0
    HsBoxedTuple -> 1
    HsConstraintTuple -> 2
    HsBoxedOrConstraintTuple -> 3)
  get bh = do
    tag <- getByte bh
    case tag of
      0 -> pure HsUnboxedTuple
      1 -> pure HsBoxedTuple
      2 -> pure HsConstraintTuple
      3 -> pure HsBoxedOrConstraintTuple
      _ -> getPanic "HsTupleSort"

instance Binary (ConDeclField GhcSe) where
  put_ bh f = case f of
    ConDeclField a b c d ->
      putByte bh 0 >> put_ bh a >> put_ bh b >> put_ bh c >> put_ bh d
    XConDeclField a ->
      putByte bh 1 >> put_ bh a

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> ConDeclField <$> get bh <*> get bh <*> get bh <*> get bh
      1 -> XConDeclField <$> get bh
      _ -> getPanic "ConDeclField"

instance Binary (FieldOcc GhcSe) where
  put_ bh o = case o of
    FieldOcc a b ->
      putByte bh 0 >> put_ bh a >> put_ bh b
    XFieldOcc a ->
      putByte bh 1 >> put_ bh a

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> FieldOcc <$> get bh <*> get bh
      1 -> XFieldOcc <$> get bh
      _ -> getPanic "FieldOcc"

instance Binary (HsTyVarBndr GhcSe) where
  put_ bh v = case v of
    UserTyVar a b ->
      putByte bh 0 >> put_ bh a >> put_ bh b
    KindedTyVar a b c ->
      putByte bh 1 >> put_ bh a >> put_ bh b >> put_ bh c
    XTyVarBndr a ->
      putByte bh 2 >> put_ bh a

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> UserTyVar <$> get bh <*> get bh
      1 -> KindedTyVar <$> get bh <*> get bh <*> get bh
      2 -> XTyVarBndr <$> get bh
      _ -> getPanic "HsTyVarBndr"

instance (Binary a, Binary b) => Binary (HsConDetails a b) where
  put_ bh c = case c of
    PrefixCon a -> putByte bh 0 >> put_ bh a
    RecCon a -> putByte bh 1 >> put_ bh a
    InfixCon a b -> putByte bh 2 >> put_ bh a >> put_ bh b
  get bh = do
    tag <- getByte bh
    case tag of
      0 -> PrefixCon <$> get bh
      1 -> RecCon <$> get bh
      2 -> InfixCon <$> get bh <*> get bh
      _ -> getPanic "HsConDetails"

instance Binary (AmbiguousFieldOcc GhcSe) where
  put_ bh o = case o of
    Unambiguous a b ->
      putByte bh 0 >> put_ bh a >> put_ bh b
    Ambiguous a b ->
      putByte bh 1 >> put_ bh a >> put_ bh b
    XAmbiguousFieldOcc a ->
      putByte bh 2 >> put_ bh a

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> Unambiguous <$> get bh <*> get bh
      1 -> Ambiguous <$> get bh <*> get bh
      2 -> XAmbiguousFieldOcc <$> get bh
      _ -> getPanic "AmbiguousOccField"

instance Binary (LHsQTyVars GhcSe) where
  put_ bh v = case v of
    HsQTvs a b ->
      putByte bh 0 >> put_ bh a >> put_ bh b
    XLHsQTyVars a ->
      putByte bh 1 >> put_ bh a

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> HsQTvs <$> get bh <*> get bh
      1 -> XLHsQTyVars <$> get bh
      _ -> getPanic "LHsQTyVars"

instance Binary (Sig GhcSe) where
  put_ bh s = case s of
    TypeSig a b c ->
      putByte bh 0 >> put_ bh a >> put_ bh b >> put_ bh c
    PatSynSig a b c ->
      putByte bh 1 >> put_ bh a >> put_ bh b >> put_ bh c
    ClassOpSig a b c d ->
      putByte bh 2 >> put_ bh a >> put_ bh b >> put_ bh c >> put_ bh d
    IdSig a b ->
      putByte bh 3 >> put_ bh a >> put_ bh b
    FixSig a b ->
      putByte bh 4 >> put_ bh a >> put_ bh b
    InlineSig a b c ->
      putByte bh 5 >> put_ bh a >> put_ bh b >> put_ bh c
    SpecSig a b c d ->
      putByte bh 6 >> put_ bh a >> put_ bh b >> put_ bh c >> put_ bh d
    SpecInstSig a b c ->
      putByte bh 7 >> put_ bh a >> put_ bh b >> put_ bh c
    SCCFunSig a b c d ->
      putByte bh 8 >> put_ bh a >> put_ bh b >> put_ bh c >> put_ bh d
    CompleteMatchSig a b c d ->
      putByte bh 9 >> put_ bh a >> put_ bh b >> put_ bh c >> put_ bh d
    MinimalSig a b c ->
      putByte bh 10 >> put_ bh a >> put_ bh b >> put_ bh c
    XSig a ->
      putByte bh 11 >> put_ bh a

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> TypeSig <$> get bh <*> get bh <*> get bh
      1 -> PatSynSig <$> get bh <*> get bh <*> get bh
      2 -> ClassOpSig <$> get bh <*> get bh <*> get bh <*> get bh
      3 -> IdSig <$> get bh <*> get bh
      4 -> FixSig <$> get bh <*> get bh
      5 -> InlineSig <$> get bh <*> get bh <*> get bh
      6 -> SpecSig <$> get bh <*> get bh <*> get bh <*> get bh
      7 -> SpecInstSig <$> get bh <*> get bh <*> get bh
      8 -> SCCFunSig <$> get bh <*> get bh <*> get bh <*> get bh
      9 -> CompleteMatchSig <$> get bh <*> get bh <*> get bh <*> get bh
      10 -> MinimalSig <$> get bh <*> get bh <*> get bh
      11 -> XSig <$> get bh
      _ -> getPanic "Sig"

instance Binary (FixitySig GhcSe) where
  put_ bh s = case s of
    FixitySig a b c ->
      putByte bh 0 >> put_ bh a >> put_ bh b >> put_ bh c
    XFixitySig a ->
      putByte bh 1 >> put_ bh a

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> FixitySig <$> get bh <*> get bh <*> get bh
      1 -> XFixitySig <$> get bh
      _ -> getPanic "FixitySig"

instance Binary (HsBindLR GhcSe GhcSe) where
  put_ bh b = case b of
    -- TODO: we drop the "fun_co_fn" field, as it seems
    --       to always be WpHole in the places where the binary
    --       serialisation instances will be used.
    -- TODO: we drop the "fun_tick" field, as it is unlikely
    --       to be used in our immediate use cases. Let's
    --       return to parametrising away the 'Id' in that
    --       field's type.
    FunBind a b c d _ -> case d of
      WpHole ->
        putByte bh 0 >> put_ bh a >> put_ bh b >> put_ bh c
      _ ->
        panic "Binary HsBindLR: FunBind with non-WpHole value in fun_co_fn"
    -- TODO: same as for FunBind, we drop pat_ticks
    PatBind a b c _ ->
      putByte bh 1 >> put_ bh a >> put_ bh b >> put_ bh c
    VarBind a b c d ->
      putByte bh 2 >> put_ bh a >> put_ bh b >> put_ bh c >> put_ bh d
    PatSynBind a b ->
      putByte bh 3 >> put_ bh a >> put_ bh b
    XHsBindsLR a ->
      putByte bh 4 >> put_ bh a
    AbsBinds {} -> putPanic "HsBindsLR" "AbsBinds"

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> FunBind <$> get bh <*> get bh <*> get bh <*> pure WpHole <*> pure []
      1 -> PatBind <$> get bh <*> get bh <*> get bh <*> pure ([], [])
      2 -> VarBind <$> get bh <*> get bh <*> get bh <*> get bh
      3 -> PatSynBind <$> get bh <*> get bh
      4 -> XHsBindsLR <$> get bh
      _ -> getPanic "HsBindsLR"

instance Binary (HsLocalBindsLR GhcSe GhcSe) where
  put_ bh b = case b of
    HsValBinds a b    -> putByte bh 0 >> put_ bh a >> put_ bh b
    EmptyLocalBinds a -> putByte bh 1 >> put_ bh a
    XHsLocalBindsLR a -> putByte bh 2 >> put_ bh a
    HsIPBinds {}      -> putPanic "HsLocalBindsLR" "HsIPBinds"
  get bh = do
    tag <- getByte bh
    case tag of
      0 -> HsValBinds <$> get bh <*> get bh
      1 -> EmptyLocalBinds <$> get bh
      2 -> XHsLocalBindsLR <$> get bh
      _ -> getPanic "HsLocalBindsLR"

instance Binary (HsValBindsLR GhcSe GhcSe) where
  put_ bh b = case b of
    ValBinds a b c -> putByte bh 0 >> put_ bh a >> put_ bh b >> put_ bh c
    XValBindsLR {} -> putPanic "HsValBindsLR" "ValBindsOut"

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> ValBinds <$> get bh <*> get bh <*> get bh
      _ -> getPanic "HsValBindsLR"

instance Binary (PatSynBind GhcSe GhcSe) where
  put_ bh b = case b of
    PSB a b c d e ->
      putByte bh 0 >> put_ bh a >> put_ bh b >> put_ bh c >> put_ bh d
                   >> put_ bh e
    XPatSynBind a ->
      putByte bh 1 >> put_ bh a

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> PSB <$> get bh <*> get bh <*> get bh <*> get bh <*> get bh
      1 -> XPatSynBind <$> get bh
      _ -> getPanic "PatSynBind"

instance Binary (HsPatSynDir GhcSe) where
  put_ bh d = case d of
    Unidirectional -> putByte bh 0
    ImplicitBidirectional -> putByte bh 1
    ExplicitBidirectional a -> putByte bh 2 >> put_ bh a
  get bh = do
    tag <- getByte bh
    case tag of
      0 -> pure Unidirectional
      1 -> pure ImplicitBidirectional
      2 -> ExplicitBidirectional <$> get bh
      _ -> getPanic "HsPatSynDir"

instance Binary a => Binary (RecordPatSynField a) where
  put_ bh (RecordPatSynField a b) = put_ bh a >> put_ bh b
  get bh = RecordPatSynField <$> get bh <*> get bh

instance Binary (IPBind GhcSe) where
  put_ bh i = case i of
    IPBind a b c -> putByte bh 0 >> put_ bh a >> put_ bh b >> put_ bh c
    XIPBind a -> putByte bh 1 >> put_ bh a

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> IPBind <$> get bh <*> get bh <*> get bh
      1 -> XIPBind <$> get bh
      _ -> getPanic "IPBind"

-- * HsDecls

instance Binary (HsDecl GhcSe) where
  put_ bh d = case d of
    TyClD a b      -> putByte bh 0 >> put_ bh a >> put_ bh b
    InstD a b      -> putByte bh 1 >> put_ bh a >> put_ bh b
    DerivD a b     -> putByte bh 2 >> put_ bh a >> put_ bh b
    ValD a b       -> putByte bh 3 >> put_ bh a >> put_ bh b
    SigD a b       -> putByte bh 4 >> put_ bh a >> put_ bh b
    DefD a b       -> putByte bh 5 >> put_ bh a >> put_ bh b
    ForD a b       -> putByte bh 6 >> put_ bh a >> put_ bh b
    WarningD a b   -> putByte bh 7 >> put_ bh a >> put_ bh b
    RoleAnnotD a b -> putByte bh 8 >> put_ bh a >> put_ bh b
    RuleD a b      -> putByte bh 9 >> put_ bh a >> put_ bh b
    AnnD a b       -> putByte bh 10 >> put_ bh a >> put_ bh b
    SpliceD a b    -> putByte bh 11 >> put_ bh a >> put_ bh b
    DocD a b       -> putByte bh 12 >> put_ bh a >> put_ bh b
    XHsDecl a      -> putByte bh 13 >> put_ bh a

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> TyClD <$> get bh <*> get bh
      1 -> InstD <$> get bh <*> get bh
      2 -> DerivD <$> get bh <*> get bh
      3 -> ValD <$> get bh <*> get bh
      4 -> SigD <$> get bh <*> get bh
      5 -> DefD <$> get bh <*> get bh
      6 -> ForD <$> get bh <*> get bh
      7 -> WarningD <$> get bh <*> get bh
      8 -> RoleAnnotD <$> get bh <*> get bh
      9 -> RuleD <$> get bh <*> get bh
      10 -> AnnD <$> get bh <*> get bh
      11 -> SpliceD <$> get bh <*> get bh
      12 -> DocD <$> get bh <*> get bh
      13 -> XHsDecl <$> get bh
      _ -> getPanic "HsDecl"

instance Binary (ForeignDecl GhcSe) where
  put_ bh d = case d of
    ForeignImport a b c d ->
      putByte bh 0 >> put_ bh a >> put_ bh b >> put_ bh c
                   >> put_ bh d
    ForeignExport a b c d ->
      putByte bh 1 >> put_ bh a >> put_ bh b >> put_ bh c
                   >> put_ bh d
    XForeignDecl a ->
      putByte bh 2 >> put_ bh a

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> ForeignImport <$> get bh <*> get bh <*> get bh <*> get bh
      1 -> ForeignExport <$> get bh <*> get bh <*> get bh <*> get bh
      2 -> XForeignDecl <$> get bh
      _ -> getPanic "ForeignDecl"

instance Binary (DefaultDecl GhcSe) where
  put_ bh d = case d of
    DefaultDecl a b -> putByte bh 0 >> put_ bh a >> put_ bh b
    XDefaultDecl a -> putByte bh 1 >> put_ bh a

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> DefaultDecl <$> get bh <*> get bh
      1 -> XDefaultDecl <$> get bh
      _ -> getPanic "DefaultDecl"

instance Binary (TyClDecl GhcSe) where
  put_ bh d = case d of
    FamDecl a b ->
      putByte bh 0 >> put_ bh a >> put_ bh b
    SynDecl a b c d e ->
      putByte bh 1 >> put_ bh a >> put_ bh b >> put_ bh c
                   >> put_ bh d >> put_ bh e
    DataDecl a b c d e ->
      putByte bh 2 >> put_ bh a >> put_ bh b >> put_ bh c
                   >> put_ bh d >> put_ bh e
    ClassDecl a b c d e f g h i j k ->
      putByte bh 3 >> put_ bh a >> put_ bh b >> put_ bh c
                   >> put_ bh d >> put_ bh e >> put_ bh f
                   >> put_ bh g >> put_ bh h >> put_ bh i
                   >> put_ bh j >> put_ bh k
    XTyClDecl a ->
      putByte bh 4 >> put_ bh a

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> FamDecl <$> get bh <*> get bh
      1 -> SynDecl <$> get bh <*> get bh <*> get bh <*> get bh <*> get bh
      2 -> DataDecl <$> get bh <*> get bh <*> get bh <*> get bh <*> get bh
      3 -> ClassDecl <$> get bh <*> get bh <*> get bh <*> get bh <*> get bh
                     <*> get bh <*> get bh <*> get bh <*> get bh <*> get bh
                     <*> get bh
      4 -> XTyClDecl <$> get bh
      _ -> getPanic "TyClDecl"

instance Binary DocDecl where
  put_ bh d = case d of
    DocCommentNext a    -> putByte bh 0 >> put_ bh a
    DocCommentPrev a    -> putByte bh 1 >> put_ bh a
    DocCommentNamed a b -> putByte bh 2 >> put_ bh a >> put_ bh b
    DocGroup a b        -> putByte bh 3 >> put_ bh a >> put_ bh b
  get bh = do
    tag <- getByte bh
    case tag of
      0 -> DocCommentNext <$> get bh
      1 -> DocCommentPrev <$> get bh
      2 -> DocCommentNamed <$> get bh <*> get bh
      3 -> DocGroup <$> get bh <*> get bh
      _ -> getPanic "DocDecl"

instance Binary (WarnDecls GhcSe) where
  put_ bh d = case d of
    Warnings a b c -> putByte bh 0 >> put_ bh a >> put_ bh b >> put_ bh c
    XWarnDecls a   -> putByte bh 1 >> put_ bh a

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> Warnings <$> get bh <*> get bh <*> get bh
      1 -> XWarnDecls <$> get bh
      _ -> getPanic "WarnDecls"

instance Binary (WarnDecl GhcSe) where
  put_ bh d = case d of
    Warning a b c -> putByte bh 0 >> put_ bh a >> put_ bh b >> put_ bh c
    XWarnDecl a   -> putByte bh 1 >> put_ bh a
  get bh = do
    tag <- getByte bh
    case tag of
      0 -> Warning <$> get bh <*> get bh <*> get bh
      1 -> XWarnDecl <$> get bh
      _ -> getPanic "WarnDecl"

instance Binary (RoleAnnotDecl GhcSe) where
  put_ bh d = case d of
    RoleAnnotDecl a b c -> putByte bh 0 >> put_ bh a >> put_ bh b >> put_ bh c
    XRoleAnnotDecl a    -> putByte bh 1 >> put_ bh a
  get bh = do
    tag <- getByte bh
    case tag of
      0 -> RoleAnnotDecl <$> get bh <*> get bh <*> get bh
      1 -> XRoleAnnotDecl <$> get bh
      _ -> getPanic "RoleAnnotDecl"

instance Binary (RuleDecls GhcSe) where
  put_ bh d = case d of
    HsRules a b c -> putByte bh 0 >> put_ bh a >> put_ bh b >> put_ bh c
    XRuleDecls a  -> putByte bh 1 >> put_ bh a
  get bh = do
    tag <- getByte bh
    case tag of
      0 -> HsRules <$> get bh <*> get bh <*> get bh
      1 -> XRuleDecls <$> get bh
      _ -> getPanic "RuleDecls"

instance Binary (RuleDecl GhcSe) where
  put_ bh decl = case decl of
    HsRule a b c d e f ->
      putByte bh 0 >> put_ bh a >> put_ bh b >> put_ bh c >> put_ bh d
                   >> put_ bh e >> put_ bh f
    XRuleDecl a ->
      putByte bh 1 >> put_ bh a

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> HsRule <$> get bh <*> get bh <*> get bh <*> get bh
                  <*> get bh <*> get bh
      1 -> XRuleDecl <$> get bh
      _ -> getPanic "RuleDecl"

instance Binary (AnnDecl GhcSe) where
  put_ bh decl = case decl of
    HsAnnotation a b c d ->
      putByte bh 0 >> put_ bh a >> put_ bh b >> put_ bh c >> put_ bh d
    XAnnDecl a ->
      putByte bh 1 >> put_ bh a

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> HsAnnotation <$> get bh <*> get bh <*> get bh <*> get bh
      1 -> XAnnDecl <$> get bh
      _ -> getPanic "AnnDecl"

instance Binary (SpliceDecl GhcSe) where
  put_ bh d = case d of
    SpliceDecl a b c -> putByte bh 0 >> put_ bh a >> put_ bh b >> put_ bh c
    XSpliceDecl a    -> putByte bh 1 >> put_ bh a

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> SpliceDecl <$> get bh <*> get bh <*> get bh
      1 -> XSpliceDecl <$> get bh
      _ -> getPanic "SpliceDecl"

instance Binary a => Binary (Tickish a) where
  put_ bh t = case t of
    ProfNote a b c ->
      putByte bh 0 >> put_ bh a >> put_ bh b >> put_ bh c
    HpcTick a b ->
      putByte bh 1 >> put_ bh a >> put_ bh b
    Breakpoint a b ->
      putByte bh 2 >> put_ bh a >> put_ bh b
    SourceNote a b ->
      putByte bh 3 >> put_ bh a >> put_ bh b
  get bh = do
    tag <- getByte bh
    case tag of
      0 -> ProfNote <$> get bh <*> get bh <*> get bh
      1 -> HpcTick <$> get bh <*> get bh
      2 -> Breakpoint <$> get bh <*> get bh
      3 -> SourceNote <$> get bh <*> get bh
      _ -> getPanic "Tickish"

instance Binary SpliceExplicitFlag where
  put_ bh f = putByte bh $ case f of
    ExplicitSplice -> 0
    ImplicitSplice -> 1
  get bh = do
    tag <- getByte bh
    case tag of
      0 -> pure ExplicitSplice
      1 -> pure ImplicitSplice
      _ -> getPanic "SpliceExplicitFlag"

instance Binary SpliceDecoration where
  put_ bh d = putByte bh $ case d of
    HasParens -> 0
    HasDollar -> 1
    NoParens  -> 2
  get bh = do
    tag <- getByte bh
    case tag of
      0 -> pure HasParens
      1 -> pure HasDollar
      2 -> pure NoParens
      _ -> getPanic "SpliceDecoration"

instance Binary (HsSplice GhcSe) where
  put_ bh s = case s of
    HsTypedSplice a b c d ->
      putByte bh 0 >> put_ bh a >> put_ bh b >> put_ bh c >> put_ bh d
    HsUntypedSplice a b c d ->
      putByte bh 1 >> put_ bh a >> put_ bh b >> put_ bh c >> put_ bh d
    HsQuasiQuote a b c d e ->
      putByte bh 2 >> put_ bh a >> put_ bh b >> put_ bh c >> put_ bh d
                   >> put_ bh e
    XSplice a ->
      putByte bh 3 >> put_ bh a
    HsSpliced {} -> putPanic "HsSplice" "HsSpliced"

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> HsTypedSplice <$> get bh <*> get bh <*> get bh <*> get bh
      1 -> HsUntypedSplice <$> get bh <*> get bh <*> get bh <*> get bh
      2 -> HsQuasiQuote <$> get bh <*> get bh <*> get bh <*> get bh
                        <*> get bh
      3 -> XSplice <$> get bh
      _ -> getPanic "HsSplice"

instance Binary (AnnProvenance SeName) where
  put_ bh p = case p of
    ValueAnnProvenance a -> putByte bh 0 >> put_ bh a
    TypeAnnProvenance a -> putByte bh 1 >> put_ bh a
    ModuleAnnProvenance -> putByte bh 2
  get bh = do
    tag <- getByte bh
    case tag of
      0 -> ValueAnnProvenance <$> get bh
      1 -> TypeAnnProvenance <$> get bh
      2 -> pure ModuleAnnProvenance
      _ -> getPanic "AnnProvenance"

instance Binary ForeignImport where
  put_ bh (CImport a b c d e) =
    put_ bh a >> put_ bh b >> put_ bh c >> put_ bh d
              >> put_ bh e
  get bh = CImport <$> get bh <*> get bh <*> get bh
                   <*> get bh <*> get bh

instance Binary CImportSpec where
  put_ bh s = case s of
    CLabel a -> putByte bh 0 >> put_ bh a
    CFunction a -> putByte bh 1 >> put_ bh a
    CWrapper -> putByte bh 2
  get bh = do
    tag <- getByte bh
    case tag of
      0 -> CLabel <$> get bh
      1 -> CFunction <$> get bh
      2 -> pure CWrapper
      _ -> getPanic "CImportSpec"

instance Binary ForeignExport where
  put_ bh (CExport a b) = put_ bh a >> put_ bh b
  get bh = CExport <$> get bh <*> get bh

instance Binary (RuleBndr GhcSe) where
  put_ bh b = case b of
    RuleBndr a b ->
      putByte bh 0 >> put_ bh a >> put_ bh b
    RuleBndrSig a b c ->
      putByte bh 1 >> put_ bh a >> put_ bh b >> put_ bh c
    XRuleBndr a ->
      putByte bh 2 >> put_ bh a
  get bh = do
    tag <- getByte bh
    case tag of
      0 -> RuleBndr <$> get bh <*> get bh
      1 -> RuleBndrSig <$> get bh <*> get bh <*> get bh
      2 -> XRuleBndr <$> get bh
      _ -> getPanic "RuleBndr"

instance (Binary a, Binary b) => Binary (FamEqn GhcSe a b) where
  put_ bh e = case e of
    FamEqn a b c d e ->
      putByte bh 0 >> put_ bh a >> put_ bh b >> put_ bh c >> put_ bh d
                   >> put_ bh e
    XFamEqn a ->
      putByte bh 1 >> put_ bh a

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> FamEqn <$> get bh <*> get bh <*> get bh <*> get bh
                  <*> get bh
      1 -> XFamEqn <$> get bh
      _ -> getPanic "FamEqn"

instance Binary (HsDataDefn GhcSe) where
  put_ bh d = case d of
    HsDataDefn a b c d e f g ->
      putByte bh 0 >> put_ bh a >> put_ bh b >> put_ bh c >> put_ bh d
                   >> put_ bh e >> put_ bh f >> put_ bh g
    XHsDataDefn a ->
      putByte bh 1 >> put_ bh a

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> HsDataDefn <$> get bh <*> get bh <*> get bh <*> get bh
                      <*> get bh <*> get bh <*> get bh
      1 -> XHsDataDefn <$> get bh
      _ -> getPanic "HsDataDefn"

instance Binary NewOrData where
  put_ bh a = putByte bh (case a of
    NewType  -> 0
    DataType -> 1)
  get bh = getByte bh >>= \b -> case b of
    0 -> pure NewType
    1 -> pure DataType
    _ -> getPanic "NewOrData"

instance Binary (HsDerivingClause GhcSe) where
  put_ bh c = case c of
    HsDerivingClause a b c ->
      putByte bh 0 >> put_ bh a >> put_ bh b >> put_ bh c
    XHsDerivingClause a ->
      putByte bh 1 >> put_ bh a

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> HsDerivingClause <$> get bh <*> get bh <*> get bh
      1 -> XHsDerivingClause <$> get bh
      _ -> getPanic "HsDerivingClause"

instance Binary (ConDecl GhcSe) where
  put_ bh d = case d of
    ConDeclGADT a b c d e f g h ->
      putByte bh 0 >> put_ bh a >> put_ bh b >> put_ bh c >> put_ bh d
                   >> put_ bh e >> put_ bh f >> put_ bh g >> put_ bh h
    ConDeclH98 a b c d e f g ->
      putByte bh 1 >> put_ bh a >> put_ bh b >> put_ bh c >> put_ bh d
                   >> put_ bh e >> put_ bh f >> put_ bh g
    XConDecl a ->
      putByte bh 2 >> put_ bh a

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> ConDeclGADT <$> get bh <*> get bh <*> get bh <*> get bh
                       <*> get bh <*> get bh <*> get bh <*> get bh
      1 -> ConDeclH98 <$> get bh <*> get bh <*> get bh <*> get bh
                      <*> get bh <*> get bh <*> get bh
      2 -> XConDecl <$> get bh
      _ -> getPanic "ConDecl"


instance Binary (FamilyDecl GhcSe) where
  put_ bh d = case d of
    FamilyDecl a b c d e f g ->
      putByte bh 0 >> put_ bh a >> put_ bh b >> put_ bh c >> put_ bh d
                   >> put_ bh e >> put_ bh f >> put_ bh g
    XFamilyDecl a ->
      putByte bh 1 >> put_ bh a

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> FamilyDecl <$> get bh <*> get bh <*> get bh <*> get bh
                      <*> get bh <*> get bh <*> get bh
      1 -> XFamilyDecl <$> get bh
      _ -> getPanic "FamilyDecl"

instance Binary (InjectivityAnn GhcSe) where
  put_ bh a = case a of
    InjectivityAnn a b -> put_ bh a >> put_ bh b
  get bh = InjectivityAnn <$> get bh <*> get bh

instance Binary (FamilyInfo GhcSe) where
  put_ bh i = case i of
    DataFamily ->
      putByte bh 0
    OpenTypeFamily ->
      putByte bh 1
    ClosedTypeFamily a ->
      putByte bh 2 >> put_ bh a

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> pure DataFamily
      1 -> pure OpenTypeFamily
      2 -> ClosedTypeFamily <$> get bh
      _ -> getPanic "FamilyInfo"

instance Binary (FamilyResultSig GhcSe) where
  put_ bh s = case s of
    NoSig a ->
      putByte bh 0 >> put_ bh a
    KindSig a b ->
      putByte bh 1 >> put_ bh a >> put_ bh b
    TyVarSig a b ->
      putByte bh 2 >> put_ bh a >> put_ bh b
    XFamilyResultSig a ->
      putByte bh 3 >> put_ bh a

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> NoSig <$> get bh
      1 -> KindSig <$> get bh <*> get bh
      2 -> TyVarSig <$> get bh <*> get bh
      3 -> XFamilyResultSig <$> get bh
      _ -> getPanic "FamilyResultSig"

instance Binary (InstDecl GhcSe) where
  put_ bh d = case d of
    ClsInstD a b ->
      putByte bh 0 >> put_ bh a >> put_ bh b
    DataFamInstD a b ->
      putByte bh 1 >> put_ bh a >> put_ bh b
    TyFamInstD a b ->
      putByte bh 2 >> put_ bh a >> put_ bh b
    XInstDecl a ->
      putByte bh 3 >> put_ bh a

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> ClsInstD <$> get bh <*> get bh
      1 -> DataFamInstD <$> get bh <*> get bh
      2 -> TyFamInstD <$> get bh <*> get bh
      3 -> XInstDecl <$> get bh
      _ -> getPanic "InstDecl"

instance Binary (ClsInstDecl GhcSe) where
  put_ bh d = case d of
    ClsInstDecl a b c d e f g ->
      putByte bh 0 >> put_ bh a >> put_ bh b >> put_ bh c >> put_ bh d
                   >> put_ bh e >> put_ bh f >> put_ bh g
    XClsInstDecl a ->
      putByte bh 1 >> put_ bh a

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> ClsInstDecl <$> get bh <*> get bh <*> get bh <*> get bh
                       <*> get bh <*> get bh <*> get bh
      1 -> XClsInstDecl <$> get bh
      _ -> getPanic "ClsInstDecl"

instance Binary (DataFamInstDecl GhcSe) where
  put_ bh (DataFamInstDecl a) = put_ bh a
  get bh = DataFamInstDecl <$> get bh

instance Binary (TyFamInstDecl GhcSe) where
  put_ bh (TyFamInstDecl a) = put_ bh a
  get bh = TyFamInstDecl <$> get bh

instance Binary (DerivDecl GhcSe) where
  put_ bh d = case d of
    DerivDecl a b c d ->
      putByte bh 0 >> put_ bh a >> put_ bh b >> put_ bh c >> put_ bh d
    XDerivDecl a ->
      putByte bh 1 >> put_ bh a

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> DerivDecl <$> get bh <*> get bh <*> get bh <*> get bh
      1 -> XDerivDecl <$> get bh
      _ -> getPanic "DerivDecl"

instance Binary (DerivStrategy GhcSe) where
  put_ bh s = case s of
    StockStrategy    -> putByte bh 0
    AnyclassStrategy -> putByte bh 1
    NewtypeStrategy  -> putByte bh 2
    ViaStrategy a    -> putByte bh 3 >> put_ bh a
  get bh = do
    tag <- getByte bh
    case tag of
      0 -> pure StockStrategy
      1 -> pure AnyclassStrategy
      2 -> pure NewtypeStrategy
      3 -> ViaStrategy <$> get bh
      _ -> getPanic "DerivStrategy"

instance Binary HsSrcBang where
  put_ bh (HsSrcBang a b c) =
    put_ bh a >> put_ bh b >> put_ bh c
  get bh = HsSrcBang <$> get bh <*> get bh <*> get bh

instance Binary RdrName where
  put_ bh n = case n of
    Unqual a -> putByte bh 0 >> put_ bh a
    Qual a b -> putByte bh 1 >> put_ bh a >> put_ bh b
    Orig a b -> putByte bh 2 >> put_ bh a >> put_ bh b
    Exact a
      | isExternalName a -> putByte bh 3 >> put_ bh a
      | otherwise -> putByte bh (if isSystemName a then 4 else 5)
          >> put_ bh (nameUnique a) >> put_ bh (nameOccName a)
          >> put_ bh (nameSrcSpan a)
  get bh = do
    tag <- getByte bh
    case tag of
      0 -> Unqual <$> get bh
      1 -> Qual <$> get bh <*> get bh
      2 -> Orig <$> get bh <*> get bh
      3 -> Exact <$> get bh
      4 -> fmap Exact (mkSystemNameAt <$> get bh <*> get bh <*> get bh)
      5 -> fmap Exact (mkInternalName <$> get bh <*> get bh <*> get bh)
      _ -> getPanic "RdrName"

-- * HsLit

instance Binary (HsLit GhcSe) where
  put_ bh lit
    = case lit of
        HsChar a b       -> putByte bh 0  >> put_ bh a >> put_ bh b
        HsCharPrim a b   -> putByte bh 1  >> put_ bh a >> put_ bh b
        HsString a b     -> putByte bh 2  >> put_ bh a >> put_ bh b
        HsStringPrim a b -> putByte bh 3  >> put_ bh a >> put_ bh b
        HsInt a b        -> putByte bh 4  >> put_ bh a >> put_ bh b
        HsIntPrim a b    -> putByte bh 5  >> put_ bh a >> put_ bh b
        HsWordPrim a b   -> putByte bh 6  >> put_ bh a >> put_ bh b
        HsInt64Prim a b  -> putByte bh 7  >> put_ bh a >> put_ bh b
        HsWord64Prim a b -> putByte bh 8  >> put_ bh a >> put_ bh b
        HsInteger a b c  -> putByte bh 9  >> put_ bh a >> put_ bh b >> put_ bh c
        HsRat a b c      -> putByte bh 10 >> put_ bh a >> put_ bh b >> put_ bh c
        HsFloatPrim a b  -> putByte bh 11 >> put_ bh a >> put_ bh b
        HsDoublePrim a b -> putByte bh 12 >> put_ bh a >> put_ bh b
        XLit a           -> putByte bh 13 >> put_ bh a

  get bh = do
    tag <- getByte bh
    case tag of
      0  -> HsChar       <$> get bh <*> get bh
      1  -> HsCharPrim   <$> get bh <*> get bh
      2  -> HsString     <$> get bh <*> get bh
      3  -> HsStringPrim <$> get bh <*> get bh
      4  -> HsInt        <$> get bh <*> get bh
      5  -> HsIntPrim    <$> get bh <*> get bh
      6  -> HsWordPrim   <$> get bh <*> get bh
      7  -> HsInt64Prim  <$> get bh <*> get bh
      8  -> HsWord64Prim <$> get bh <*> get bh
      9  -> HsInteger    <$> get bh <*> get bh <*> get bh
      10 -> HsRat        <$> get bh <*> get bh <*> get bh
      11 -> HsFloatPrim  <$> get bh <*> get bh
      12 -> HsDoublePrim <$> get bh <*> get bh
      13 -> XLit         <$> get bh
      _ -> getPanic "HsLit"

instance Binary (HsOverLit GhcSe) where
  put_ bh lit = case lit of
    OverLit a b c -> putByte bh 0 >> put_ bh a >> put_ bh b >> put_ bh c
    XOverLit a    -> putByte bh 1 >> put_ bh a

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> OverLit <$> get bh <*> get bh <*> get bh
      1 -> XOverLit <$> get bh
      _ -> getPanic "HsOverLit"

instance Binary Promoted where
  get bh = getByte bh >>= \tag -> case tag of
    0 -> pure Promoted
    1 -> pure NotPromoted
    _ -> getPanic "Promoted"

  put_ bh p = putByte bh $ case p of
    Promoted -> 0
    NotPromoted -> 1

instance Binary RealSrcLoc where
  put_ bh l = do
    put_ bh (srcLocFile l)
    put_ bh (srcLocLine l)
    put_ bh (srcLocCol l)

  get bh = mkRealSrcLoc <$> get bh <*> get bh <*> get bh

instance Binary RealSrcSpan where
  put_ bh s = put_ bh (realSrcSpanStart s) >> put_ bh (realSrcSpanEnd s)

  get bh = do
    loc1 <- get bh
    loc2 <- get bh
    return (mkRealSrcSpan loc1 loc2)

instance Binary OverLitVal where
  put_ bh v
    = case v of
        HsIntegral a   -> putByte bh 0 >> put_ bh a
        HsFractional a -> putByte bh 1 >> put_ bh a
        HsIsString a b -> putByte bh 2 >> put_ bh a >> put_ bh b
  get bh = do
    tag <- getByte bh
    case tag of
      0 -> HsIntegral <$> get bh
      1 -> HsFractional <$> get bh
      2 -> HsIsString <$> get bh <*> get bh
      _ -> getPanic "OverLitVal"
