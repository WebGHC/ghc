{-# LANGUAGE GADTs #-}
module HsExprBin_ConversionSE2PS where

import Control.Applicative
import Data.Traversable

import Bag (mapBagM)
import Class
import CoreSyn ( Tickish(..) )
import GhcPrelude
import HsBinds
import HsDecls
import HsExpr
import HsExprBin_Conversions
import HsExtension
import HsLit
import HsPat
import HsTypes

-- * Conversion from serialisable ASTs to parsed ASTs

cvLHsDecl :: LHsDecl GhcSe -> Conv (LHsDecl GhcPs)
cvLHsDecl = traverse cvHsDecl

cvHsDecl :: HsDecl GhcSe -> Conv (HsDecl GhcPs)
cvHsDecl (TyClD a b) = TyClD <$> pure a <*> cvTyClDecl b
cvHsDecl (InstD a b) = InstD <$> pure a <*> cvInstDecl b
cvHsDecl (DerivD a b) = DerivD <$> pure a <*> cvDerivDecl b
cvHsDecl (ValD a b) = ValD <$> pure a <*> cvHsBindLR b
cvHsDecl (SigD a b) = SigD <$> pure a <*> cvSig b
cvHsDecl (DefD a b) = DefD <$> pure a <*> cvDefaultDecl b
cvHsDecl (ForD a b) = ForD <$> pure a <*> cvForeignDecl b
cvHsDecl (WarningD a b) = WarningD <$> pure a <*> cvWarningDecls b
cvHsDecl (RoleAnnotD a b) = RoleAnnotD <$> pure a <*> cvRoleAnnotDecl b
cvHsDecl (AnnD a b) = AnnD <$> pure a <*> cvAnnDecl b
cvHsDecl (RuleD a b) = RuleD <$> pure a <*> cvRuleDecls b
cvHsDecl (SpliceD a b) = SpliceD <$> pure a <*> cvSpliceDecl b
cvHsDecl (DocD a b) = pure (DocD a b)
cvHsDecl (XHsDecl a) = pure (XHsDecl a)

cvAnnDecl :: AnnDecl GhcSe -> Conv (AnnDecl GhcPs)
cvAnnDecl (HsAnnotation a b c d) =
  HsAnnotation a b <$> cvAnnProvenance c <*> cvLHsExpr d
cvAnnDecl (XAnnDecl a) = pure (XAnnDecl a)

cvInstDecl :: InstDecl GhcSe -> Conv (InstDecl GhcPs)
cvInstDecl (ClsInstD a b) = ClsInstD a <$> cvClsInstDecl b
cvInstDecl (DataFamInstD a b) = DataFamInstD a <$> cvDataFamInstDecl b
cvInstDecl (TyFamInstD a b) = TyFamInstD a <$> cvTyFamInstDecl b
cvInstDecl (XInstDecl a) = pure (XInstDecl a)

cvClsInstDecl :: ClsInstDecl GhcSe -> Conv (ClsInstDecl GhcPs)
cvClsInstDecl (ClsInstDecl a b c d e f g) =
  ClsInstDecl a
    <$> cvHsImplicitBndrs (traverse cvType) b
    <*> mapBagM (traverse cvHsBindLR) c
    <*> traverse (traverse cvSig) d
    <*> traverse (traverse cvTyFamInstDecl) e
    <*> traverse (traverse cvDataFamInstDecl) f
    <*> pure g
cvClsInstDecl (XClsInstDecl a) = pure (XClsInstDecl a)

cvDerivDecl :: DerivDecl GhcSe -> Conv (DerivDecl GhcPs)
cvDerivDecl (DerivDecl a b c d) =
  DerivDecl a <$> cvHsWildCardBndrs (cvHsImplicitBndrs $ traverse cvType) b
              <*> traverse (traverse cvDerivStrategy) c
              <*> pure d
cvDerivDecl (XDerivDecl a) = pure (XDerivDecl a)

cvDerivStrategy
  :: DerivStrategy GhcSe -> Conv (DerivStrategy GhcPs)
cvDerivStrategy StockStrategy = pure StockStrategy
cvDerivStrategy AnyclassStrategy = pure AnyclassStrategy
cvDerivStrategy NewtypeStrategy = pure NewtypeStrategy
cvDerivStrategy (ViaStrategy a) = ViaStrategy
  <$> cvHsImplicitBndrs (traverse cvType) a

cvTyClDecl :: TyClDecl GhcSe -> Conv (TyClDecl GhcPs)
cvTyClDecl (FamDecl a b) = FamDecl <$> pure a <*> cvFamilyDecl b
cvTyClDecl (SynDecl a b c d e) =
  SynDecl a
    <$> convertName b
    <*> cvLHsQTyVars c <*> pure d
    <*> traverse cvType e
cvTyClDecl (DataDecl a b c d e) =
  DataDecl a
    <$> convertName b
    <*> cvLHsQTyVars c <*> pure d
    <*> cvHsDataDefn e
cvTyClDecl (ClassDecl a b c d e f g h i j k) =
  ClassDecl a
    <$> traverse (traverse (traverse cvType)) b
    <*> convertName c
    <*> cvLHsQTyVars d
    <*> pure e
    <*> traverse (traverse cvFunDep) f
    <*> traverse (traverse cvSig) g
    <*> mapBagM (traverse cvHsBindLR) h
    <*> traverse (traverse cvFamilyDecl) i
    <*> traverse (traverse $ cvFamEqn cvLHsQTyVars (traverse cvType)) j
    <*> pure k
cvTyClDecl (XTyClDecl a) = pure (XTyClDecl a)

cvRoleAnnotDecl :: RoleAnnotDecl GhcSe -> Conv (RoleAnnotDecl GhcPs)
cvRoleAnnotDecl (RoleAnnotDecl a b c) =
  RoleAnnotDecl a <$> convertName b <*> pure c
cvRoleAnnotDecl (XRoleAnnotDecl a) = pure (XRoleAnnotDecl a)

cvRuleDecls :: RuleDecls GhcSe -> Conv (RuleDecls GhcPs)
cvRuleDecls (HsRules a b c) = HsRules a b <$> traverse (traverse cvRuleDecl) c
cvRuleDecls (XRuleDecls a) = pure (XRuleDecls a)

cvRuleDecl :: RuleDecl GhcSe -> Conv (RuleDecl GhcPs)
cvRuleDecl (HsRule a b c d e f) =
  HsRule a b c <$> traverse (traverse cvRuleBndr) d
               <*> cvLHsExpr e <*> cvLHsExpr f
cvRuleDecl (XRuleDecl a) = pure (XRuleDecl a)

cvSpliceDecl :: SpliceDecl GhcSe -> Conv (SpliceDecl GhcPs)
cvSpliceDecl (SpliceDecl a b c) =
  SpliceDecl a <$> traverse cvHsSplice b <*> pure c
cvSpliceDecl (XSpliceDecl a) = pure (XSpliceDecl a)

cvHsSplice :: HsSplice GhcSe -> Conv (HsSplice GhcPs)
cvHsSplice (HsTypedSplice a b c d) =
  HsTypedSplice a b <$> convertName c <*> cvLHsExpr d
cvHsSplice (HsUntypedSplice a b c d) =
  HsUntypedSplice a b <$> convertName c <*> cvLHsExpr d
cvHsSplice (HsQuasiQuote a b c d e) =
  HsQuasiQuote a <$> convertName b <*> convertName c <*> pure d <*> pure e
cvHsSplice (HsSpliced {}) =
  unsupported "HsSpliced" "HsSplice" (error "<not printable>")
cvHsSplice (XSplice a) = pure (XSplice a)

cvRuleBndr :: RuleBndr GhcSe -> Conv (RuleBndr GhcPs)
cvRuleBndr (RuleBndr a b) = RuleBndr a <$> convertName b
cvRuleBndr (RuleBndrSig a b c) =
  RuleBndrSig a <$> convertName b <*> cvHsSigWcType c
cvRuleBndr (XRuleBndr a) = pure (XRuleBndr a)

cvFamEqn
  :: ( XCFamEqn GhcSe a b ~ XCFamEqn GhcPs c d
     , XXFamEqn GhcSe a b ~ XXFamEqn GhcPs c d
     )
  => (a -> Conv c)
  -> (b -> Conv d)
  -> FamEqn GhcSe a b
  -> Conv (FamEqn GhcPs c d)
cvFamEqn goPats goRhs (FamEqn a b c d e) =
  FamEqn a <$> convertName b <*> goPats c <*> pure d <*> goRhs e
cvFamEqn _ _ (XFamEqn a) = pure (XFamEqn a)

cvFamilyDecl :: FamilyDecl GhcSe -> Conv (FamilyDecl GhcPs)
cvFamilyDecl (FamilyDecl a b c d e f g) =
  FamilyDecl a
    <$> cvFamilyInfo b <*> convertName c
    <*> cvLHsQTyVars d <*> pure e
    <*> traverse cvFamilyResultSig f
    <*> traverse (traverse cvInjectivityAnn) g
cvFamilyDecl (XFamilyDecl a) = pure (XFamilyDecl a)

cvAnnProvenance :: ConvertName a b => AnnProvenance a -> Conv (AnnProvenance b)
cvAnnProvenance (ValueAnnProvenance a) = ValueAnnProvenance <$> convertName a
cvAnnProvenance (TypeAnnProvenance a) = TypeAnnProvenance <$> convertName a
cvAnnProvenance ModuleAnnProvenance = pure ModuleAnnProvenance

cvInjectivityAnn
  :: InjectivityAnn GhcSe -> Conv (InjectivityAnn GhcPs)
cvInjectivityAnn (InjectivityAnn a b) =
  InjectivityAnn <$> convertName a <*> convertName b

cvFamilyResultSig
  :: FamilyResultSig GhcSe -> Conv (FamilyResultSig GhcPs)
cvFamilyResultSig (NoSig a) = pure (NoSig a)
cvFamilyResultSig (KindSig a b) = KindSig a <$> traverse cvType b
cvFamilyResultSig (TyVarSig a b) = TyVarSig a <$> traverse cvHsTyVarBndr b
cvFamilyResultSig (XFamilyResultSig a) = pure (XFamilyResultSig a)

cvFamilyInfo
  :: FamilyInfo GhcSe -> Conv (FamilyInfo GhcPs)
cvFamilyInfo DataFamily = pure DataFamily
cvFamilyInfo OpenTypeFamily = pure OpenTypeFamily
cvFamilyInfo (ClosedTypeFamily a) =
  ClosedTypeFamily <$> traverse (traverse (traverse (cvFamInstEqn (traverse cvType)))) a

cvFamInstEqn
  :: ( XCFamEqn GhcSe (HsTyPats GhcSe) a
       ~ XCFamEqn GhcPs (HsTyPats GhcPs) b
     , XHsIB GhcSe (FamEqn GhcSe (HsTyPats p) a)
       ~ XHsIB GhcPs (FamEqn GhcPs (HsTyPats GhcPs) b)
     , XXFamEqn GhcSe (HsTyPats GhcSe) a
       ~ XXFamEqn GhcPs (HsTyPats GhcPs) b
     , XXHsImplicitBndrs GhcSe (FamEqn GhcSe (HsTyPats GhcSe) a)
       ~ XXHsImplicitBndrs GhcPs (FamEqn GhcPs (HsTyPats GhcPs) b)
     )
  => (a -> Conv b)
  -> FamInstEqn GhcSe a
  -> Conv (FamInstEqn GhcPs b)
cvFamInstEqn f = cvHsImplicitBndrs (cvFamEqn (traverse (traverse cvType)) f)

cvFunDep :: ConvertName a b => FunDep a -> Conv (FunDep b)
cvFunDep (xs, ys) = (,) <$> convertName xs <*> convertName ys

cvLHsQTyVars :: LHsQTyVars GhcSe -> Conv (LHsQTyVars GhcPs)
cvLHsQTyVars (HsQTvs a b) = HsQTvs a <$> traverse (traverse cvHsTyVarBndr) b
cvLHsQTyVars (XLHsQTyVars a) = pure (XLHsQTyVars a)

cvForeignDecl :: ForeignDecl GhcSe -> Conv (ForeignDecl GhcPs)
cvForeignDecl (ForeignImport a b c d) =
  ForeignImport a
    <$> convertName b
    <*> cvHsImplicitBndrs (traverse cvType) c
    <*> pure d
cvForeignDecl (ForeignExport a b c d) =
  ForeignExport a
    <$> convertName b
    <*> cvHsImplicitBndrs (traverse cvType) c
    <*> pure d
cvForeignDecl (XForeignDecl a) = pure (XForeignDecl a)

cvDefaultDecl :: DefaultDecl GhcSe -> Conv (DefaultDecl GhcPs)
cvDefaultDecl (DefaultDecl a b) = DefaultDecl a <$> traverse (traverse cvType) b
cvDefaultDecl (XDefaultDecl a) = pure (XDefaultDecl a)

cvTyFamInstDecl
  :: TyFamInstDecl GhcSe -> Conv (TyFamInstDecl GhcPs)
cvTyFamInstDecl (TyFamInstDecl d) =
  TyFamInstDecl <$> cvFamInstEqn (traverse cvType) d

cvDataFamInstDecl
  :: DataFamInstDecl GhcSe -> Conv (DataFamInstDecl GhcPs)
cvDataFamInstDecl (DataFamInstDecl d) =
  DataFamInstDecl <$> cvFamInstEqn cvHsDataDefn d

cvHsDataDefn :: HsDataDefn GhcSe -> Conv (HsDataDefn GhcPs)
cvHsDataDefn (HsDataDefn a b c d e f g) =
  HsDataDefn a b
    <$> traverse (traverse (traverse cvType)) c <*> pure d
    <*> traverse (traverse cvType) e
    <*> traverse (traverse cvConDecl) f <*> cvHsDeriving g
cvHsDataDefn (XHsDataDefn a) = pure (XHsDataDefn a)

cvConDecl :: ConDecl GhcSe -> Conv (ConDecl GhcPs)
cvConDecl (ConDeclGADT a b c d e f g h) =
  ConDeclGADT a
    <$> convertName b
    <*> pure c
    <*> cvLHsQTyVars d
    <*> traverse (traverse (traverse (traverse cvType))) e
    <*> cvHsConDeclDetails f
    <*> traverse cvType g
    <*> pure h
cvConDecl (ConDeclH98 a b c d e f g) =
  ConDeclH98 a
    <$> convertName b
    <*> pure c
    <*> traverse (traverse cvHsTyVarBndr) d
    <*> traverse (traverse (traverse (traverse cvType))) e
    <*> cvHsConDeclDetails f
    <*> pure g
cvConDecl (XConDecl a) = pure (XConDecl a)

cvHsDeriving :: HsDeriving GhcSe -> Conv (HsDeriving GhcPs)
cvHsDeriving = traverse (traverse (traverse cvHsDerivingClause))

cvHsDerivingClause
  :: HsDerivingClause GhcSe -> Conv (HsDerivingClause GhcPs)
cvHsDerivingClause (HsDerivingClause a b c) =
  HsDerivingClause a
    <$> traverse (traverse cvDerivStrategy) b
    <*> traverse (traverse (cvHsImplicitBndrs (traverse cvType))) c
cvHsDerivingClause (XHsDerivingClause a) = pure (XHsDerivingClause a)

cvHsConDeclDetails
  :: HsConDeclDetails GhcSe -> Conv (HsConDeclDetails GhcPs)
cvHsConDeclDetails =
  cvHsConDetails (traverse cvType)
                 (traverse (traverse (traverse cvConDeclField)))

cvHsConDetails
  :: (a -> Conv c) -> (b -> Conv d) -> HsConDetails a b -> Conv (HsConDetails c d)
cvHsConDetails f _  (PrefixCon a) = PrefixCon <$> traverse f a
cvHsConDetails _ g     (RecCon a) = RecCon    <$> g a
cvHsConDetails f _ (InfixCon a b) = InfixCon  <$> f a <*> f b

cvConDeclField :: ConDeclField GhcSe -> Conv (ConDeclField GhcPs)
cvConDeclField (ConDeclField a b c d) =
  ConDeclField a <$> traverse (traverse cvFieldOcc) b <*> traverse cvType c
                 <*> pure d
cvConDeclField (XConDeclField a) = pure (XConDeclField a)

cvWarningDecls :: WarnDecls GhcSe -> Conv (WarnDecls GhcPs)
cvWarningDecls (Warnings a b c) =
  Warnings a b <$> traverse (traverse cvWarningDecl) c
cvWarningDecls (XWarnDecls a) = pure (XWarnDecls a)

cvWarningDecl :: WarnDecl GhcSe -> Conv (WarnDecl GhcPs)
cvWarningDecl (Warning a b c) = Warning a <$> convertName b <*> pure c
cvWarningDecl (XWarnDecl a) = pure (XWarnDecl a)

-- expressions

cvLHsExpr :: LHsExpr GhcSe -> Conv (LHsExpr GhcPs)
cvLHsExpr = traverse cvHsExpr

cvHsExpr :: HsExpr GhcSe -> Conv (HsExpr GhcPs)
cvHsExpr e = case e of
  HsVar a b -> HsVar a <$> convertName b
  HsUnboundVar a b -> pure (HsUnboundVar a b)
  HsConLikeOut a b -> pure (HsConLikeOut a b)
  HsRecFld a b -> HsRecFld a <$> cvAFieldOcc b
  HsOverLabel a b c -> HsOverLabel a <$> convertName b <*> pure c
  HsIPVar a b -> pure (HsIPVar a b)
  HsOverLit a b -> HsOverLit a <$> cvOverLit b
  HsLit a b -> HsLit a <$> cvLit b
  HsLam a b -> HsLam a <$> cvMatchGroup cvLHsExpr b
  HsLamCase a b -> HsLamCase a <$> cvMatchGroup cvLHsExpr b
  HsApp a b c -> HsApp a <$> cvLHsExpr b <*> cvLHsExpr c
  HsAppType a b -> HsAppType
    <$> cvHsWildCardBndrs (traverse cvType) a <*> cvLHsExpr b
  OpApp a b c d -> OpApp a <$> cvLHsExpr b <*> cvLHsExpr c <*> cvLHsExpr d
  NegApp a b c -> NegApp a <$> cvLHsExpr b <*> cvSyntaxExpr c
  HsPar a b -> HsPar a <$> cvLHsExpr b
  SectionL a b c -> SectionL a <$> cvLHsExpr b <*> cvLHsExpr c
  SectionR a b c -> SectionR a <$> cvLHsExpr b <*> cvLHsExpr c
  ExplicitTuple a b c -> ExplicitTuple a <$> traverse (traverse cvHsTupArg) b
                                         <*> pure c
  ExplicitSum a b c d -> ExplicitSum a b c <$> cvLHsExpr d
  ExplicitList a b c -> ExplicitList a <$> traverse cvSyntaxExpr b <*> traverse cvLHsExpr c
  HsCase a b c -> HsCase a <$> cvLHsExpr b <*> cvMatchGroup cvLHsExpr c
  HsIf a b c d e -> HsIf a <$> traverse cvSyntaxExpr b
                           <*> cvLHsExpr c <*> cvLHsExpr d <*> cvLHsExpr e
  HsMultiIf a b -> HsMultiIf a <$> traverse (traverse (cvGRHS cvLHsExpr)) b
  HsLet a b c -> HsLet a <$> traverse cvHsLocalBinds b <*> cvLHsExpr c
  HsDo a b c -> HsDo a
    <$> convertName b <*> traverse (traverse (traverse (cvStmtLR cvLHsExpr))) c
  RecordCon a b c -> RecordCon a <$> convertName b <*> cvRecordBinds c
  RecordUpd a b c -> RecordUpd a <$> cvLHsExpr b
                                 <*> traverse (traverse cvHsRecUpdField) c
  ExprWithTySig a b -> ExprWithTySig <$> cvHsSigWcType a <*> cvLHsExpr b
  ArithSeq a b c -> ArithSeq a <$> traverse cvSyntaxExpr b <*> cvArithSeqInfo c
  HsSCC a b c d -> HsSCC a b c <$> cvLHsExpr d
  HsCoreAnn a b c d -> HsCoreAnn a b c <$> cvLHsExpr d
  HsStatic a b -> HsStatic a <$> cvLHsExpr b
  EWildPat a -> pure (EWildPat a)
  EAsPat a b c -> EAsPat a <$> convertName b <*> cvLHsExpr c
  EViewPat a b c -> EViewPat a <$> cvLHsExpr b <*> cvLHsExpr c
  ELazyPat a b -> ELazyPat a <$> cvLHsExpr b
  HsProc a b c -> HsProc a <$> traverse cvPat b <*> traverse cvHsCmdTop c
  HsBinTick a b c d -> HsBinTick a b c <$> cvLHsExpr d
  HsTickPragma a b c d e -> HsTickPragma a b c d <$> cvLHsExpr e
  HsSpliceE a b -> HsSpliceE a <$> cvHsSplice b
  HsBracket a b -> HsBracket a <$> cvHsBracket b
  HsTick a b c -> HsTick a <$> cvTickish b <*> cvLHsExpr c
  XExpr a -> pure (XExpr a)
  HsArrApp {} -> unsupported "HsArrApp" "HsExpr" (error "<not printable>")
  HsArrForm {} -> unsupported "HsArrForm" "HsExpr" (error "<not printable>")
  HsWrap {} -> unsupported "HsWrap" "HsExpr" (error "<not printable>")
  HsRnBracketOut {} -> unsupported "HsRnBracketOut" "HsExpr" (error "<not printable>")
  HsTcBracketOut {} -> unsupported "HsTcBracketOut" "HsExpr" (error "<not printable>")

cvHsBracket :: HsBracket GhcSe -> Conv (HsBracket GhcPs)
cvHsBracket (ExpBr a b) = ExpBr a <$> cvLHsExpr b
cvHsBracket (PatBr a b) = PatBr a <$> traverse cvPat b
cvHsBracket (DecBrL a b) = DecBrL a <$> traverse (traverse cvHsDecl) b
cvHsBracket (DecBrG a b) = DecBrG a <$> cvHsGroup b
cvHsBracket (TypBr a b) = TypBr a <$> traverse cvType b
cvHsBracket (VarBr a b c) = VarBr a b <$> convertName c
cvHsBracket (TExpBr a b) = TExpBr a <$> cvLHsExpr b
cvHsBracket (XBracket a) = pure (XBracket a)

cvTickish :: ConvertName a b => Tickish a -> Conv (Tickish b)
cvTickish (ProfNote a b c) = pure (ProfNote a b c)
cvTickish (HpcTick a b) = pure (HpcTick a b)
cvTickish (Breakpoint a b) = Breakpoint a <$> convertName b
cvTickish (SourceNote a b) = pure (SourceNote a b)

cvHsGroup :: HsGroup GhcSe -> Conv (HsGroup GhcPs)
cvHsGroup (HsGroup a b c d e f g h i j k l) = HsGroup a
  <$> cvHsValBindsLR b <*> traverse (traverse cvSpliceDecl) c
  <*> traverse cvTyClGroup d
  <*> traverse (traverse cvDerivDecl) e
  <*> traverse (traverse cvFixitySig) f
  <*> traverse (traverse cvDefaultDecl) g
  <*> traverse (traverse cvForeignDecl) h
  <*> traverse (traverse cvWarningDecls) i
  <*> traverse (traverse cvAnnDecl) j
  <*> traverse (traverse cvRuleDecls) k
  <*> pure l
cvHsGroup (XHsGroup a) = pure (XHsGroup a)

cvTyClGroup :: TyClGroup GhcSe -> Conv (TyClGroup GhcPs)
cvTyClGroup (TyClGroup a b c d) = TyClGroup a
  <$> traverse (traverse cvTyClDecl) b
  <*> traverse (traverse cvRoleAnnotDecl) c
  <*> traverse (traverse cvInstDecl) d
cvTyClGroup (XTyClGroup a) = pure (XTyClGroup a)

cvHsCmdTop :: HsCmdTop GhcSe -> Conv (HsCmdTop GhcPs)
cvHsCmdTop (HsCmdTop a b) = HsCmdTop a <$> traverse cvHsCmd b
cvHsCmdTop (XCmdTop a) = pure (XCmdTop a)

cvHsCmd :: HsCmd GhcSe -> Conv (HsCmd GhcPs)
cvHsCmd (HsCmdArrApp a b c d e) = HsCmdArrApp a
  <$> cvLHsExpr b <*> cvLHsExpr c <*> pure d <*> pure e
cvHsCmd (HsCmdArrForm a b c d e) = HsCmdArrForm a
  <$> cvLHsExpr b <*> pure c <*> pure d
  <*> traverse (traverse cvHsCmdTop) e
cvHsCmd (HsCmdApp a b c) = HsCmdApp a <$> traverse cvHsCmd b <*> cvLHsExpr c
cvHsCmd (HsCmdLam a b) = HsCmdLam a <$> cvMatchGroup (traverse cvHsCmd) b
cvHsCmd (HsCmdPar a b) = HsCmdPar a <$> traverse cvHsCmd b
cvHsCmd (HsCmdCase a b c) = HsCmdCase a
  <$> cvLHsExpr b <*> cvMatchGroup (traverse cvHsCmd) c
cvHsCmd (HsCmdIf a b c d e) = HsCmdIf a
  <$> traverse cvSyntaxExpr b
  <*> cvLHsExpr c
  <*> traverse cvHsCmd d
  <*> traverse cvHsCmd e
cvHsCmd (HsCmdLet a b c) = HsCmdLet a
  <$> traverse cvHsLocalBinds b <*> traverse cvHsCmd c
cvHsCmd (HsCmdDo a b) = HsCmdDo a
  <$> traverse (traverse (traverse (cvStmtLR (traverse cvHsCmd)))) b
cvHsCmd (HsCmdWrap {}) = unsupported "HsCmdWrap" "HsCmd" (error "<not printable>")
cvHsCmd (XCmd a) = pure (XCmd a)

cvArithSeqInfo :: ArithSeqInfo GhcSe -> Conv (ArithSeqInfo GhcPs)
cvArithSeqInfo (From e) = From <$> cvLHsExpr e
cvArithSeqInfo (FromThen a b) = FromThen <$> cvLHsExpr a <*> cvLHsExpr b
cvArithSeqInfo (FromTo a b) = FromTo <$> cvLHsExpr a <*> cvLHsExpr b
cvArithSeqInfo (FromThenTo a b c) = FromThenTo <$> cvLHsExpr a <*> cvLHsExpr b <*> cvLHsExpr c

cvHsTupArg :: HsTupArg GhcSe -> Conv (HsTupArg GhcPs)
cvHsTupArg (Present a b) = Present a <$> cvLHsExpr b
cvHsTupArg (Missing a) = pure (Missing a)
cvHsTupArg (XTupArg a) = pure (XTupArg a)

cvAFieldOcc
  :: AmbiguousFieldOcc GhcSe -> Conv (AmbiguousFieldOcc GhcPs)
cvAFieldOcc (Unambiguous a b) = Unambiguous a <$> convertName b
cvAFieldOcc (Ambiguous a b) = Ambiguous a <$> convertName b
cvAFieldOcc (XAmbiguousFieldOcc a) = pure (XAmbiguousFieldOcc a)

cvOverLit :: HsOverLit GhcSe -> Conv (HsOverLit GhcPs)
cvOverLit (OverLit a b c) = OverLit a b <$> cvHsExpr c
cvOverLit (XOverLit a) = pure (XOverLit a)

cvLit :: HsLit GhcSe -> Conv (HsLit GhcPs)
cvLit (HsChar a b) = pure (HsChar a b)
cvLit (HsCharPrim a b) = pure (HsCharPrim a b)
cvLit (HsString a b) = pure (HsString a b)
cvLit (HsStringPrim a b) = pure (HsStringPrim a b)
cvLit (HsInt a b) = pure (HsInt a b)
cvLit (HsIntPrim a b) = pure (HsIntPrim a b)
cvLit (HsWordPrim a b) = pure (HsWordPrim a b)
cvLit (HsInt64Prim a b) = pure (HsInt64Prim a b)
cvLit (HsWord64Prim a b) = pure (HsWord64Prim a b)
cvLit (HsInteger a b c) = HsInteger a b <$> convertType c
cvLit (HsRat a b c) = HsRat a b <$> convertType c
cvLit (HsFloatPrim a b) = pure (HsFloatPrim a b)
cvLit (HsDoublePrim a b) = pure (HsDoublePrim a b)
cvLit (XLit a) = pure (XLit a)

cvMatchGroup
  :: ( XMG GhcSe a ~ XMG GhcPs b
     , XCMatch GhcSe a ~ XCMatch GhcPs b
     , XCGRHSs GhcSe a ~ XCGRHSs GhcPs b
     , XCGRHS GhcSe a ~ XCGRHS GhcPs b
     , XXMatchGroup GhcSe a ~ XXMatchGroup GhcPs b
     , XXMatch GhcSe a ~ XXMatch GhcPs b
     , XXGRHSs GhcSe a ~ XXGRHSs GhcPs b
     , XXGRHS GhcSe a ~ XXGRHS GhcPs b
     )
  => (a -> Conv b) -> MatchGroup GhcSe a -> Conv (MatchGroup GhcPs b)
cvMatchGroup f (MG a b c) = MG a
  <$> traverse (traverse (traverse (cvMatch f))) b
  <*> pure c
cvMatchGroup _ (XMatchGroup a) = pure (XMatchGroup a)

cvMatch
  :: ( XCMatch GhcSe a ~ XCMatch GhcPs b
     , XCGRHSs GhcSe a ~ XCGRHSs GhcPs b
     , XCGRHS GhcSe a ~ XCGRHS GhcPs b
     , XXMatch GhcSe a ~ XXMatch GhcPs b
     , XXGRHSs GhcSe a ~ XXGRHSs GhcPs b
     , XXGRHS GhcSe a ~ XXGRHS GhcPs b
     )
  => (a -> Conv b) -> Match GhcSe a -> Conv (Match GhcPs b)
cvMatch f (Match a b c d) = Match a
   <$> convertName b <*> traverse (traverse cvPat) c <*> cvGRHSs f d
cvMatch _ (XMatch a) = pure (XMatch a)

cvLHsPat :: LPat GhcSe -> Conv (LPat GhcPs)
cvLHsPat = traverse cvPat

cvPat :: Pat GhcSe -> Conv (Pat GhcPs)
cvPat (WildPat a) = pure (WildPat a)
cvPat (VarPat a b) = VarPat a <$> convertName b
cvPat (LazyPat a b) = LazyPat a <$> traverse cvPat b
cvPat (AsPat a b c) = AsPat a <$> convertName b <*> traverse cvPat c
cvPat (ParPat a b) = ParPat a <$> traverse cvPat b
cvPat (BangPat a b) = BangPat a <$> traverse cvPat b
cvPat (ListPat a b) = ListPat a
  <$> traverse (traverse cvPat) b
cvPat (TuplePat a b c) = TuplePat a
  <$> traverse (traverse cvPat) b
  <*> pure c
cvPat (SumPat a b c d) = SumPat a
  <$> traverse cvPat b
  <*> pure c <*> pure d
cvPat (ConPatIn a b) = ConPatIn <$> convertName a <*> cvHsConPatDetails b
cvPat (ViewPat a b c) = ViewPat a <$> cvLHsExpr b <*> traverse cvPat c
cvPat (LitPat a b) = LitPat a <$> cvLit b
cvPat (NPat a b c d) = NPat a
  <$> traverse cvOverLit b <*> traverse cvSyntaxExpr c
  <*> cvSyntaxExpr d
cvPat (NPlusKPat a b c d e f) = NPlusKPat a
  <$> convertName b
  <*> traverse cvOverLit c <*> cvOverLit d
  <*> cvSyntaxExpr e <*> cvSyntaxExpr f
cvPat (SigPat a b) = SigPat <$> cvHsSigWcType a <*> traverse cvPat b
cvPat (SplicePat a b) = SplicePat a <$> cvHsSplice b
cvPat (CoPat {}) = unsupported "CoPat" "Pat" (error "<not printable>")
cvPat (ConPatOut {}) = unsupported "ConPatOut" "Pat" (error "<not printable>")
cvPat (XPat a) = pure (XPat a)

cvGRHSs
  :: ( XCGRHSs GhcSe a ~ XCGRHSs GhcPs b
     , XCGRHS GhcSe a ~ XCGRHS GhcPs b
     , XXGRHSs GhcSe a ~ XXGRHSs GhcPs b
     , XXGRHS GhcSe a ~ XXGRHS GhcPs b
     )
  => (a -> Conv b) -> GRHSs GhcSe a -> Conv (GRHSs GhcPs b)
cvGRHSs f (GRHSs a b c) = GRHSs a
  <$> traverse (traverse (cvGRHS f)) b
  <*> traverse cvHsLocalBinds c
cvGRHSs _ (XGRHSs a) = pure (XGRHSs a)

cvGRHS
  :: ( XCGRHS GhcSe a ~ XCGRHS GhcPs b
     , XXGRHS GhcSe a ~ XXGRHS GhcPs b
     )
  => (a -> Conv b) -> GRHS GhcSe a -> Conv (GRHS GhcPs b)
cvGRHS f (GRHS a b c) = GRHS a
  <$> traverse (traverse (cvStmtLR cvLHsExpr)) b <*> f c
cvGRHS _ (XGRHS a) = pure (XGRHS a)

cvHsLocalBinds
  :: HsLocalBinds GhcSe -> Conv (HsLocalBinds GhcPs)
cvHsLocalBinds (HsValBinds a b) = HsValBinds a <$> cvHsValBindsLR b
cvHsLocalBinds (HsIPBinds a b) = HsIPBinds a <$> cvHsIPBinds b
cvHsLocalBinds (EmptyLocalBinds a) = pure (EmptyLocalBinds a)
cvHsLocalBinds (XHsLocalBindsLR a) = pure (XHsLocalBindsLR a)

cvHsValBindsLR
  :: HsValBindsLR GhcSe GhcSe -> Conv (HsValBindsLR GhcPs GhcPs)
cvHsValBindsLR (ValBinds a b c) = ValBinds a
  <$> mapBagM (traverse cvHsBindLR) b
  <*> traverse (traverse cvSig) c
cvHsValBindsLR (XValBindsLR _) =
  unsupported "XValBindsLR" "HsValBindsLR" (error "<not printable>")

cvHsConPatDetails
  :: HsConPatDetails GhcSe -> Conv (HsConPatDetails GhcPs)
cvHsConPatDetails (PrefixCon a) = PrefixCon <$> traverse (traverse cvPat) a
cvHsConPatDetails (RecCon a) = RecCon <$> cvHsRecFieldsPat a
cvHsConPatDetails (InfixCon a b) = InfixCon
  <$> traverse cvPat a <*> traverse cvPat b

cvHsRecFields
  :: (thing -> Conv thing')
  -> HsRecFields GhcSe thing
  -> Conv (HsRecFields GhcPs thing')
cvHsRecFields f (HsRecFields a b) =
  HsRecFields <$> traverse (traverse (cvHsRecField' cvFieldOcc f)) a <*> pure b

cvHsRecField'
  :: (id -> Conv id')
  -> (thing -> Conv thing')
  -> HsRecField' id thing
  -> Conv (HsRecField' id' thing')
cvHsRecField' f g (HsRecField a b c) =
  HsRecField <$> traverse f a <*> g b <*> pure c

cvHsRecFieldsPat
  :: HsRecFields GhcSe (LPat GhcSe) -> Conv (HsRecFields GhcPs (LPat GhcPs))
cvHsRecFieldsPat = cvHsRecFields (traverse cvPat)

cvHsRecUpdField
  :: HsRecUpdField GhcSe -> Conv (HsRecUpdField GhcPs)
cvHsRecUpdField = cvHsRecField' cvAFieldOcc cvLHsExpr

cvRecordBinds
  :: HsRecordBinds GhcSe -> Conv (HsRecordBinds GhcPs)
cvRecordBinds = cvHsRecFields cvLHsExpr

cvFieldOcc :: FieldOcc GhcSe -> Conv (FieldOcc GhcPs)
cvFieldOcc (FieldOcc a b) = FieldOcc a <$> convertName b
cvFieldOcc (XFieldOcc a) = pure (XFieldOcc a)

cvStmtLR
  :: ( XLastStmt GhcSe GhcSe a ~ XLastStmt GhcPs GhcPs b
     , XBindStmt GhcSe GhcSe a ~ XBindStmt GhcPs GhcPs b
     , XBodyStmt GhcSe GhcSe a ~ XBodyStmt GhcPs GhcPs b
     , XApplicativeStmt GhcSe GhcSe a ~ XApplicativeStmt GhcPs GhcPs b
     , XLetStmt GhcSe GhcSe a ~ XLetStmt GhcPs GhcPs b
     , XRecStmt GhcSe GhcSe a ~ XRecStmt GhcPs GhcPs b
     , XParStmt GhcSe GhcSe a ~ XParStmt GhcPs GhcPs b
     , XTransStmt GhcSe GhcSe a ~ XTransStmt GhcPs GhcPs b
     , XXStmtLR GhcSe GhcSe a ~ XXStmtLR GhcPs GhcPs b
     )
  => (a -> Conv b) -> StmtLR GhcSe GhcSe a -> Conv (StmtLR GhcPs GhcPs b)
cvStmtLR k (LastStmt a b c d) = LastStmt a
  <$> k b <*> pure c <*> cvSyntaxExpr d
cvStmtLR k (BindStmt a b c d e) = BindStmt a
  <$> traverse cvPat b <*> k c
  <*> cvSyntaxExpr d <*> cvSyntaxExpr e
cvStmtLR k (BodyStmt a b c d) = BodyStmt a
  <$> k b <*> cvSyntaxExpr c
  <*> cvSyntaxExpr d
cvStmtLR _ (ApplicativeStmt a b c) = ApplicativeStmt a
  <$> traverse
        (\(se, aa) -> (,) <$> cvSyntaxExpr se <*> cvApplicativeArg aa)
        b
  <*> traverse cvSyntaxExpr c
cvStmtLR _ (LetStmt a b) = LetStmt a <$> traverse cvHsLocalBinds b
cvStmtLR k (RecStmt a b c d e f g) = RecStmt a
  <$> traverse (traverse (cvStmtLR k)) b
  <*> convertName c
  <*> convertName d
  <*> cvSyntaxExpr e
  <*> cvSyntaxExpr f
  <*> cvSyntaxExpr g
cvStmtLR _ (ParStmt a b c d) = ParStmt a
  <$> traverse cvParStmtBlock b
  <*> cvHsExpr c
  <*> cvSyntaxExpr d
cvStmtLR _ (TransStmt a b c d e f g h i) = TransStmt a b
  <$> traverse (traverse (cvStmtLR cvLHsExpr)) c
  <*> traverse (\(x, y) -> (,) <$> convertName x <*> convertName y) d
  <*> cvLHsExpr e
  <*> traverse cvLHsExpr f
  <*> cvSyntaxExpr g
  <*> cvSyntaxExpr h
  <*> cvHsExpr i
cvStmtLR _ (XStmtLR a) = pure (XStmtLR a)

cvParStmtBlock
  :: ParStmtBlock GhcSe GhcSe -> Conv (ParStmtBlock GhcPs GhcPs)
cvParStmtBlock (ParStmtBlock a b c d) = ParStmtBlock a
  <$> traverse (traverse (cvStmtLR cvLHsExpr)) b
  <*> convertName c
  <*> cvSyntaxExpr d
cvParStmtBlock (XParStmtBlock a) = pure (XParStmtBlock a)

cvSyntaxExpr :: SyntaxExpr GhcSe -> Conv (SyntaxExpr GhcPs)
cvSyntaxExpr (SyntaxExpr a b c) =
  SyntaxExpr <$> cvHsExpr a <*> pure b <*> pure c

cvHsIPBinds
  :: HsIPBinds GhcSe -> Conv (HsIPBinds GhcPs)
cvHsIPBinds (IPBinds a b) = IPBinds a <$> traverse (traverse cvIPBind) b
cvHsIPBinds (XHsIPBinds a) = pure (XHsIPBinds a)

cvIPBind :: IPBind GhcSe -> Conv (IPBind GhcPs)
cvIPBind (IPBind a b c) = IPBind a <$> convertName b <*> cvLHsExpr c
cvIPBind (XIPBind a) = pure (XIPBind a)

cvHsBindLR
  :: HsBindLR GhcSe GhcSe -> Conv (HsBindLR GhcPs GhcPs)
cvHsBindLR (FunBind a b c d e) = FunBind a
  <$> convertName b
  <*> cvMatchGroup cvLHsExpr c
  <*> pure d <*> pure e
cvHsBindLR (PatBind a b c d ) = PatBind a
  <$> traverse cvPat b <*> cvGRHSs cvLHsExpr c <*> pure d
cvHsBindLR (VarBind a b c d) = VarBind a
  <$> convertName b <*> cvLHsExpr c <*> pure d
cvHsBindLR (PatSynBind a b) = PatSynBind a <$> cvPatSynBind b
cvHsBindLR (AbsBinds {}) =
  unsupported "AbsBind" "HsBindLR" (error "<not printable>")
cvHsBindLR (XHsBindsLR a) = pure (XHsBindsLR a)

cvHsWildCardBndrs
  :: ( XHsWC GhcSe thing ~ XHsWC GhcPs thing'
     , XXHsWildCardBndrs GhcSe thing ~ XXHsWildCardBndrs GhcPs thing'
     )
  => (thing -> Conv thing')
  -> HsWildCardBndrs GhcSe thing
  -> Conv (HsWildCardBndrs GhcPs thing')
cvHsWildCardBndrs thingF (HsWC a b) = HsWC a <$> thingF b
cvHsWildCardBndrs _ (XHsWildCardBndrs a) = pure (XHsWildCardBndrs a)

cvLHsWcType
  :: LHsWcType GhcSe -> Conv (LHsWcType GhcPs)
cvLHsWcType = cvHsWildCardBndrs (traverse cvType)

cvHsSigWcType
  :: LHsSigWcType GhcSe -> Conv (LHsSigWcType GhcPs)
cvHsSigWcType = cvHsWildCardBndrs (cvHsImplicitBndrs (traverse cvType))

cvHsImplicitBndrs
  :: ( XHsIB GhcSe thing ~ XHsIB GhcPs thing'
     , XXHsImplicitBndrs GhcSe thing ~ XXHsImplicitBndrs GhcPs thing'
     )
  => (thing -> Conv thing')
  -> HsImplicitBndrs GhcSe thing
  -> Conv (HsImplicitBndrs GhcPs thing')
cvHsImplicitBndrs f (HsIB a b) = HsIB a <$> f b
cvHsImplicitBndrs _ (XHsImplicitBndrs a) = pure (XHsImplicitBndrs a)

cvLHsType :: LHsType GhcSe -> Conv (LHsType GhcPs)
cvLHsType = traverse cvType

cvType :: HsType GhcSe -> Conv (HsType GhcPs)
cvType (HsForAllTy a b c) = HsForAllTy a
  <$> traverse (traverse cvHsTyVarBndr) b
  <*> traverse cvType c
cvType (HsQualTy a b c) = HsQualTy a
  <$> traverse (traverse (traverse cvType)) b
  <*> traverse cvType c
cvType (HsTyVar a b c) = HsTyVar a b <$> convertName c
cvType (HsAppTy a b c) = HsAppTy a
  <$> traverse cvType b
  <*> traverse cvType c
cvType (HsFunTy a b c) = HsFunTy a
  <$> traverse cvType b
  <*> traverse cvType c
cvType (HsListTy a b) = HsListTy a <$> traverse cvType b
cvType (HsTupleTy a b c) = HsTupleTy a b <$> traverse (traverse cvType) c
cvType (HsSumTy a b) = HsSumTy a <$> traverse (traverse cvType) b
cvType (HsOpTy a b c d) = HsOpTy a
  <$> traverse cvType b
  <*> convertName c
  <*> traverse cvType d
cvType (HsParTy a b) = HsParTy a <$> traverse cvType b
cvType (HsIParamTy a b c) = HsIParamTy a b <$> traverse cvType c
cvType (HsKindSig a b c) = HsKindSig a
  <$> traverse cvType b
  <*> traverse cvType c
cvType (HsBangTy a b c) = HsBangTy a b <$> traverse cvType c
cvType (HsRecTy a b) = HsRecTy a <$> traverse (traverse cvConDeclField) b
cvType (HsExplicitListTy a b c) = HsExplicitListTy a b
  <$> traverse (traverse cvType) c
cvType (HsExplicitTupleTy a b) = HsExplicitTupleTy a
  <$> traverse (traverse cvType) b
cvType (HsTyLit a b) = pure (HsTyLit a b)
cvType (HsWildCardTy a) = pure (HsWildCardTy a)
cvType (HsDocTy a b c) = HsDocTy a <$> traverse cvType b <*> pure c
cvType (HsSpliceTy a b) = HsSpliceTy a <$> cvHsSplice b
cvType (HsStarTy a b) = pure (HsStarTy a b)
cvType (XHsType a) = pure (XHsType a)

cvHsTyVarBndr
  :: HsTyVarBndr GhcSe -> Conv (HsTyVarBndr GhcPs)
cvHsTyVarBndr (UserTyVar a b) = UserTyVar a <$> convertName b
cvHsTyVarBndr (KindedTyVar a b c) = KindedTyVar a
  <$> convertName b
  <*> traverse cvType c
cvHsTyVarBndr (XTyVarBndr a) = pure (XTyVarBndr a)

cvApplicativeArg
  :: ApplicativeArg GhcSe -> Conv (ApplicativeArg GhcPs)
cvApplicativeArg (ApplicativeArgOne a b c d) = ApplicativeArgOne a
  <$> traverse cvPat b <*> cvLHsExpr c <*> pure d
cvApplicativeArg (ApplicativeArgMany a b c d) = ApplicativeArgMany a
  <$> traverse (traverse (cvStmtLR cvLHsExpr)) b <*> cvHsExpr c
  <*> traverse cvPat d
cvApplicativeArg (XApplicativeArg a) = pure (XApplicativeArg a)

cvSig :: Sig GhcSe -> Conv (Sig GhcPs)
cvSig (TypeSig a b c) = TypeSig a <$> convertName b <*> cvHsSigWcType c
cvSig (PatSynSig a b c) = PatSynSig a
  <$> convertName b <*> cvHsImplicitBndrs (traverse cvType) c
cvSig (ClassOpSig a b c d) = ClassOpSig a b
  <$> convertName c <*> cvHsImplicitBndrs (traverse cvType) d
cvSig (InlineSig a b c) = InlineSig a <$> convertName b <*> pure c
cvSig (FixSig a b) = FixSig a <$> cvFixitySig b
cvSig (SpecSig a b c d) = SpecSig a
  <$> convertName b
  <*> traverse (cvHsImplicitBndrs (traverse cvType)) c
  <*> pure d
cvSig (SpecInstSig a b c) = SpecInstSig a b
  <$> cvHsImplicitBndrs (traverse cvType) c
cvSig (SCCFunSig a b c d) = SCCFunSig a b <$> convertName c <*> pure d
cvSig (CompleteMatchSig a b c d) = CompleteMatchSig a b
  <$> convertName c <*> convertName d
cvSig (MinimalSig a b c) = MinimalSig a b <$> traverse (traverse convertName) c
cvSig (IdSig {}) = unsupported "IdSig" "Sig" (error "<not printable>")
cvSig (XSig a) = pure (XSig a)

cvFixitySig :: FixitySig GhcSe -> Conv (FixitySig GhcPs)
cvFixitySig (FixitySig a b c) = FixitySig a <$> convertName b <*> pure c
cvFixitySig (XFixitySig a) = pure (XFixitySig a)

cvPatSynBind :: PatSynBind GhcSe GhcSe -> Conv (PatSynBind GhcPs GhcPs)
cvPatSynBind (PSB a b c d e) = PSB a
  <$> convertName b
  <*> cvHsPatSynDetails convertName c <*> traverse cvPat d
  <*> cvHsPatSynDir e
cvPatSynBind (XPatSynBind a) = pure (XPatSynBind a)

cvHsPatSynDetails
  :: (a -> Conv b)
  -> HsPatSynDetails a
  -> Conv (HsPatSynDetails b)
cvHsPatSynDetails f = cvHsConDetails f (traverse (cvRecordPatSynField f))

cvRecordPatSynField
  :: (a -> Conv b)
  -> RecordPatSynField a
  -> Conv (RecordPatSynField b)
cvRecordPatSynField f (RecordPatSynField a b) =
  RecordPatSynField <$> f a <*> f b

cvHsPatSynDir :: HsPatSynDir GhcSe -> Conv (HsPatSynDir GhcPs)
cvHsPatSynDir Unidirectional = pure Unidirectional
cvHsPatSynDir ImplicitBidirectional = pure ImplicitBidirectional
cvHsPatSynDir (ExplicitBidirectional a) = ExplicitBidirectional
  <$> cvMatchGroup cvLHsExpr a
