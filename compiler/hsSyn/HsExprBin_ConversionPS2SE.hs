{-# LANGUAGE GADTs #-}
module HsExprBin_ConversionPS2SE where

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

cvLHsDecl :: LHsDecl GhcPs -> Conv (LHsDecl GhcSe)
cvLHsDecl = traverse cvHsDecl

cvHsDecl :: HsDecl GhcPs -> Conv (HsDecl GhcSe)
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

cvAnnDecl :: AnnDecl GhcPs -> Conv (AnnDecl GhcSe)
cvAnnDecl (HsAnnotation a b c d) =
  HsAnnotation a b <$> cvAnnProvenance c <*> cvLHsExpr d
cvAnnDecl (XAnnDecl a) = pure (XAnnDecl a)

cvInstDecl :: InstDecl GhcPs -> Conv (InstDecl GhcSe)
cvInstDecl (ClsInstD a b) = ClsInstD a <$> cvClsInstDecl b
cvInstDecl (DataFamInstD a b) = DataFamInstD a <$> cvDataFamInstDecl b
cvInstDecl (TyFamInstD a b) = TyFamInstD a <$> cvTyFamInstDecl b
cvInstDecl (XInstDecl a) = pure (XInstDecl a)

cvClsInstDecl :: ClsInstDecl GhcPs -> Conv (ClsInstDecl GhcSe)
cvClsInstDecl (ClsInstDecl a b c d e f g) =
  ClsInstDecl a
    <$> cvHsImplicitBndrs (traverse cvType) b
    <*> mapBagM (traverse cvHsBindLR) c
    <*> traverse (traverse cvSig) d
    <*> traverse (traverse cvTyFamInstDecl) e
    <*> traverse (traverse cvDataFamInstDecl) f
    <*> pure g
cvClsInstDecl (XClsInstDecl a) = pure (XClsInstDecl a)

cvDerivDecl :: DerivDecl GhcPs -> Conv (DerivDecl GhcSe)
cvDerivDecl (DerivDecl a b c d) =
  DerivDecl a <$> cvHsWildCardBndrs (cvHsImplicitBndrs $ traverse cvType) b
              <*> traverse (traverse cvDerivStrategy) c
              <*> pure d
cvDerivDecl (XDerivDecl a) = pure (XDerivDecl a)

cvDerivStrategy
  :: DerivStrategy GhcPs -> Conv (DerivStrategy GhcSe)
cvDerivStrategy StockStrategy = pure StockStrategy
cvDerivStrategy AnyclassStrategy = pure AnyclassStrategy
cvDerivStrategy NewtypeStrategy = pure NewtypeStrategy
cvDerivStrategy (ViaStrategy a) = ViaStrategy
  <$> cvHsImplicitBndrs (traverse cvType) a

cvTyClDecl :: TyClDecl GhcPs -> Conv (TyClDecl GhcSe)
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

cvRoleAnnotDecl :: RoleAnnotDecl GhcPs -> Conv (RoleAnnotDecl GhcSe)
cvRoleAnnotDecl (RoleAnnotDecl a b c) =
  RoleAnnotDecl a <$> convertName b <*> pure c
cvRoleAnnotDecl (XRoleAnnotDecl a) = pure (XRoleAnnotDecl a)

cvRuleDecls :: RuleDecls GhcPs -> Conv (RuleDecls GhcSe)
cvRuleDecls (HsRules a b c) = HsRules a b <$> traverse (traverse cvRuleDecl) c
cvRuleDecls (XRuleDecls a) = pure (XRuleDecls a)

cvRuleDecl :: RuleDecl GhcPs -> Conv (RuleDecl GhcSe)
cvRuleDecl (HsRule a b c d e f) =
  HsRule a b c <$> traverse (traverse cvRuleBndr) d
               <*> cvLHsExpr e <*> cvLHsExpr f
cvRuleDecl (XRuleDecl a) = pure (XRuleDecl a)

cvSpliceDecl :: SpliceDecl GhcPs -> Conv (SpliceDecl GhcSe)
cvSpliceDecl (SpliceDecl a b c) =
  SpliceDecl a <$> traverse cvHsSplice b <*> pure c
cvSpliceDecl (XSpliceDecl a) = pure (XSpliceDecl a)

cvHsSplice :: HsSplice GhcPs -> Conv (HsSplice GhcSe)
cvHsSplice (HsTypedSplice a b c d) =
  HsTypedSplice a b <$> convertName c <*> cvLHsExpr d
cvHsSplice (HsUntypedSplice a b c d) =
  HsUntypedSplice a b <$> convertName c <*> cvLHsExpr d
cvHsSplice (HsQuasiQuote a b c d e) =
  HsQuasiQuote a <$> convertName b <*> convertName c <*> pure d <*> pure e
cvHsSplice (HsSpliced {}) =
  unsupported "HsSpliced" "HsSplice" (error "<not printable>")
cvHsSplice (XSplice a) = pure (XSplice a)

cvRuleBndr :: RuleBndr GhcPs -> Conv (RuleBndr GhcSe)
cvRuleBndr (RuleBndr a b) = RuleBndr a <$> convertName b
cvRuleBndr (RuleBndrSig a b c) =
  RuleBndrSig a <$> convertName b <*> cvHsSigWcType c
cvRuleBndr (XRuleBndr a) = pure (XRuleBndr a)

cvFamEqn
  :: ( XCFamEqn GhcPs a b ~ XCFamEqn GhcSe c d
     , XXFamEqn GhcPs a b ~ XXFamEqn GhcSe c d
     )
  => (a -> Conv c)
  -> (b -> Conv d)
  -> FamEqn GhcPs a b
  -> Conv (FamEqn GhcSe c d)
cvFamEqn goPats goRhs (FamEqn a b c d e) =
  FamEqn a <$> convertName b <*> goPats c <*> pure d <*> goRhs e
cvFamEqn _ _ (XFamEqn a) = pure (XFamEqn a)

cvFamilyDecl :: FamilyDecl GhcPs -> Conv (FamilyDecl GhcSe)
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
  :: InjectivityAnn GhcPs -> Conv (InjectivityAnn GhcSe)
cvInjectivityAnn (InjectivityAnn a b) =
  InjectivityAnn <$> convertName a <*> convertName b

cvFamilyResultSig
  :: FamilyResultSig GhcPs -> Conv (FamilyResultSig GhcSe)
cvFamilyResultSig (NoSig a) = pure (NoSig a)
cvFamilyResultSig (KindSig a b) = KindSig a <$> traverse cvType b
cvFamilyResultSig (TyVarSig a b) = TyVarSig a <$> traverse cvHsTyVarBndr b
cvFamilyResultSig (XFamilyResultSig a) = pure (XFamilyResultSig a)

cvFamilyInfo
  :: FamilyInfo GhcPs -> Conv (FamilyInfo GhcSe)
cvFamilyInfo DataFamily = pure DataFamily
cvFamilyInfo OpenTypeFamily = pure OpenTypeFamily
cvFamilyInfo (ClosedTypeFamily a) =
  ClosedTypeFamily <$> traverse (traverse (traverse (cvFamInstEqn (traverse cvType)))) a

cvFamInstEqn
  :: ( XCFamEqn GhcPs (HsTyPats GhcPs) a
       ~ XCFamEqn GhcSe (HsTyPats GhcSe) b
     , XHsIB GhcPs (FamEqn GhcPs (HsTyPats p) a)
       ~ XHsIB GhcSe (FamEqn GhcSe (HsTyPats GhcSe) b)
     , XXFamEqn GhcPs (HsTyPats GhcPs) a
       ~ XXFamEqn GhcSe (HsTyPats GhcSe) b
     , XXHsImplicitBndrs GhcPs (FamEqn GhcPs (HsTyPats GhcPs) a)
       ~ XXHsImplicitBndrs GhcSe (FamEqn GhcSe (HsTyPats GhcSe) b)
     )
  => (a -> Conv b)
  -> FamInstEqn GhcPs a
  -> Conv (FamInstEqn GhcSe b)
cvFamInstEqn f = cvHsImplicitBndrs (cvFamEqn (traverse (traverse cvType)) f)

cvFunDep :: ConvertName a b => FunDep a -> Conv (FunDep b)
cvFunDep (xs, ys) = (,) <$> convertName xs <*> convertName ys

cvLHsQTyVars :: LHsQTyVars GhcPs -> Conv (LHsQTyVars GhcSe)
cvLHsQTyVars (HsQTvs a b) = HsQTvs a <$> traverse (traverse cvHsTyVarBndr) b
cvLHsQTyVars (XLHsQTyVars a) = pure (XLHsQTyVars a)

cvForeignDecl :: ForeignDecl GhcPs -> Conv (ForeignDecl GhcSe)
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

cvDefaultDecl :: DefaultDecl GhcPs -> Conv (DefaultDecl GhcSe)
cvDefaultDecl (DefaultDecl a b) = DefaultDecl a <$> traverse (traverse cvType) b
cvDefaultDecl (XDefaultDecl a) = pure (XDefaultDecl a)

cvTyFamInstDecl
  :: TyFamInstDecl GhcPs -> Conv (TyFamInstDecl GhcSe)
cvTyFamInstDecl (TyFamInstDecl d) =
  TyFamInstDecl <$> cvFamInstEqn (traverse cvType) d

cvDataFamInstDecl
  :: DataFamInstDecl GhcPs -> Conv (DataFamInstDecl GhcSe)
cvDataFamInstDecl (DataFamInstDecl d) =
  DataFamInstDecl <$> cvFamInstEqn cvHsDataDefn d

cvHsDataDefn :: HsDataDefn GhcPs -> Conv (HsDataDefn GhcSe)
cvHsDataDefn (HsDataDefn a b c d e f g) =
  HsDataDefn a b
    <$> traverse (traverse (traverse cvType)) c <*> pure d
    <*> traverse (traverse cvType) e
    <*> traverse (traverse cvConDecl) f <*> cvHsDeriving g
cvHsDataDefn (XHsDataDefn a) = pure (XHsDataDefn a)

cvConDecl :: ConDecl GhcPs -> Conv (ConDecl GhcSe)
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

cvHsDeriving :: HsDeriving GhcPs -> Conv (HsDeriving GhcSe)
cvHsDeriving = traverse (traverse (traverse cvHsDerivingClause))

cvHsDerivingClause
  :: HsDerivingClause GhcPs -> Conv (HsDerivingClause GhcSe)
cvHsDerivingClause (HsDerivingClause a b c) =
  HsDerivingClause a
    <$> traverse (traverse cvDerivStrategy) b
    <*> traverse (traverse (cvHsImplicitBndrs (traverse cvType))) c
cvHsDerivingClause (XHsDerivingClause a) = pure (XHsDerivingClause a)

cvHsConDeclDetails
  :: HsConDeclDetails GhcPs -> Conv (HsConDeclDetails GhcSe)
cvHsConDeclDetails =
  cvHsConDetails (traverse cvType)
                 (traverse (traverse (traverse cvConDeclField)))

cvHsConDetails
  :: (a -> Conv c) -> (b -> Conv d) -> HsConDetails a b -> Conv (HsConDetails c d)
cvHsConDetails f _  (PrefixCon a) = PrefixCon <$> traverse f a
cvHsConDetails _ g     (RecCon a) = RecCon    <$> g a
cvHsConDetails f _ (InfixCon a b) = InfixCon  <$> f a <*> f b

cvConDeclField :: ConDeclField GhcPs -> Conv (ConDeclField GhcSe)
cvConDeclField (ConDeclField a b c d) =
  ConDeclField a <$> traverse (traverse cvFieldOcc) b <*> traverse cvType c
                 <*> pure d
cvConDeclField (XConDeclField a) = pure (XConDeclField a)

cvWarningDecls :: WarnDecls GhcPs -> Conv (WarnDecls GhcSe)
cvWarningDecls (Warnings a b c) =
  Warnings a b <$> traverse (traverse cvWarningDecl) c
cvWarningDecls (XWarnDecls a) = pure (XWarnDecls a)

cvWarningDecl :: WarnDecl GhcPs -> Conv (WarnDecl GhcSe)
cvWarningDecl (Warning a b c) = Warning a <$> convertName b <*> pure c
cvWarningDecl (XWarnDecl a) = pure (XWarnDecl a)

-- expressions

cvLHsExpr :: LHsExpr GhcPs -> Conv (LHsExpr GhcSe)
cvLHsExpr = traverse cvHsExpr

cvHsExpr :: HsExpr GhcPs -> Conv (HsExpr GhcSe)
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
  HsAppType a b -> HsAppType <$> cvLHsWcType a <*> cvLHsExpr b
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

cvHsBracket :: HsBracket GhcPs -> Conv (HsBracket GhcSe)
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

cvHsGroup :: HsGroup GhcPs -> Conv (HsGroup GhcSe)
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

cvTyClGroup :: TyClGroup GhcPs -> Conv (TyClGroup GhcSe)
cvTyClGroup (TyClGroup a b c d) = TyClGroup a
  <$> traverse (traverse cvTyClDecl) b
  <*> traverse (traverse cvRoleAnnotDecl) c
  <*> traverse (traverse cvInstDecl) d
cvTyClGroup (XTyClGroup a) = pure (XTyClGroup a)

cvHsCmdTop :: HsCmdTop GhcPs -> Conv (HsCmdTop GhcSe)
cvHsCmdTop (HsCmdTop a b) = HsCmdTop a <$> traverse cvHsCmd b
cvHsCmdTop (XCmdTop a) = pure (XCmdTop a)

cvHsCmd :: HsCmd GhcPs -> Conv (HsCmd GhcSe)
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

cvArithSeqInfo :: ArithSeqInfo GhcPs -> Conv (ArithSeqInfo GhcSe)
cvArithSeqInfo (From e) = From <$> cvLHsExpr e
cvArithSeqInfo (FromThen a b) = FromThen <$> cvLHsExpr a <*> cvLHsExpr b
cvArithSeqInfo (FromTo a b) = FromTo <$> cvLHsExpr a <*> cvLHsExpr b
cvArithSeqInfo (FromThenTo a b c) = FromThenTo <$> cvLHsExpr a <*> cvLHsExpr b <*> cvLHsExpr c

cvHsTupArg :: HsTupArg GhcPs -> Conv (HsTupArg GhcSe)
cvHsTupArg (Present a b) = Present a <$> cvLHsExpr b
cvHsTupArg (Missing a) = pure (Missing a)
cvHsTupArg (XTupArg a) = pure (XTupArg a)

cvAFieldOcc
  :: AmbiguousFieldOcc GhcPs -> Conv (AmbiguousFieldOcc GhcSe)
cvAFieldOcc (Unambiguous a b) = Unambiguous a <$> convertName b
cvAFieldOcc (Ambiguous a b) = Ambiguous a <$> convertName b
cvAFieldOcc (XAmbiguousFieldOcc a) = pure (XAmbiguousFieldOcc a)

cvOverLit :: HsOverLit GhcPs -> Conv (HsOverLit GhcSe)
cvOverLit (OverLit a b c) = OverLit a b <$> cvHsExpr c
cvOverLit (XOverLit a) = pure (XOverLit a)

cvLit :: HsLit GhcPs -> Conv (HsLit GhcSe)
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
  :: ( XMG GhcPs a ~ XMG GhcSe b
     , XCMatch GhcPs a ~ XCMatch GhcSe b
     , XCGRHSs GhcPs a ~ XCGRHSs GhcSe b
     , XCGRHS GhcPs a ~ XCGRHS GhcSe b
     , XXMatchGroup GhcPs a ~ XXMatchGroup GhcSe b
     , XXMatch GhcPs a ~ XXMatch GhcSe b
     , XXGRHSs GhcPs a ~ XXGRHSs GhcSe b
     , XXGRHS GhcPs a ~ XXGRHS GhcSe b
     )
  => (a -> Conv b) -> MatchGroup GhcPs a -> Conv (MatchGroup GhcSe b)
cvMatchGroup f (MG a b c) = MG a
  <$> traverse (traverse (traverse (cvMatch f))) b
  <*> pure c
cvMatchGroup _ (XMatchGroup a) = pure (XMatchGroup a)

cvMatch
  :: ( XCMatch GhcPs a ~ XCMatch GhcSe b
     , XCGRHSs GhcPs a ~ XCGRHSs GhcSe b
     , XCGRHS GhcPs a ~ XCGRHS GhcSe b
     , XXMatch GhcPs a ~ XXMatch GhcSe b
     , XXGRHSs GhcPs a ~ XXGRHSs GhcSe b
     , XXGRHS GhcPs a ~ XXGRHS GhcSe b
     )
  => (a -> Conv b) -> Match GhcPs a -> Conv (Match GhcSe b)
cvMatch f (Match a b c d) = Match a
   <$> convertName b <*> traverse (traverse cvPat) c <*> cvGRHSs f d
cvMatch _ (XMatch a) = pure (XMatch a)

cvLHsPat :: LHsPat GhcPs -> Conv (LHsPat GhcSe)
cvLHsPat = traverse cvPat

cvPat :: Pat GhcPs -> Conv (Pat GhcSe)
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
  :: ( XCGRHSs GhcPs a ~ XCGRHSs GhcSe b
     , XCGRHS GhcPs a ~ XCGRHS GhcSe b
     , XXGRHSs GhcPs a ~ XXGRHSs GhcSe b
     , XXGRHS GhcPs a ~ XXGRHS GhcSe b
     )
  => (a -> Conv b) -> GRHSs GhcPs a -> Conv (GRHSs GhcSe b)
cvGRHSs f (GRHSs a b c) = GRHSs a
  <$> traverse (traverse (cvGRHS f)) b
  <*> traverse cvHsLocalBinds c
cvGRHSs _ (XGRHSs a) = pure (XGRHSs a)

cvGRHS
  :: ( XCGRHS GhcPs a ~ XCGRHS GhcSe b
     , XXGRHS GhcPs a ~ XXGRHS GhcSe b
     )
  => (a -> Conv b) -> GRHS GhcPs a -> Conv (GRHS GhcSe b)
cvGRHS f (GRHS a b c) = GRHS a
  <$> traverse (traverse (cvStmtLR cvLHsExpr)) b <*> f c
cvGRHS _ (XGRHS a) = pure (XGRHS a)

cvHsLocalBinds
  :: HsLocalBinds GhcPs -> Conv (HsLocalBinds GhcSe)
cvHsLocalBinds (HsValBinds a b) = HsValBinds a <$> cvHsValBindsLR b
cvHsLocalBinds (HsIPBinds a b) = HsIPBinds a <$> cvHsIPBinds b
cvHsLocalBinds (EmptyLocalBinds a) = pure (EmptyLocalBinds a)
cvHsLocalBinds (XHsLocalBindsLR a) = pure (XHsLocalBindsLR a)

cvHsValBindsLR
  :: HsValBindsLR GhcPs GhcPs -> Conv (HsValBindsLR GhcSe GhcSe)
cvHsValBindsLR (ValBinds a b c) = ValBinds a
  <$> mapBagM (traverse cvHsBindLR) b
  <*> traverse (traverse cvSig) c
cvHsValBindsLR (XValBindsLR _) =
  unsupported "XValBindsLR" "HsValBindsLR" (error "<not printable>")

cvHsConPatDetails
  :: HsConPatDetails GhcPs -> Conv (HsConPatDetails GhcSe)
cvHsConPatDetails (PrefixCon a) = PrefixCon <$> traverse (traverse cvPat) a
cvHsConPatDetails (RecCon a) = RecCon <$> cvHsRecFieldsPat a
cvHsConPatDetails (InfixCon a b) = InfixCon
  <$> traverse cvPat a <*> traverse cvPat b

cvHsRecFields
  :: (thing -> Conv thing')
  -> HsRecFields GhcPs thing
  -> Conv (HsRecFields GhcSe thing')
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
  :: HsRecFields GhcPs (LPat GhcPs) -> Conv (HsRecFields GhcSe (LPat GhcSe))
cvHsRecFieldsPat = cvHsRecFields (traverse cvPat)

cvHsRecUpdField
  :: HsRecUpdField GhcPs -> Conv (HsRecUpdField GhcSe)
cvHsRecUpdField = cvHsRecField' cvAFieldOcc cvLHsExpr

cvRecordBinds
  :: HsRecordBinds GhcPs -> Conv (HsRecordBinds GhcSe)
cvRecordBinds = cvHsRecFields cvLHsExpr

cvFieldOcc :: FieldOcc GhcPs -> Conv (FieldOcc GhcSe)
cvFieldOcc (FieldOcc a b) = FieldOcc a <$> convertName b
cvFieldOcc (XFieldOcc a) = pure (XFieldOcc a)

cvStmtLR
  :: ( XLastStmt GhcPs GhcPs a ~ XLastStmt GhcSe GhcSe b
     , XBindStmt GhcPs GhcPs a ~ XBindStmt GhcSe GhcSe b
     , XBodyStmt GhcPs GhcPs a ~ XBodyStmt GhcSe GhcSe b
     , XApplicativeStmt GhcPs GhcPs a ~ XApplicativeStmt GhcSe GhcSe b
     , XLetStmt GhcPs GhcPs a ~ XLetStmt GhcSe GhcSe b
     , XRecStmt GhcPs GhcPs a ~ XRecStmt GhcSe GhcSe b
     , XParStmt GhcPs GhcPs a ~ XParStmt GhcSe GhcSe b
     , XTransStmt GhcPs GhcPs a ~ XTransStmt GhcSe GhcSe b
     , XXStmtLR GhcPs GhcPs a ~ XXStmtLR GhcSe GhcSe b
     )
  => (a -> Conv b) -> StmtLR GhcPs GhcPs a -> Conv (StmtLR GhcSe GhcSe b)
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
  :: ParStmtBlock GhcPs GhcPs -> Conv (ParStmtBlock GhcSe GhcSe)
cvParStmtBlock (ParStmtBlock a b c d) = ParStmtBlock a
  <$> traverse (traverse (cvStmtLR cvLHsExpr)) b
  <*> convertName c
  <*> cvSyntaxExpr d
cvParStmtBlock (XParStmtBlock a) = pure (XParStmtBlock a)

cvSyntaxExpr :: SyntaxExpr GhcPs -> Conv (SyntaxExpr GhcSe)
cvSyntaxExpr (SyntaxExpr a b c) =
  SyntaxExpr <$> cvHsExpr a <*> pure b <*> pure c

cvHsIPBinds
  :: HsIPBinds GhcPs -> Conv (HsIPBinds GhcSe)
cvHsIPBinds (IPBinds a b) = IPBinds a <$> traverse (traverse cvIPBind) b
cvHsIPBinds (XHsIPBinds a) = pure (XHsIPBinds a)

cvIPBind :: IPBind GhcPs -> Conv (IPBind GhcSe)
cvIPBind (IPBind a b c) = IPBind a <$> convertName b <*> cvLHsExpr c
cvIPBind (XIPBind a) = pure (XIPBind a)

cvHsBindLR
  :: HsBindLR GhcPs GhcPs -> Conv (HsBindLR GhcSe GhcSe)
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
  :: ( XHsWC GhcPs thing ~ XHsWC GhcSe thing'
     , XXHsWildCardBndrs GhcPs thing ~ XXHsWildCardBndrs GhcSe thing'
     )
  => (thing -> Conv thing')
  -> HsWildCardBndrs GhcPs thing
  -> Conv (HsWildCardBndrs GhcSe thing')
cvHsWildCardBndrs thingF (HsWC a b) = HsWC a <$> thingF b
cvHsWildCardBndrs _ (XHsWildCardBndrs a) = pure (XHsWildCardBndrs a)

cvLHsWcType
  :: LHsWcType GhcPs -> Conv (LHsWcType GhcSe)
cvLHsWcType = cvHsWildCardBndrs (traverse cvType)

cvHsSigWcType
  :: LHsSigWcType GhcPs -> Conv (LHsSigWcType GhcSe)
cvHsSigWcType = cvHsWildCardBndrs (cvHsImplicitBndrs (traverse cvType))

cvHsImplicitBndrs
  :: ( XHsIB GhcPs thing ~ XHsIB GhcSe thing'
     , XXHsImplicitBndrs GhcPs thing ~ XXHsImplicitBndrs GhcSe thing'
     )
  => (thing -> Conv thing')
  -> HsImplicitBndrs GhcPs thing
  -> Conv (HsImplicitBndrs GhcSe thing')
cvHsImplicitBndrs f (HsIB a b) = HsIB a <$> f b
cvHsImplicitBndrs _ (XHsImplicitBndrs a) = pure (XHsImplicitBndrs a)

cvLHsType :: LHsType GhcPs -> Conv (HsType GhcSe)
cvLHsType = traverse cvType

cvType :: HsType GhcPs -> Conv (HsType GhcSe)
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
  :: HsTyVarBndr GhcPs -> Conv (HsTyVarBndr GhcSe)
cvHsTyVarBndr (UserTyVar a b) = UserTyVar a <$> convertName b
cvHsTyVarBndr (KindedTyVar a b c) = KindedTyVar a
  <$> convertName b
  <*> traverse cvType c
cvHsTyVarBndr (XTyVarBndr a) = pure (XTyVarBndr a)

cvApplicativeArg
  :: ApplicativeArg GhcPs -> Conv (ApplicativeArg GhcSe)
cvApplicativeArg (ApplicativeArgOne a b c d) = ApplicativeArgOne a
  <$> traverse cvPat b <*> cvLHsExpr c <*> pure d
cvApplicativeArg (ApplicativeArgMany a b c d) = ApplicativeArgMany a
  <$> traverse (traverse (cvStmtLR cvLHsExpr)) b <*> cvHsExpr c
  <*> traverse cvPat d
cvApplicativeArg (XApplicativeArg a) = pure (XApplicativeArg a)

cvSig :: Sig GhcPs -> Conv (Sig GhcSe)
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

cvFixitySig :: FixitySig GhcPs -> Conv (FixitySig GhcSe)
cvFixitySig (FixitySig a b c) = FixitySig a <$> convertName b <*> pure c
cvFixitySig (XFixitySig a) = pure (XFixitySig a)

cvPatSynBind :: PatSynBind GhcPs GhcPs -> Conv (PatSynBind GhcSe GhcSe)
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

cvHsPatSynDir :: HsPatSynDir GhcPs -> Conv (HsPatSynDir GhcSe)
cvHsPatSynDir Unidirectional = pure Unidirectional
cvHsPatSynDir ImplicitBidirectional = pure ImplicitBidirectional
cvHsPatSynDir (ExplicitBidirectional a) = ExplicitBidirectional
  <$> cvMatchGroup cvLHsExpr a
