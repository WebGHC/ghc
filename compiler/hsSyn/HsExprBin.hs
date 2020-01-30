module HsExprBin
  ( getModuleSplicesPath
  , whenSet
  , HsSpliceData(..)
  , nonEmptyHsSpliceData
  , emptyHsSpliceData
  , SpliceResult(..)
  , recordSpliceResult
  , lookupSpliceResult
  , exprSE2PS
  , declSE2PS
  , patSE2PS
  , tySE2PS
  , exprPS2SE
  , declPS2SE
  , patPS2SE
  , tyPS2SE
  , handleUnsupported
  ) where

import Binary
import GhcPrelude
import HsDecls
import HsExpr
import HsExprBin_Conversions
import qualified HsExprBin_ConversionSE2PS as SE2PS
import qualified HsExprBin_ConversionPS2SE as PS2SE
import HsExprBin_Instances ()
import HsExtension
import HsPat
import HsTypes
import Module
import Outputable
import SrcLoc
import TcRnTypes

import qualified Data.Map.Strict as Map
import System.FilePath

{-

Note [Serialisable AST phase]

There is an AST phase called GhcSe, where 'Se' stands for Serialisable.
It is quite close to GhcPs, in that it mostly represents ASTs the same way,
except for (syntax-level) types and names, which are represented in a way
that is (binary) serialisation friendly.

The motivation for this new phase is to be able to serialise ASTs of Haskell
code. (No existing phase has this property.) One use case would be to save
ASTs resulting from the evaluation of Template Haskell code and to reuse them
later, in place of evaluating the Template Haskell code. More generally,
it seems useful to be able to persist or load parsed ASTs, may it be for
IDE-style interactions or plugins.

The purpose of the HsExprBin* modules is to define:
- conversions from GhcSe to GhcPs, and back, with the four functions exported
  by this module;
- Binary instances for AST data types, only when "instantiated" at the GhcSe
  phase.

The former is done in two modules: HsExprBin_ConversionSE2PS and
HsExprBin_ConversionPS2SE. The latter in HsExprBin_Instances.

-}

-- * .hs-splice file contents

getModuleSplicesPath :: FilePath -> Module -> FilePath
getModuleSplicesPath splicesDir m = splicesDir
  </> toPath (moduleNameString (moduleName m)) <.> "hs-splice"

  where toPath = map (\c -> if c == '.' then '/' else c)

whenSet :: Monad m => Maybe a -> (a -> m b) -> m b -> m b
whenSet m j n = maybe n j m

newtype HsSpliceData = HsSpliceData { hsSpliceMap :: Map.Map SrcSpan SpliceResult }

emptyHsSpliceData :: HsSpliceData
emptyHsSpliceData = HsSpliceData Map.empty

nonEmptyHsSpliceData :: HsSpliceData -> Bool
nonEmptyHsSpliceData = not . Map.null . hsSpliceMap

data SpliceResult
  = SRExpr  (LHsExpr GhcSe)
  | SRDecls [LHsDecl GhcSe] -- TODO: change to HsGroup ?
  | SRPat   (LPat GhcSe)
  | SRTy    (LHsType GhcSe)

instance Binary SpliceResult where
  put_ bh r = case r of
    SRExpr e -> putByte bh 0 >> put_ bh e
    SRDecls ds -> putByte bh 1 >> put_ bh ds
    SRPat p -> putByte bh 2 >> put_ bh p
    SRTy t  -> putByte bh 3 >> put_ bh t
  get bh = do
    tag <- getByte bh
    case tag of
      0 -> SRExpr <$> get bh
      1 -> SRDecls <$> get bh
      2 -> SRPat <$> get bh
      3 -> SRTy <$> get bh
      _ -> panic "Binary SpliceResult: unknown tag"

instance Binary HsSpliceData where
  put_ bh (HsSpliceData m) = put_ bh (Map.toList m)
  get bh = (\l -> HsSpliceData (Map.fromList l)) <$> get bh

recordSpliceResult :: SrcSpan -> SpliceResult -> HsSpliceData -> HsSpliceData
recordSpliceResult loc res (HsSpliceData m) = HsSpliceData (Map.insert loc res m)

lookupSpliceResult :: SrcSpan -> HsSpliceData -> Maybe SpliceResult
lookupSpliceResult loc (HsSpliceData m) = Map.lookup loc m

-- * High-level conversion interface

-- Converting Se -> Ps

-- | Convert a serialisable expression AST to a parsed expression AST
exprSE2PS :: LHsExpr GhcSe -> RnM (ConvResult (LHsExpr GhcPs))
exprSE2PS = runConv . SE2PS.cvLHsExpr

-- | Convert a serialisable declaration AST to a parsed declaration AST
declSE2PS :: LHsDecl GhcSe -> RnM (ConvResult (LHsDecl GhcPs))
declSE2PS = runConv . SE2PS.cvLHsDecl

-- | Convert a serialisable pattern AST to a parsed pattern AST
patSE2PS :: LPat GhcSe -> RnM (ConvResult (LPat GhcPs))
patSE2PS = runConv . SE2PS.cvLHsPat

-- | Convert a serialisable type AST to a parsed type ST
tySE2PS :: LHsType GhcSe -> RnM (ConvResult (LHsType GhcPs))
tySE2PS = runConv . SE2PS.cvLHsType

-- Converting Ps -> Se

-- | Convert a parsed expression AST to a serialisable expression AST
exprPS2SE :: LHsExpr GhcPs -> RnM (ConvResult (LHsExpr GhcSe))
exprPS2SE = runConv . PS2SE.cvLHsExpr

-- | Convert a parsed declaration AST to a serialisable expression AST
declPS2SE :: LHsDecl GhcPs -> RnM (ConvResult (LHsDecl GhcSe))
declPS2SE = runConv . PS2SE.cvLHsDecl

-- | Convert a serialisable pattern AST to a parsed pattern AST
patPS2SE :: LPat GhcPs -> RnM (ConvResult (LPat GhcSe))
patPS2SE = runConv . PS2SE.cvLHsPat

-- | Convert a serialisable type AST to a parsed type ST
tyPS2SE :: LHsType GhcPs -> RnM (ConvResult (LHsType GhcSe))
tyPS2SE = runConv . PS2SE.cvLHsType

-- * Error reporting

-- | Panics with a nice error when we encounter an unsupported
--   construct, or returns the actual result if the conversion
--   succeeded.
handleUnsupported
  :: Located SDoc -- ^ TH expression that got evaluated
  -> Maybe SDoc -- ^ code resulting from the evaluation of the 1st arg
  -> ConvResult a -- ^ result of the conversion
  -> RnM a
handleUnsupported (L loc thDoc) resDoc convRes = case convRes of
  ConvOK a -> pure a
  ConvError (ConvUnsupported conName tyName subexprDoc) ->
    pprPanic "HsExprBin.handleUnsupported" . vcat $
      [ text "GHC encountered a Haskell construct not supported by -{load, save}-splices:"
      , nest 4 $ subexprDoc <> text (" - constructor " ++ conName ++ " of type " ++ tyName)
      , text "while evaluating the following expression from "  <> ppr loc <> text ":"
      , nest 4 $ thDoc
      ] ++
      maybe [] (\d -> [text "which resulted in:" , nest 4 d]) resDoc

  ConvError (ConvFailure errorStr) -> panic errorStr
