{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module SeName (SeName(..), mkSeName) where

import Outputable
import RdrName

-- TODO: make this smarter, so as to check whether
-- the name is local or not.
newtype SeName = SeName RdrName
  deriving (Outputable, OutputableBndr)

mkSeName :: RdrName -> SeName
mkSeName = SeName
