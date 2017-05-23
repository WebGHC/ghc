
module TH_Depends_External where

import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Lib

loadStringFromFile :: Q Exp
loadStringFromFile = do
  let externalDependency = "TH_Depends_external.txt"
  qAddDependentFile externalDependency
  s <- qReadFile externalDependency
  stringE s
