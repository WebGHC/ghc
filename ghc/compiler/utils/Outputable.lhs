%
% (c) The GRASP Project, Glasgow University, 1992-1996
%
\section[Outputable]{Classes for pretty-printing}

Defines classes for pretty-printing and forcing, both forms of
``output.''

\begin{code}
#include "HsVersions.h"

module Outputable (
	-- NAMED-THING-ERY
	NamedThing(..),		-- class
	ExportFlag(..),

	getItsUnique, getOrigName, getOccName, getExportFlag,
	getSrcLoc, isLocallyDefined, isPreludeDefined, isExported,
	getLocalName, getOrigNameRdr, ltLexical,

	-- PRINTERY AND FORCERY
	Outputable(..), 	-- class

	interppSP, interpp'SP,
	ifnotPprForUser,
	ifPprDebug,
	ifPprShowAll, ifnotPprShowAll,
	ifPprInterface,

	isOpLexeme, pprOp, pprNonOp,
	isConop, isAconop, isAvarid, isAvarop
    ) where

import Ubiq{-uitous-}

import Name		( nameUnique, nameOrigName, nameOccName,
			  nameExportFlag, nameSrcLoc,
			  isLocallyDefinedName, isPreludeDefinedName
			)
import PprStyle		( PprStyle(..) )
import Pretty
import Util		( cmpPString )
\end{code}

%************************************************************************
%*									*
\subsection[NamedThing-class]{The @NamedThing@ class}
%*									*
%************************************************************************

\begin{code}
class NamedThing a where
    getName :: a -> Name

getItsUnique	    :: NamedThing a => a -> Unique
getOrigName	    :: NamedThing a => a -> (Module, FAST_STRING)
getOccName	    :: NamedThing a => a -> RdrName
getExportFlag	    :: NamedThing a => a -> ExportFlag
getSrcLoc	    :: NamedThing a => a -> SrcLoc
isLocallyDefined    :: NamedThing a => a -> Bool
isPreludeDefined    :: NamedThing a => a -> Bool

getItsUnique	    = nameUnique   	   . getName
getOrigName	    = nameOrigName 	   . getName
getOccName	    = nameOccName  	   . getName
getExportFlag	    = nameExportFlag	   . getName
getSrcLoc	    = nameSrcLoc	   . getName
isLocallyDefined    = isLocallyDefinedName . getName
isPreludeDefined    = isPreludeDefinedName . getName

isExported a
  = case (getExportFlag a) of
      NotExported -> False
      _		  -> True

getLocalName :: (NamedThing a) => a -> FAST_STRING
getLocalName = snd . getOrigName

getOrigNameRdr :: (NamedThing a) => a -> RdrName
getOrigNameRdr n | isPreludeDefined n = Unqual str
		 | otherwise          = Qual mod str
  where
    (mod,str) = getOrigName n

#ifdef USE_ATTACK_PRAGMAS
{-# SPECIALIZE isExported :: Class -> Bool #-}
{-# SPECIALIZE isExported :: Id -> Bool #-}
{-# SPECIALIZE isExported :: TyCon -> Bool #-}
#endif
\end{code}

@ltLexical@ is used for sorting things into lexicographical order, so
as to canonicalize interfaces.  [Regular @(<)@ should be used for fast
comparison.]

\begin{code}
a `ltLexical` b
  = BIND isLocallyDefined a	_TO_ a_local ->
    BIND isLocallyDefined b	_TO_ b_local ->
    BIND getOrigName a		_TO_ (a_mod, a_name) ->
    BIND getOrigName b		_TO_ (b_mod, b_name) ->
    if a_local || b_local then
       a_name < b_name	-- can't compare module names
    else
       case _CMP_STRING_ a_mod b_mod of
	 LT_  -> True
	 EQ_  -> a_name < b_name
	 GT__ -> False
    BEND BEND BEND BEND

#ifdef USE_ATTACK_PRAGMAS
{-# SPECIALIZE ltLexical :: Class -> Class -> Bool #-}
{-# SPECIALIZE ltLexical :: Id -> Id -> Bool #-}
{-# SPECIALIZE ltLexical :: TyCon -> TyCon -> Bool #-}
#endif
\end{code}

%************************************************************************
%*									*
\subsection[ExportFlag-datatype]{The @ExportFlag@ datatype}
%*									*
%************************************************************************

The export flag @ExportAll@ means `export all there is', so there are
times when it is attached to a class or data type which has no
ops/constructors (if the class/type was imported abstractly).  In
fact, @ExportAll@ is attached to everything except to classes/types
which are being {\em exported} abstractly, regardless of how they were
imported.

\begin{code}
data ExportFlag
  = ExportAll		-- export with all constructors/methods
  | ExportAbs		-- export abstractly
  | NotExported
\end{code}

%************************************************************************
%*									*
\subsection[Outputable-class]{The @Outputable@ class}
%*									*
%************************************************************************

\begin{code}
class Outputable a where
	ppr :: PprStyle -> a -> Pretty
\end{code}

\begin{code}
-- the ppSep in the ppInterleave puts in the spaces
-- Death to ppSep! (WDP 94/11)

interppSP  :: Outputable a => PprStyle -> [a] -> Pretty
interppSP  sty xs = ppIntersperse ppSP (map (ppr sty) xs)

interpp'SP :: Outputable a => PprStyle -> [a] -> Pretty
interpp'SP sty xs
  = ppInterleave sep (map (ppr sty) xs)
  where
    sep = ppBeside ppComma ppSP

#ifdef USE_ATTACK_PRAGMAS
{-# SPECIALIZE interppSP :: PprStyle -> [Id] -> Pretty #-}
{-# SPECIALIZE interppSP :: PprStyle -> [TyVar] -> Pretty #-}

{-# SPECIALIZE interpp'SP :: PprStyle -> [(Id, Id)] -> Pretty #-}
{-# SPECIALIZE interpp'SP :: PprStyle -> [Id] -> Pretty #-}
{-# SPECIALIZE interpp'SP :: PprStyle -> [TyVarTemplate] -> Pretty #-}
{-# SPECIALIZE interpp'SP :: PprStyle -> [TyVar] -> Pretty #-}
{-# SPECIALIZE interpp'SP :: PprStyle -> [Type] -> Pretty #-}
#endif
\end{code}

\begin{code}
ifPprDebug	sty p = case sty of PprDebug	 -> p ; _ -> ppNil
ifPprShowAll	sty p = case sty of PprShowAll	 -> p ; _ -> ppNil
ifPprInterface  sty p = case sty of PprInterface -> p ; _ -> ppNil

ifnotPprForUser	  sty p = case sty of PprForUser -> ppNil ; _ -> p
ifnotPprShowAll	  sty p = case sty of PprShowAll -> ppNil ; _ -> p
\end{code}

These functions test strings to see if they fit the lexical categories
defined in the Haskell report. 
Normally applied as in e.g. @isConop (getLocalName foo)@

\begin{code}
isConop, isAconop, isAvarid, isAvarop :: FAST_STRING -> Bool

isConop cs
  | _NULL_ cs	= False
  | c == '_'	= isConop (_TAIL_ cs)		-- allow for leading _'s
  | otherwise	= isUpper c || c == ':' 
		  || c == '[' || c == '('	-- [] () and (,,) come is as Conop strings !!!
		  || isUpperISO c
  where					
    c = _HEAD_ cs

isAconop cs
  | _NULL_ cs	= False
  | otherwise	= c == ':'
  where
    c = _HEAD_ cs

isAvarid cs
  | _NULL_ cs	 = False
  | c == '_'	 = isAvarid (_TAIL_ cs)	-- allow for leading _'s
  | isLower c	 = True
  | isLowerISO c = True
  | otherwise    = False
  where
    c = _HEAD_ cs

isAvarop cs
  | _NULL_ cs	 		    = False
  | isLower c    		    = False
  | isUpper c    		    = False
  | c `elem` "!#$%&*+./<=>?@\\^|~-" = True
  | isSymbolISO c		    = True
  | otherwise			    = False
  where
    c = _HEAD_ cs

isSymbolISO c = ord c `elem` (0xd7 : 0xf7 : [0xa1 .. 0xbf])
isUpperISO  c = 0xc0 <= oc && oc <= 0xde && oc /= 0xd7 where oc = ord c
isLowerISO  c = 0xdf <= oc && oc <= 0xff && oc /= 0xf7 where oc = ord c
\end{code}

And one ``higher-level'' interface to those:

\begin{code}
isOpLexeme :: NamedThing a => a -> Bool

isOpLexeme v
  = let str = snd (getOrigName v) in isAvarop str || isAconop str

-- print `vars`, (op) correctly
pprOp, pprNonOp :: (NamedThing name, Outputable name) => PprStyle -> name -> Pretty

pprOp sty var
  = if isOpLexeme var
    then ppr sty var
    else ppBesides [ppChar '`', ppr sty var, ppChar '`']

pprNonOp sty var
  = if isOpLexeme var
    then ppBesides [ppLparen, ppr sty var, ppRparen]
    else ppr sty var

#ifdef USE_ATTACK_PRAGMAS
{-# SPECIALIZE isOpLexeme :: Id -> Bool #-}
{-# SPECIALIZE pprNonOp :: PprStyle -> Id -> Pretty #-}
{-# SPECIALIZE pprNonOp :: PprStyle -> TyCon -> Pretty #-}
{-# SPECIALIZE pprOp :: PprStyle -> Id -> Pretty #-}
#endif
\end{code}

\begin{code}
instance Outputable Bool where
    ppr sty True = ppPStr SLIT("True")
    ppr sty False = ppPStr SLIT("False")

instance (Outputable a) => Outputable [a] where
    ppr sty xs =
      ppBesides [ ppLbrack, ppInterleave ppComma (map (ppr sty) xs), ppRbrack ]

instance (Outputable a, Outputable b) => Outputable (a, b) where
    ppr sty (x,y) =
      ppHang (ppBesides [ppLparen, ppr sty x, ppComma]) 4 (ppBeside (ppr sty y) ppRparen)

-- ToDo: may not be used
instance (Outputable a, Outputable b, Outputable c) => Outputable (a, b, c) where
    ppr sty (x,y,z) =
      ppSep [ ppBesides [ppLparen, ppr sty x, ppComma],
	      ppBeside (ppr sty y) ppComma,
	      ppBeside (ppr sty z) ppRparen ]
\end{code}
