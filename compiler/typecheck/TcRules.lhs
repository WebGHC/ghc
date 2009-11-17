%
% (c) The University of Glasgow 2006
% (c) The AQUA Project, Glasgow University, 1993-1998
%

TcRules: Typechecking transformation rules

\begin{code}
module TcRules ( tcRules ) where

import HsSyn
import TcRnMonad
import TcSimplify
import TcMType
import TcType
import TcHsType
import TcExpr
import TcEnv
import Inst
import Id
import Name
import SrcLoc
import Outputable
import FastString
\end{code}

Note [Typechecking rules]
~~~~~~~~~~~~~~~~~~~~~~~~~
We *infer* the typ of the LHS, and use that type to *check* the type of 
the RHS.  That means that higher-rank rules work reasonably well. Here's
an example (test simplCore/should_compile/rule2.hs) produced by Roman:

   foo :: (forall m. m a -> m b) -> m a -> m b
   foo f = ...

   bar :: (forall m. m a -> m a) -> m a -> m a
   bar f = ...

   {-# RULES "foo/bar" foo = bar #-}

He wanted the rule to typecheck.

\begin{code}
tcRules :: [LRuleDecl Name] -> TcM [LRuleDecl TcId]
tcRules decls = mapM (wrapLocM tcRule) decls

tcRule :: RuleDecl Name -> TcM (RuleDecl TcId)
tcRule (HsRule name act vars lhs fv_lhs rhs fv_rhs)
  = addErrCtxt (ruleCtxt name)			$ do
    traceTc (ptext (sLit "---- Rule ------") <+> ppr name)

	-- Deal with the tyvars mentioned in signatures
    (ids, lhs', rhs', lhs_lie, rhs_lie, rule_ty) <-
      tcRuleBndrs vars $ \ ids -> do
		-- Now LHS and RHS; see Note [Typechecking rules]
        ((lhs', rule_ty), lhs_lie) <- getLIE (tcInferRho lhs)
        (rhs', rhs_lie) <- getLIE (tcMonoExpr rhs rule_ty)
        return (ids, lhs', rhs', lhs_lie, rhs_lie, rule_ty)

		-- Check that LHS has no overloading at all
    (lhs_dicts, lhs_binds) <- tcSimplifyRuleLhs lhs_lie

	-- Gather the template variables and tyvars
    let
	tpl_ids = map instToId lhs_dicts ++ ids

	-- IMPORTANT!  We *quantify* over any dicts that appear in the LHS
	-- Reason: 
	--	a) The particular dictionary isn't important, because its value
	--	   depends only on the type
	--		e.g	gcd Int $fIntegralInt
	--         Here we'd like to match against (gcd Int any_d) for any 'any_d'
	--
	--	b) We'd like to make available the dictionaries bound 
	--	   on the LHS in the RHS, so quantifying over them is good
	--	   See the 'lhs_dicts' in tcSimplifyAndCheck for the RHS

	-- We initially quantify over any tyvars free in *either* the rule
	--  *or* the bound variables.  The latter is important.  Consider
	--	ss (x,(y,z)) = (x,z)
	--	RULE:  forall v. fst (ss v) = fst v
	-- The type of the rhs of the rule is just a, but v::(a,(b,c))
	--
	-- We also need to get the free tyvars of the LHS; but we do that
	-- during zonking (see TcHsSyn.zonkRule)
	--
	forall_tvs = tyVarsOfTypes (rule_ty : map idType tpl_ids)

	-- RHS can be a bit more lenient.  In particular,
	-- we let constant dictionaries etc float outwards
	--
	-- NB: tcSimplifyInferCheck zonks the forall_tvs, and 
	--     knocks out any that are constrained by the environment
    loc <- getInstLoc (SigOrigin (RuleSkol name))
    (forall_tvs1, rhs_binds) <- tcSimplifyInferCheck loc
                                        forall_tvs
                                        lhs_dicts rhs_lie

    return (HsRule name act
		    (map (RuleBndr . noLoc) (forall_tvs1 ++ tpl_ids))	-- yuk
		    (mkHsDictLet lhs_binds lhs') fv_lhs
		    (mkHsDictLet rhs_binds rhs') fv_rhs)

tcRuleBndrs :: [RuleBndr Name] -> ([Id] -> TcM a) -> TcM a
tcRuleBndrs [] thing_inside = thing_inside []
tcRuleBndrs (RuleBndr var : vars) thing_inside
  = do 	{ ty <- newFlexiTyVarTy openTypeKind
	; let id = mkLocalId (unLoc var) ty
	; tcExtendIdEnv [id] $
	  tcRuleBndrs vars (\ids -> thing_inside (id:ids)) }
tcRuleBndrs (RuleBndrSig var rn_ty : vars) thing_inside
--  e.g 	x :: a->a
--  The tyvar 'a' is brought into scope first, just as if you'd written
--		a::*, x :: a->a
  = do	{ let ctxt = FunSigCtxt (unLoc var)
	; (tyvars, ty) <- tcHsPatSigType ctxt rn_ty
	; let skol_tvs = tcSkolSigTyVars (SigSkol ctxt) tyvars
	      id_ty = substTyWith tyvars (mkTyVarTys skol_tvs) ty
	      id = mkLocalId (unLoc var) id_ty
	; tcExtendTyVarEnv skol_tvs $
	  tcExtendIdEnv [id] $
	  tcRuleBndrs vars (\ids -> thing_inside (id:ids)) }

ruleCtxt :: FastString -> SDoc
ruleCtxt name = ptext (sLit "When checking the transformation rule") <+> 
		doubleQuotes (ftext name)
\end{code}




