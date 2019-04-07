#include "zfc.h"

//Redo of everything  using E internal methods rather than printing to file (slow)

long compute_schemas_tform(ProofControl_p control, TB_p bank, OCB_p ocb, Clause_p clause,
			  ClauseSet_p store, VarBank_p
              freshvars, ProofState_p state) 
{
	if (clause->properties == CPIsSchema)
	{
		printf("\nSelected schema instance\n");
	}
	
	long numfreevars = 0;
	long res = 0;
	TFormula_p clauseasformula;
	TFormula_p schemaformula = NULL;
	PTree_p freevars = NULL;
	PStack_p varstack = PStackAlloc();
	ClauseSet_p final = ClauseSetAlloc();
	Clause_p tobeevaluated;
	Clause_p clausecopy = ClauseCopy(clause,bank);
	
	clauseasformula = TFormulaClauseEncode(bank, clausecopy);
	VarBankVarsSetProp(bank->vars, TPIsFreeVar);
	TFormulaCollectFreeVars(bank, clauseasformula, &freevars);
	PTreeToPStack(varstack,freevars);
	numfreevars = PTreeNodes(freevars);
	PTreeFree(freevars);
	
	if (numfreevars == 1)  //Comprehension
	{
		WFormula_p schemaaswformula;
		schemaformula = tformula_comprehension(bank, state, varstack, clauseasformula);
		TBInsert(bank,schemaformula,DEREF_NEVER);
		schemaaswformula = WTFormulaAlloc(bank,schemaformula);
		WFormulaPushDerivation(schemaaswformula, DCFofQuote, NULL, NULL);
		WTFormulaConjunctiveNF(schemaaswformula, bank);
		
		TFormulaToCNF(schemaaswformula, FormulaQueryType(schemaaswformula),
                        final, bank, state->freshvars);
        
		//res = WFormulaCNF(schemaaswformula,final,state->terms,state->freshvars);
		while (tobeevaluated = ClauseSetExtractFirst(final))
		{
		  tobeevaluated->properties = CPIsSchema;
		  ClauseSetInsert(state->tmp_store, tobeevaluated);
		  HCBClauseEvaluate(control->hcb, tobeevaluated);
		}
		WFormulaCellFree(schemaaswformula);
	}
	
	/*
	else if (numfreevars == 2) // Replacement
	{
		final = tformula_replacement(bank,state,final,varstack,clauseasformula,clausecopy);
		
		while (tobeevaluated = ClauseSetExtractFirst(final))
		{
		  tobeevaluated->properties = CPIsSchema;
		  ClauseSetIndexedInsertClause(state->tmp_store, tobeevaluated);
		  HCBClauseEvaluate(control->hcb, tobeevaluated);
		}
	}
	*/
	PStackFree(varstack);
	ClauseSetFree(final);
	ClauseFree(clausecopy);
	
	return 0;
}

//  Compute comprehension instance for TFormula_p with ONE free variable

WFormula_p WFormula_Comprehension(TB_p bank, ProofState_p state, PStack_p freevars, WFormula_p input)
{
   TFormula_p temp = NULL;
   temp = tformula_comprehension(bank,state,freevars,input->tformula);
   WFormula_p handle = WTFormulaAlloc(bank,temp);
   return handle;
}

TFormula_p tformula_comprehension(TB_p bank, ProofState_p state, PStack_p freevars, TFormula_p input)
{
	FunCode member = SigFindFCode(state->signature, "member");
	TFormula_p freevariable = PStackElementP(freevars,0);
	
	VarBankResetVCounts(state->freshvars);
	TFormula_p a = VarBankGetFreshVar(state->freshvars,freevariable->sort);
	TFormula_p b = VarBankGetFreshVar(state->freshvars,freevariable->sort);
	
	TFormula_p xina = TFormulaFCodeAlloc(bank,member,freevariable,a);
	TFormula_p xinb = TFormulaFCodeAlloc(bank,member,freevariable,b);
	
	Eqn_p xina_eq = EqnAlloc(xina,bank->true_term,bank,true);
	Eqn_p xinb_eq = EqnAlloc(xinb,bank->true_term,bank,true);
	
	TFormula_p xina_f = TFormulaLitAlloc(xina_eq);
	TFormula_p xinb_f = TFormulaLitAlloc(xinb_eq);
	
	//TFormula_p input2 = TFormulaCopy(bank,input);
	
	TFormula_p input_and = TFormulaFCodeAlloc(bank,bank->sig->and_code,xina_f,input);
	TFormula_p input_equiv = TFormulaFCodeAlloc(bank,bank->sig->equiv_code,xinb_f,input_and);
	TFormula_p input_q1 = TFormulaAddQuantor(bank,input_equiv,true,freevariable);
	TFormula_p input_q2 = TFormulaAddQuantor(bank,input_q1,false,b);
	TFormula_p input_q3 = TFormulaAddQuantor(bank,input_q2,true,a);
	
	EqnFree(xina_eq);
	EqnFree(xinb_eq);
	
	return input_q3;
}

ClauseSet_p tformula_replacement(TB_p bank, ProofState_p state, ClauseSet_p final, PStack_p freevars, TFormula_p input, Clause_p clause)
{
	FunCode member = SigFindFCode(state->signature, "member");
	
	TFormula_p x = PStackElementP(freevars,0);
	TFormula_p y = PStackElementP(freevars,1);
	
	TFormula_p temp1 = TFormulaCopy(bank,input);
	
	VarBankResetVCounts(state->freshvars);
	TFormula_p a = VarBankGetFreshVar(state->freshvars,x->sort);
	TFormula_p b = VarBankGetFreshVar(state->freshvars,x->sort);
	
	TFormula_p c = VarBankGetFreshVar(state->freshvars,x->sort);
	
	Clause_p substitutedclause = ClauseMergeVars(clause, bank, y, c);
	
	TFormula_p phi2 = TFormulaClauseEncode(bank, substitutedclause);
	
	TFormula_p xina = TFormulaFCodeAlloc(bank,member,x,a);
	Eqn_p xina_eq = EqnAlloc(xina,bank->true_term,bank,true);
	TFormula_p xina_f = TFormulaLitAlloc(xina_eq);
	EqnFree(xina_eq);
	
	TFormula_p temp2 = TFormulaFCodeAlloc(bank,bank->sig->and_code,xina_f,temp1);
	TFormula_p temp3 = TFormulaAddQuantor(bank,temp2,false,a);
	
	TFormula_p yinb = TFormulaFCodeAlloc(bank,member,y,b);
	Eqn_p yinb_eq = EqnAlloc(yinb,bank->true_term,bank,true);
	TFormula_p yinb_f = TFormulaLitAlloc(yinb_eq);
	EqnFree(yinb_eq);
	
	TFormula_p temp4 = TFormulaFCodeAlloc(bank,bank->sig->equiv_code,yinb_f,temp3);
	TFormula_p temp5 = TFormulaAddQuantor(bank,temp4,true,y);
	TFormula_p temp6 = TFormulaAddQuantor(bank,temp5,false,b);
	TFormula_p temp7 = TFormulaAddQuantor(bank,temp6,true,a);
	
	TFormula_p yeqc = TFormulaFCodeAlloc(bank,bank->sig->eqn_code,y,c);
	
	TFormula_p phi3 = TFormulaFCodeAlloc(bank,bank->sig->equiv_code,phi2,yeqc);
	TFormula_p phi4 = TFormulaAddQuantor(bank,phi3,true,c);
	TFormula_p phi5 = TFormulaAddQuantor(bank,phi4,false,y);
	TFormula_p phi6 = TFormulaAddQuantor(bank,phi5,true,x);
	
	TFormula_p temp8 = TFormulaFCodeAlloc(bank,bank->sig->impl_code,phi6,temp7);
	
	WFormula_p schemaaswformula = WTFormulaAlloc(bank,temp8);
	
	long res = WFormulaCNF(schemaaswformula,final,state->terms,state->freshvars);
	
	ClauseFree(substitutedclause);
	WFormulaFree(schemaaswformula);
	
	return final;
}
/*-----------------------------------------------------------------------
//
// Function: ClauseMergeVars()
//
//   Create a copy of clause in which the two variables x and y are
//   merged, or, more exactly, every occurrence of x is replaced by
//   one in y.
//
// Global Variables: -
//
// Side Effects    : Memory operations
//
/----------------------------------------------------------------------*/


Clause_p ClauseMergeVars(Clause_p clause,  TB_p bank, Term_p x, Term_p y)
{
   Subst_p  subst = SubstAlloc();
   Clause_p new_clause;
   
   SubstAddBinding(subst, x,y);
   new_clause = ClauseCopy(clause, bank);
   SubstDelete(subst);

   return new_clause;
}

/*-----------------------------------------------------------------------
//
// Function: FormulaMergeVars()
//
//   Create a copy of formula in which the two variables x and y are
//   merged, or, more exactly, every occurrence of x is replaced by
//   one in y.
//
// Global Variables: -
//
// Side Effects    : Memory operations
//
/----------------------------------------------------------------------*/


WFormula_p FormulaMergeVars(WFormula_p formula,  TB_p bank, Term_p x, Term_p y)
{
   Subst_p  subst = SubstAlloc();
   Clause_p new_clause;
   WFormula_p new_formula;
   TFormula_p new_tform;
   
   SubstAddBinding(subst, x,y);
   new_tform = TBInsertNoProps(bank, formula->tformula, DEREF_ALWAYS);
   new_formula = WTFormulaAlloc(bank,new_tform);
   SubstDelete(subst);

   return new_formula;
}
