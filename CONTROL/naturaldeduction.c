#include "naturaldeduction.h"

/*  Forward Declarations
 * 
*/

/*  Internal functions
 * 
 * 
 * 
*/

void ProofTest(Tableau_p ndcontrol)
{
   printf("\n");
   TFormulaTPTPPrint(GlobalOut,ndcontrol->terms,ndcontrol->nd_generated->anchor->succ->tformula->args[0],true,true);
   printf("\n");
   TFormulaTPTPPrint(GlobalOut,ndcontrol->terms,ndcontrol->nd_generated->anchor->succ->tformula->args[1],true,true);
   
   //PStack_p variables = PStackAlloc();
   WFormula_p goal = ndcontrol->nd_generated->anchor->succ;
   WFormula_p start = WTFormulaAlloc(ndcontrol->terms,ndcontrol->nd_generated->anchor->succ->tformula->args[0]);
   //nd_collect_subterms(ndcontrol,ndcontrol->signature,start->tformula,variables);
   //Term_p x = PStackPopP(variables);
   //printf("\n");
   //TermPrint(GlobalOut,x,ndcontrol->signature,true);
   Term_p y1 = VarBankGetFreshVar(ndcontrol->terms->vars,STIndividuals);
   WFormula_p f1 = TableauUniversalElimination(ndcontrol,ndcontrol->terms,start,y1);
   WFormula_p f2 = TableauAndElimination(ndcontrol,ndcontrol->terms,f1,0);
   Term_p x = VarBankGetFreshVar(ndcontrol->terms->vars,STIndividuals);
   WFormula_p f3 = TableauUniversalIntroduction(ndcontrol,ndcontrol->terms,y1,x,f2);
   Term_p y2 = VarBankGetFreshVar(ndcontrol->terms->vars,STIndividuals);
   WFormula_p f4 = TableauUniversalElimination(ndcontrol,ndcontrol->terms,start,y2);
   WFormula_p f5 = TableauAndElimination(ndcontrol,ndcontrol->terms,f4,1);
   WFormula_p f6 = TableauUniversalIntroduction(ndcontrol,ndcontrol->terms,y2,x,f5);
   WFormula_p f7 = TableauAndIntroduction(ndcontrol,ndcontrol->terms,f3,f6);
   WFormula_p f8 = TableauImplIntroduction(ndcontrol,ndcontrol->terms,start,f7);
   
   TFormula_p var_renamed = f8->tformula;
   var_renamed = TFormulaVarRename(ndcontrol->terms,var_renamed);
   WFormula_p f_renamed = WTFormulaAlloc(ndcontrol->terms,var_renamed);
   
   printf("\nstart: \n");
   WFormulaPrint(GlobalOut,start,true);
   printf("\nf1: \n");
   WFormulaPrint(GlobalOut,f1,true);
   printf("\nf2: \n");
   WFormulaPrint(GlobalOut,f2,true);
   printf("\nf3: \n");
   WFormulaPrint(GlobalOut,f3,true);
   printf("\nf4: \n");
   WFormulaPrint(GlobalOut,f4,true);
   printf("\nf5: \n");
   WFormulaPrint(GlobalOut,f5,true);
   printf("\nf6: \n");
   WFormulaPrint(GlobalOut,f6,true);
   printf("\nf7: \n");
   WFormulaPrint(GlobalOut,f7,true);
   printf("\nf8: \n");
   WFormulaPrint(GlobalOut,f8,true);
   
   printf("\nResult: \n");
   WFormulaPrint(GlobalOut,f_renamed,true);
   printf("\nGoal: \n");
   WFormulaPrint(GlobalOut,goal,true);
   Subst_p subst = SubstAlloc();
   //bool success = SubstComputeMatch(f_renamed,goal,temp_subst);
   //bool success_2 = SubstComputeMgu(f_renamed,goal,temp_subst);
   
   bool success = TableauUnify(ndcontrol,subst,f_renamed->tformula,goal->tformula);
   //bool success_2 = TableauUnify(ndcontrol,subst,f8->tformula,f7->tformula);
   
   //printf("\nsuccess: %d success2: %d\n",success,success_2);
   printf("\nsuccess: %d\n",success);

}

/*  Unification algorithm from Handbook of Automated Reasoning p. 454
 * 
 *  Warning:  May damage the dag structure of terms
*/


bool TableauUnify(Tableau_p control, Subst_p subst, Term_p s, Term_p t)
{
	if (TermIsVar(s))
	{
		s = TermCopy(s,control->terms->vars,DEREF_NEVER);
	}
	if (TermIsVar(t))
	{
		t = TermCopy(t,control->terms->vars,DEREF_NEVER);
	}
	if (TermIsVar(s) && TermStructEqual(s,t))
	{
		// do nothing
	}
	else if (!TermIsVar(s) && !TermIsVar(t))
	{
		if (s->f_code == t->f_code)
		{
			int arity = (s->arity > t->arity) ? t->arity : s->arity;
			for (int i=0; i<arity; i++)
			{
				bool temp1 = TableauUnify(control, subst, s->args[i],t->args[i]);
				if (!temp1) 
				{
					//printf("\ntemp1 fail\n");
					return false;
				}
			}
		}
		else
		{
			return false;
		}
	}
	else if (!TermIsVar(s))
	{
		bool temp2 = TableauUnify(control,subst,t,s);
		if (!temp2)
		{ 
			//printf("\ntemp2 fail\n");
			return false;
		}
	}
	else if (TBTermIsSubterm(t,s))
	{
		//printf("\nsubterm fail\n");
		return false;
	}
	else
	{
		SubstAddBinding(subst,s,t);
	}
	return true;
}

/*  Collect subterms using the style of the nd_label method, reducing the number
 *  of formulas that need to be labelled.
 *  
 * 
*/

long nd_collect_subterms2(Tableau_p control, Sig_p sig, Term_p term, PStack_p collector)
{
	//printf("\nlabelling: ");
	//TermPrint(GlobalOut,term,sig,DEREF_NEVER);
	//printf("\n");
	long res = 0;
	if (term->arity == 0)
	{
		printf("\n");
		PStackPushP(collector,term);
		res += 1;
	}
	else if (term->f_code > 0)
	{
		if (term->arity == 2 && ((term->args[0]->f_code == SigFindFCode(sig,"$true"))
					|| (term->args[1]->f_code == SigFindFCode(sig,"$true"))
					|| (term->args[0]->f_code == SigFindFCode(sig,"$false"))
					|| (term->args[1]->f_code == SigFindFCode(sig,"$false"))))
		{
			for (int i=0; i<term->args[0]->arity; i++)
			{
				if (term->args[0]->args[i]->arity > 0)
				{
					res += nd_collect_subterms2(control,sig,term->args[0]->args[i],collector);
				}
			}
		}
		else if ((term->f_code == sig->not_code) || (term->f_code == sig->or_code)
												 || (term->f_code == sig->qall_code)
												 || (term->f_code == sig->qex_code)
												 || (term->f_code == sig->impl_code)
												 || (term->f_code == sig->equiv_code)
												 || (term->f_code == sig->and_code)
												 || (term->f_code == sig ->eqn_code)
												 || (term->f_code == sig->neqn_code))
		{
			for (int i=0; i<term->arity; i++)
			{
				if (term->args[i]->arity > 0)
				{
					res += nd_collect_subterms2(control,sig,term->args[i],collector);
				}
			}
		}
		else if (term->arity >= 0)
		{
			//printf("\nfound a function symbol\n");
			PStackPushP(collector,term);
			TermPrint(GlobalOut,term,sig,DEREF_NEVER);
			for (int i=0; i<term->arity; i++)
			{
				if (term->args[i]->arity > 0)
				{
					res += nd_collect_subterms2(control,sig,term->args[i],collector);
				}
			}
		}
	}
	else
	{
		PStackPushP(collector,term);
		printf("\n");
		TermPrint(GlobalOut,term,sig,DEREF_NEVER);
		res += 1;
	}
	return res;
}

/*
 *  Update the control symbols of all formulas in formulaset target
 * 
 * 
*/



void FormulaSetUpdateControlSymbols(Tableau_p control, FormulaSet_p target)
{
	WFormula_p handle = target->anchor->succ;
	//printf("\nLabelling formulas... %ld of them\n",target->members);
	while (handle!= target->anchor)
	{
		//TFormula_p temporary = TermCopyKeepVars(handle->tformula,DEREF_NEVER);
		//TFormula_p temporary = TermCopy(handle->tformula,control->terms->vars,false);
		//printf("\nf_code: %ld\n",handle->tformula->f_code);
		//printf("\nf_code: %%\n",SigFindName(control->signature,handle->tformula->f_code));
		//printf("\n");
		//WFormulaPrint(GlobalOut,handle,true);
		//nd_label_symbols(control,temporary);
		nd_label_symbols(control,handle->tformula);
		//TermFree(temporary);
		handle = handle->succ;
	}
	//printf("\nUpdating control symbols...");
	UpdateControlSymbols(control);
}

//TableauSaturateLoop is a test method for checking how the inference rules work when applied multiple times

void TableauSaturateLoop(Tableau_p ndcontrol, long loops)
{
   WFormula_p handle;
   long i;
   FormulaSetUpdateControlSymbols(ndcontrol,ndcontrol->nd_generated);
   for (i=0;i<loops;i++)
   {
	   handle = ndcontrol->nd_generated->anchor->succ;
	   printf("\nnew loop through generated");
	   while(handle!=ndcontrol->nd_generated->anchor)
	   {
		  printf("\n");
		  WFormulaPrint(GlobalOut,handle,true);
		  printf("\n");
		  
		  TableauAndIntProcess(ndcontrol,ndcontrol->terms,handle);
		  TableauOrIntProcess(ndcontrol,ndcontrol->terms,handle);
		  TableauImplIntProcess(ndcontrol,ndcontrol->terms,handle);
		  TableauNegIntProcess(ndcontrol,ndcontrol->terms,handle);
		  TableauUniversalIntProcess(ndcontrol,ndcontrol->terms,handle);
		  TableauExistentialIntProcess(ndcontrol,ndcontrol->terms,handle);
		  TableauOrElimProcess(ndcontrol,ndcontrol->terms,handle);
		  TableauAndElimProcess(ndcontrol,ndcontrol->terms,handle);
		  TableauImplElimProcess(ndcontrol,ndcontrol->terms,handle);
		  TableauNegElimProcess(ndcontrol,ndcontrol->terms,handle);
		  // universal and existential elimination process needs to be included

		  handle = handle->succ;
		  
	   }
	   //printf("\nupdating control symbols...");
	   //FormulaSetUpdateControlSymbols(ndcontrol,ndcontrol->nd_temporary_formulas);
	   printf("\ndumping %ld previous formulas...",ndcontrol->nd_generated->members);
	   FormulaSetFreeFormulas(ndcontrol->nd_generated);
	   printf("\ninserting %ld temporary formulas...",ndcontrol->nd_temporary_formulas->members);
	   FormulaSetInsertSet(ndcontrol->nd_generated,ndcontrol->nd_temporary_formulas);
   }
}

/*  Generate the possible inferences with handle and the generated formulas
 * 
 * 
*/

void TableauGenerateAndScoreFormulas(Tableau_p ndcontrol,WFormula_p handle)
{
	//printf("\n generating formulas for: ");
	//WFormulaPrint(GlobalOut,handle,true);
	//printf("\n");
	TableauAndIntProcess(ndcontrol,ndcontrol->terms,handle);
	TableauOrIntProcess(ndcontrol,ndcontrol->terms,handle);
	TableauImplIntProcess(ndcontrol,ndcontrol->terms,handle);
	TableauNegIntProcess(ndcontrol,ndcontrol->terms,handle);
	TableauUniversalIntProcess(ndcontrol,ndcontrol->terms,handle);
	TableauExistentialIntProcess(ndcontrol,ndcontrol->terms,handle);
	TableauOrElimProcess(ndcontrol,ndcontrol->terms,handle);
	TableauAndElimProcess(ndcontrol,ndcontrol->terms,handle);
	TableauImplElimProcess(ndcontrol,ndcontrol->terms,handle);
	TableauNegElimProcess(ndcontrol,ndcontrol->terms,handle);
	TableauUniversalElimProcess(ndcontrol,ndcontrol->terms,handle);
	TableauExistentialElimProcess(ndcontrol,ndcontrol->terms,handle);
	
	//TableauEqualityEliminationProcess(ndcontrol,ndcontrol->terms,handle);
	
	//printf("\ndumping %ld previous formulas...",ndcontrol->nd_generated->members);
	//FormulaSetFreeFormulas(ndcontrol->nd_generated);
	//printf("\ninserting %ld temporary formulas...",ndcontrol->nd_temporary_formulas->members);
	FormulaSetUpdateControlSymbols(ndcontrol,ndcontrol->nd_temporary_formulas);
	FormulaSetInsertSet(ndcontrol->nd_generated,ndcontrol->nd_temporary_formulas);
}

void TableauGenerateAndScoreFormulasSkeleton(Tableau_p ndcontrol,WFormula_p handle)
{
	
	TableauAndIntProcess(ndcontrol,ndcontrol->terms,handle);
	TableauOrIntProcess(ndcontrol,ndcontrol->terms,handle);
	TableauImplIntProcess(ndcontrol,ndcontrol->terms,handle);
	TableauNegIntProcess(ndcontrol,ndcontrol->terms,handle);
	TableauUniversalIntProcess(ndcontrol,ndcontrol->terms,handle);
	TableauExistentialIntProcess(ndcontrol,ndcontrol->terms,handle);
	TableauOrElimProcess(ndcontrol,ndcontrol->terms,handle);
	TableauAndElimProcess(ndcontrol,ndcontrol->terms,handle);
	TableauImplElimProcess(ndcontrol,ndcontrol->terms,handle);
	TableauNegElimProcess(ndcontrol,ndcontrol->terms,handle);
	TableauUniversalElimProcess(ndcontrol,ndcontrol->terms,handle);
	TableauExistentialElimProcess(ndcontrol,ndcontrol->terms,handle);
	
	//printf("\ndumping %ld previous formulas...",ndcontrol->nd_generated->members);
	//FormulaSetFreeFormulas(ndcontrol->nd_generated);
	//printf("\ninserting %ld temporary formulas...",ndcontrol->nd_temporary_formulas->members);
	if (ndcontrol->nd_temporary_formulas->members == 0)
	{
		//printf("\nno generated formulas\n");
		exit(0);
	}
	FormulaSetUpdateControlSymbols(ndcontrol,ndcontrol->nd_temporary_formulas);
	FormulaSetInsertSet(ndcontrol->nd_generated,ndcontrol->nd_temporary_formulas);
}

/*  Push the elements of source to target, unless they are skip
 * 
 * 
*/

void pstack_push_skip(PStack_p target, PStack_p source, Term_p skip)
{
	
   PStackPointer i;

   for(i=0; i<PStackGetSP(source); i++)
   {
	  Term_p handle = PStackElementP(source,i);
	  if (TermStructEqual(handle,skip))
	  {
		  continue;
	  }
      push(target, PStackElement(source,i));
   }
}

long nd_label_symbols(Tableau_p control,Term_p term)
{
	Sig_p sig = control->signature;

	if (term->arity == 2 && ((term->args[0]->f_code == SIG_TRUE_CODE)
				|| (term->args[1]->f_code == SIG_TRUE_CODE)
				|| (term->args[0]->f_code == SIG_FALSE_CODE)
				|| (term->args[1]->f_code == SIG_FALSE_CODE)))
	{
		//printf("\nfound a predicate\n");
		PStackPushInt(control->predicates,term->args[0]->f_code);
		for (int i=0; i<term->args[0]->arity; i++)
		{
			if (term->args[0]->args[i]->arity > 0)
			{
				nd_label_symbols(control,term->args[0]->args[i]);
			}
		}
	}
	else if (term->f_code == sig->eqn_code || term->f_code == sig->neqn_code)
	{
		//printf("\nfound equality\n");
		PStackPushInt(control->predicates,term->f_code);
		for (int i=0; i<term->arity; i++)
		{
			if (term->args[i]->arity > 0)
			{
				nd_label_symbols(control,term->args[i]);
			}
		}
	}
	else if ((term->f_code == sig->not_code) || (term->f_code == sig->or_code)
											 || (term->f_code == sig->qall_code)
											 || (term->f_code == sig->qex_code)
											 || (term->f_code == sig->impl_code)
											 || (term->f_code == sig->equiv_code)
											 || (term->f_code == sig->and_code)
											 || (term->f_code == sig->bimpl_code))
	{
		//printf("\nfound a boolean\n");
		for (int i=0; i<term->arity; i++)
		{
			if (term->args[i]->arity > 0)
			{
				nd_label_symbols(control,term->args[i]);
			}
		}
	}
	else if (term->arity >= 0)
	{
		//printf("\nfound a function symbol\n");
		PStackPushInt(control->functions,term->f_code);
		for (int i=0; i<term->arity; i++)
		{
			if (term->args[i]->arity > 0)
			{
				nd_label_symbols(control,term->args[i]);
			}
		}
	}
	return 0;
}

long nd_collect_subterms(Tableau_p control, Sig_p sig, Term_p term, PStack_p collector)
{
	long res = 0;
	if (term->f_code > 0)
	{
		if (FunCodeIsFunction(control,term->f_code))
		{
			res += 1;
			PStackPushP(collector,term);
		}
	}
	else
	{
		res += 1;
		PStackPushP(collector,term);
	}
	for (int i=0; i<term->arity;i++)
	{
		res += nd_collect_subterms(control,sig,term->args[i],collector);
	}
	return res;
}

/*  Externally declared functions
 *  
 * 
 * 
*/

Tableau_p TableauAlloc(ProofState_p initial)
{
	Tableau_p handle = TableauCellAlloc();
	handle->derivation = PStackAlloc();
	handle->absolutely_flagged_variables = PStackAlloc();
	handle->relatively_flagged_variables = PStackAlloc();
	handle->predicates = PStackAlloc();
	handle->functions = PStackAlloc();
	handle->nd_derivation = FormulaSetAlloc();
	handle->nd_generated = FormulaSetAlloc();
	handle->nd_temporary_formulas = FormulaSetAlloc();
	handle->generated_formulas = 0;
	handle->signature = initial->signature;
	handle->terms = initial->terms;
	handle->freshvars = initial->freshvars;
	handle->goal = NULL;
	handle->last_assumption = NULL;
	handle->active = true;
	//handle->last_assumption_branch = NULL;
	//handle->master = handle;
	return handle;
}

void TableauFree(Tableau_p initial)
{
	PStackFree(initial->derivation);
	PStackFree(initial->absolutely_flagged_variables);
	PStackFree(initial->relatively_flagged_variables);
	PStackFree(initial->predicates);
	PStackFree(initial->functions);
	
	FormulaSetFree(initial->nd_derivation);
	FormulaSetFree(initial->nd_generated);
	FormulaSetFree(initial->nd_temporary_formulas);
	//WFormulaFree(initial->goal);
	TableauCellFree(initial);
}

Tableau_p TableauAllocAssumption(Tableau_p initial)
{
	Tableau_p handle = TableauCellAlloc();
	handle->last_assumption = NULL;
	//handle->derivation = PStackAlloc();  // leaking?
	handle->absolutely_flagged_variables = initial->absolutely_flagged_variables;
	handle->relatively_flagged_variables = initial->relatively_flagged_variables;
	handle->predicates = PStackAlloc();
	handle->functions = PStackAlloc();
	handle->nd_derivation = FormulaSetAlloc(); //alloc
	FormulaSetCopyFormulas(handle->nd_derivation,initial->nd_derivation);
	handle->nd_generated = FormulaSetAlloc(); //alloc
	handle->nd_temporary_formulas = FormulaSetAlloc();  // alloc
	handle->branch_formulas = FormulaSetAlloc(); //alloc
	handle->generated_formulas = 0;
	handle->signature = initial->signature;
	handle->terms = initial->terms;
	handle->freshvars = initial->freshvars;
	handle->goal = NULL;
	handle->derivation = NULL;
	handle->active = true;
	//handle->last_assumption_branch = NULL;
	//handle->master = initial->master;
	//TableauSetInsert(initial->set,handle);
	return handle;
}

void TableauAssumptionControlFree(Tableau_p initial)
{
	//FormulaSetFreeFormulas(initial->nd_derivation);
	//FormulaSetFreeFormulas(initial->nd_generated);
	//FormulaSetFreeFormulas(initial->nd_temporary_formulas);
	//WFormulaFree(initial->goal);
	//PStackFree(initial->derivation);
	PStackFree(initial->predicates);
	PStackFree(initial->functions);
	FormulaSetFree(initial->nd_derivation);
	FormulaSetFree(initial->nd_generated);
	FormulaSetFree(initial->nd_temporary_formulas);
	FormulaSetFree(initial->branch_formulas);
	TableauCellFree(initial);
	//WFormulaFree(initial->last_assumption);
}

void TableauCloseAssumption(Tableau_p initial)
{
	//FormulaSetFreeFormulas(initial->nd_derivation);
	//FormulaSetFreeFormulas(initial->nd_generated);
	//FormulaSetFreeFormulas(initial->nd_temporary_formulas);
	//WFormulaFree(initial->goal);
	//PStackFree(initial->derivation);
	PStackFree(initial->predicates);
	PStackFree(initial->functions);
	FormulaSetFree(initial->nd_derivation);
	FormulaSetFree(initial->nd_generated);
	FormulaSetFree(initial->nd_temporary_formulas);
	initial->active = false;
	//TableauFree(initial);
	//WFormulaFree(initial->last_assumption);
}

WFormula_p TableauAndIntroduction(Tableau_p control,TB_p bank, WFormula_p a, WFormula_p b)
{
	TFormula_p a_tform = a->tformula;
	TFormula_p b_tform = b->tformula;
	if (!a_tform || !b_tform)
	{
		return NULL;
	}
	TFormula_p a_and_b = TFormulaFCodeAlloc(bank,bank->sig->and_code,a_tform,b_tform);
	WFormula_p handle = WTFormulaAlloc(bank,a_and_b);
	return handle;
}

WFormula_p TableauOrIntroduction(Tableau_p control,TB_p bank, WFormula_p a, WFormula_p b)
{
	TFormula_p a_tform = a->tformula;
	TFormula_p b_tform = b->tformula;
	TFormula_p a_or_b = TFormulaFCodeAlloc(bank,bank->sig->or_code,a_tform,b_tform);
	WFormula_p handle = WTFormulaAlloc(bank,a_or_b);
	return handle;
}

/*  a must be the most recent non discarded assumption occuring in the proof
 * 
 * 
*/

WFormula_p TableauImplIntroduction(Tableau_p control,TB_p bank, WFormula_p a, WFormula_p b)
{
	TFormula_p a_tform = a->tformula;
	TFormula_p b_tform = b->tformula;
	TFormula_p a_impl_b = TFormulaFCodeAlloc(bank,bank->sig->impl_code,a_tform,b_tform);
	WFormula_p handle = WTFormulaAlloc(bank,a_impl_b);
	return handle;
}

/*  Return NULL if invalid
 *  c must be the most recent non discarded assumption occuring in the proof
 * 
 * 
*/

WFormula_p TableauNegIntroduction(Tableau_p control,TB_p bank, WFormula_p a, WFormula_p b, WFormula_p c)
{
	if (!a || !b || !c)
	{
		return NULL;
	}
	TFormula_p a_tform = a->tformula;
	TFormula_p b_tform = b->tformula;
	TFormula_p c_tform = c->tformula;
	TFormula_p a_neg = TFormulaFCodeAlloc(bank,bank->sig->not_code,a_tform,NULL);
	TFormula_p b_neg = TFormulaFCodeAlloc(bank,bank->sig->not_code,b_tform,NULL);

	WFormula_p handle = NULL;
	
	Subst_p subst1 = SubstAlloc();  // leaking??
	Subst_p subst2 = SubstAlloc();  // leaking??
	if (TableauUnify(control,subst1,a_tform,b_neg) || TableauUnify(control,subst2,a_neg,b_tform))
	{
		TFormula_p c_neg = TFormulaFCodeAlloc(bank,bank->sig->not_code,c_tform,NULL);
		handle = WTFormulaAlloc(bank,c_neg);
	}
	SubstDelete(subst1);
	SubstDelete(subst2);
	
	return handle;
}

/*  Does not check if the Tableau rule is allowed!!!  Only does it if physically possible
 *  Return NULL if term is not a subterm of the formula
 *  Replaces term with variable, absolutely flags term
 *  Absolutely and relatively flags variables
*/

WFormula_p TableauUniversalIntroduction(Tableau_p control,TB_p bank, Term_p term, Term_p variable, WFormula_p formula)
{
	
	TFormula_p handle = formula->tformula;
	TFormula_p new_tform,qall_new_tform;
	WFormula_p qall_new_form;
	
	if (!TermIsSubterm(handle,term,DEREF_NEVER))
	{
		//printf("term not subterm\n");
		return NULL; //term is not a subterm of the formula
	}
	// Check this....
	//if (TableauTermIsAbsolutelyFlagged(control,variable) || TableauTermIsAbsolutelyFlagged(control,term))
	if (TableauTermIsAbsolutelyFlagged(control,term))
	{
		//printf("flagging error\n");
		return NULL; //do not universally quantify over symbols affected by some rules
	}
	
	PTree_p free_variables = NULL;
	PStack_p free_stack = PStackAlloc();
	TFormulaCollectFreeVars(bank, formula->tformula, &free_variables);
	PTreeToPStack(free_stack,free_variables);
	
	// push parameters to relatively flagged variables
	pstack_push_skip(control->relatively_flagged_variables,free_stack,term);
	// push variable being introduced to absolutely flagged variables
	PStackPushP(control->absolutely_flagged_variables,term);
	
	//printf("\nUniversalIntroductionTest\n");
	//WFormulaPrint(GlobalOut,formula,true);
	//printf("\nfreshvariable: ");
	//TermPrint(GlobalOut,variable,control->signature,DEREF_NEVER);
	//printf("\nterm: ");
	//TermPrint(GlobalOut,term,control->signature,DEREF_NEVER);
	//printf("\n");

	new_tform = TFormulaMergeVars(formula,bank,term,variable);
	
	//printf("replaced\n");
	//TFormulaTPTPPrint(GlobalOut,bank,new_tform,true,true);
	
	if (!new_tform)
	{
		return NULL;
	}
	
	qall_new_tform = TFormulaQuantorAlloc(bank,bank->sig->qall_code,variable,new_tform);
	qall_new_form = WTFormulaAlloc(bank,qall_new_tform);
	
	PStackFree(free_stack);
	PTreeFree(free_variables);
	return qall_new_form;
	
}

WFormula_p TableauExistentialIntroduction(Tableau_p control,TB_p bank, Term_p term, Term_p variable, WFormula_p formula)
{
	TFormula_p handle = formula->tformula;
	TFormula_p new_tform,qex_new_tform;
	WFormula_p qex_new_form;
	
	if (!TermIsSubterm(handle,term,DEREF_NEVER))
	{
		return NULL; //term is not a subterm of the formula
	}
	
	new_tform = TFormulaMergeVars(formula,bank,term,variable);
	
	if (!new_tform)
	{
		return NULL;
	}
	
	qex_new_tform = TFormulaQuantorAlloc(bank,bank->sig->qex_code,variable,new_tform);
	qex_new_form = WTFormulaAlloc(bank,qex_new_tform);
	
	return qex_new_form;
	
}

/* conjunct is A & B, select = 0 returns A, select = 0 returns B.
 * Return NULL if conjunct is not actually a conjunct
 * 
*/

// CHECK THIS

WFormula_p TableauAndElimination(Tableau_p control,TB_p bank, WFormula_p conjunct, int select)
{
	assert(select==0 || select==1);
	WFormula_p target;
	TFormula_p tform;
	if (conjunct->tformula->f_code != bank->sig->and_code)
	{
		return NULL;
	}
	tform = conjunct->tformula->args[select];
	target = WTFormulaAlloc(bank,tform);
	return target;
}

/*  Checks for which one should be disjunct and which is negated
 *  If invalid formulae are passed, return NULL
 * 
 * 
*/

WFormula_p TableauOrElimination(Tableau_p control,TB_p bank, WFormula_p a,WFormula_p b)
{
	WFormula_p disjunct,negated,target;
	TFormula_p tform,unnegated;
	if (a->tformula->f_code == bank->sig->or_code)
	{
		disjunct = a;
		negated = b;
		unnegated = b->tformula->args[0];
		if (negated->tformula->f_code != bank->sig->not_code)
		{
			return NULL;
		}
		if (TermStructEqual(unnegated,disjunct->tformula->args[0]))
		{
			tform = negated->tformula->args[1];
			target = WTFormulaAlloc(bank,tform);
			return target;	
		}
		else if (TermStructEqual(unnegated,disjunct->tformula->args[1]))
		{
			tform = negated->tformula->args[0];
			target = WTFormulaAlloc(bank,tform);
			return target;	
		}
		return NULL;
	}
	else if (b->tformula->f_code == bank->sig->or_code)
	{
		disjunct = b;
		negated = a;
		unnegated = a->tformula->args[0];
		if (negated->tformula->f_code != bank->sig->not_code)
		{
			return NULL;
		}
		if (TermStructEqual(unnegated,disjunct->tformula->args[0]))
		{
			tform = negated->tformula->args[1];
			target = WTFormulaAlloc(bank,tform);
			return target;	
		}
		else if (TermStructEqual(unnegated,disjunct->tformula->args[1]))
		{
			tform = negated->tformula->args[0];
			target = WTFormulaAlloc(bank,tform);
			return target;	
		}
		return NULL;
	}
	return NULL;
}

/* As TableauOrElimination
 * 
 * 
 * 
 * 
*/

WFormula_p TableauImplElimination(Tableau_p control,TB_p bank, WFormula_p a,WFormula_p b)
{
	WFormula_p sequent,assumption,target;
	TFormula_p tform;
	if (a->tformula->f_code == bank->sig->impl_code)
	{
		sequent = a;
		assumption = b;
		if (assumption->tformula->f_code != bank->sig->not_code)
		{
			return NULL;
		}
		if (TermStructEqual(assumption->tformula,sequent->tformula->args[0]))
		{
			tform = sequent->tformula->args[1];
			target = WTFormulaAlloc(bank,tform);
			return target;	
		}
		return NULL;
	}
	else if (b->tformula->f_code == bank->sig->impl_code)
	{
		sequent = b;
		assumption = a;
		if (assumption->tformula->f_code != bank->sig->not_code)
		{
			return NULL;
		}
		if (TermStructEqual(assumption->tformula,sequent->tformula->args[0]))
		{
			tform = sequent->tformula->args[1];
			target = WTFormulaAlloc(bank,tform);
			return target;	
		}
		return NULL;
	}
	return NULL;
}

/*  Negation elimination
 *  
 * 
 * 
 * 
*/

WFormula_p TableauNegationElimination(Tableau_p control,TB_p bank, WFormula_p a)
{
	TFormula_p interior;
	WFormula_p handle;
	if (a->tformula->f_code != bank->sig->not_code)
	{
		return NULL;
	}
	if (a->tformula->args[0]->f_code != bank->sig->not_code)
	{
		return NULL;
	}
	interior = a->tformula->args[0]->args[0];
	handle = WTFormulaAlloc(bank,interior);
	return handle;
}

/*  Universal Elimination
 * 
 *   w_matrix??? fix
 * 
*/

WFormula_p TableauUniversalElimination(Tableau_p control,TB_p bank, WFormula_p a, Term_p substitute)
{
	WFormula_p w_matrix,target;
	TFormula_p matrix;
	Term_p bound_variable;
	if (a->tformula->f_code != bank->sig->qall_code)
	{
		return NULL;
	}
	bound_variable = a->tformula->args[0];
	matrix = a->tformula->args[1];
	w_matrix = WTFormulaAlloc(bank,matrix);
	target = FormulaMergeVars(w_matrix,bank,bound_variable,substitute);
	
	WFormulaFree(w_matrix);
	
	return target;
}

/*
 *   w_matrix??? fix
 *   Needs more conditions restricting the term a (substitute)
 *   This is the Quine/Jaskowski style existential elimination,
 *   and as written may be unsound due to the necessary restrictions
*/

WFormula_p TableauExistentialElimination(Tableau_p control,TB_p bank, WFormula_p a, Term_p substitute)
{
	WFormula_p w_matrix,target;
	TFormula_p matrix;
	Term_p bound_variable;
	
	if (a->tformula->f_code != bank->sig->qex_code)
	{
		return NULL;
	}
	
	//substitute = VarBankGetFreshVar(control->freshvars,control->freshvars->sort_table->default_type);
	PStack_p empty_stack = PStackAlloc();
	substitute = TermAllocNewSkolem(control->signature,empty_stack,0);
	PStackFree(empty_stack);
	
	PTree_p free_variables = NULL;
	PStack_p free_stack = PStackAlloc();
	TFormulaCollectFreeVars(bank, a->tformula, &free_variables);
	
	PTreeToPStack(free_stack,free_variables);
	//PStackPushStack(control->relatively_flagged_variables,free_stack);
	//PStackPushP(control->absolutely_flagged_variables,substitute);
	TableauRelativelyFlagTerms(control,free_stack);
	TableauAbsolutelyFlagTerm(control,substitute);
	
	
	bound_variable = a->tformula->args[0];
	matrix = a->tformula->args[1];
	w_matrix = WTFormulaAlloc(bank,matrix);
	target = FormulaMergeVars(w_matrix,bank,bound_variable,substitute);
	
	WFormulaFree(w_matrix);
	PStackFree(free_stack);
	PTreeFree(free_variables);
	return target;
}

/*  This is meant to be the Gentzen style existential elimination
 *  Reference: The Natural Deducation Pack by Alastair Carr p. 3
 *  
 *  Restrictions:  psi must follow from a discharged assumption of the form
 *  [phi(t/v)] where phi is found in our existential expression Ev phi
 * 
 *  The skolem constant in the assumption phi(t/v) cannot occur in Ev phi, psi, or any undischarged assumption in the proof, other than the one in brackets above
 * 
 *  Warning:  Do not call this method unless existential is assured to be an existential formula
 *   		  Do not call this method unless phi is the initial assumption of a closed assumption branch
 * 
*/

WFormula_p TableauExistentialElimination2(Tableau_p control,TB_p bank, WFormula_p existential, WFormula_p psi)
{
	// check that psi is conclusion of the most recent derivation, and that this derivation is founded by a formula of form phi(t/v)
	//TFormula_p existential_tformula = existential->tformula;
	//TFormula_p existential_matrix = existential_tformula->args[1];
	return psi;
}

/*  Equality Rules
 *
*/

WFormula_p TableauEqualityIntroduction(Tableau_p control, TB_p bank, Term_p term)
{
	Eqn_p equals = EqnAlloc(term,term,bank,true);
	TFormula_p equals_tf = TFormulaLitAlloc(equals);
	return WTFormulaAlloc(bank,equals_tf);
}

WFormula_p TableauEqualityEliminationLeft(Tableau_p control, TB_p bank, WFormula_p substituted, WFormula_p equality)
{
	if ((equality->tformula->f_code != bank->sig->eqn_code) || 
		(equality->tformula->args[0]->f_code == SIG_TRUE_CODE) || 
		(equality->tformula->args[1]->f_code == SIG_TRUE_CODE))
	{
		return NULL;
	}
	Term_p s = equality->tformula->args[0];
	Term_p t = equality->tformula->args[1];
	return FormulaMergeVars(substituted,bank,s,t);
}

WFormula_p TableauEqualityEliminationRight(Tableau_p control, TB_p bank, WFormula_p substituted, WFormula_p equality)
{
	if ((equality->tformula->f_code != bank->sig->eqn_code) || 
		(equality->tformula->args[0]->f_code == SIG_TRUE_CODE) || 
		(equality->tformula->args[1]->f_code == SIG_TRUE_CODE))
	{
		return NULL;
	}
	Term_p t = equality->tformula->args[0];
	Term_p s = equality->tformula->args[1];
	return FormulaMergeVars(substituted,bank,s,t);
}

long TableauEqualityEliminationProcess(Tableau_p control, TB_p bank, WFormula_p selected)
{
	FormulaSet_p target = control->nd_derivation;
	FormulaSet_p temporary_store = control->nd_temporary_formulas;
	WFormula_p handle = target->anchor->succ;
	long counter = 0;
	while (handle != target->anchor)
	{
		if (handle->tformula->f_code != bank->sig->eqn_code)
		{
			handle = handle->succ;
			continue;
		}
		WFormula_p left = TableauEqualityEliminationLeft(control,bank,selected,handle);
		WFormula_p right = TableauEqualityEliminationRight(control,bank,selected,handle);
		if (left)
		{
			FormulaSetInsert(temporary_store,left);
			counter++;
		}
		if (right)
		{
			FormulaSetInsert(temporary_store,right);
			counter++;
		}
		handle = handle->succ;
	}
	return counter;
}


/*  Make all possible and introductions with the Tableau_p and formula passed
 * 
 * 
*/

long TableauAndIntProcess(Tableau_p control,TB_p bank,WFormula_p selected)
{
	WFormula_p handle;
	FormulaSet_p target = control->nd_derivation;
	FormulaSet_p temporary_store = control->nd_temporary_formulas;
	handle = target->anchor->succ;
	long counter = 0;
	while(handle!=target->anchor)
	{
		WFormula_p generated = TableauAndIntroduction(control,bank,selected,handle);
		if (generated)
		{
			FormulaSetInsert(temporary_store,generated);
			counter++;
		}
		else 
		{
			//printf("\nnull...\n");
		}
		handle = handle->succ;
	}
	return counter;
}

long TableauOrIntProcess(Tableau_p control,TB_p bank,WFormula_p selected)
{
	WFormula_p handle;
	FormulaSet_p target = control->nd_derivation;
	FormulaSet_p temporary_store = control->nd_temporary_formulas;
	handle = target->anchor->succ;
	long counter = 0;
	while(handle!=target->anchor)
	{
		WFormula_p generated = TableauOrIntroduction(control,bank,selected,handle);
		if (generated)
		{
			FormulaSetInsert(temporary_store,generated);
			counter++;
		}
		else 
		{
			//printf("\nnull...\n");
		}
		handle = handle->succ;
	}
	return counter;
}

long TableauImplIntProcess(Tableau_p control,TB_p bank,WFormula_p selected)
{
	WFormula_p handle;
	FormulaSet_p target = control->nd_derivation;
	FormulaSet_p temporary_store = control->nd_temporary_formulas;
	handle = target->anchor->succ;
	long counter = 0;
	while(handle!=target->anchor)
	{
		WFormula_p generated = TableauImplIntroduction(control,bank,selected,handle);
		if (generated)
		{
			//printf("\n");
			//WFormulaPrint(GlobalOut,generated,true);
			FormulaSetInsert(temporary_store,generated);
			counter++;
		}
		else 
		{
			//printf("\nnull...\n");
			WFormulaFree(generated);
		}
		handle = handle->succ;
	}
	return counter;
}

/*  If a contradiction is found between selected and handle, the negation of alt_handle is 
 *  inserted to temporary store
 * 
 *  This will need to be introduced differently with assumption trees,
 *  specifically the idea that if a contradiction is found, the negation introduced should be the
 *  negation of the most recent assumption
 * 
 * Need to check that the formula alt_handle is ONLY the most recent nondiscarded assumption in the proof
*/  

long TableauNegIntProcess(Tableau_p control,TB_p bank,WFormula_p selected)
{
	WFormula_p handle,alt_handle;
	FormulaSet_p target = control->nd_derivation;
	FormulaSet_p temporary_store = control->nd_temporary_formulas;
	handle = target->anchor->succ;
	alt_handle = target->anchor->succ;
	long counter=0;
	//printf("\nNEW ITERATION\n");
	while(handle!=target->anchor)
	{
		while (alt_handle!=target->anchor)
		{
			WFormula_p generated = TableauNegIntroduction(control,bank,selected,handle,alt_handle);
			if (generated)
			{
				//WFormulaPrint(GlobalOut,generated,true);
				FormulaSetInsert(temporary_store,generated);
				counter++;
			}
			else 
			{
				//printf("\nnull...\n");
			}
			alt_handle = alt_handle->succ;
		}
		handle = handle->succ;
	}
	return counter;
}

//replace an arbitrary constant with a fresh variable
// need to adjust this for flagged variables (?)

long TableauUniversalIntProcess(Tableau_p control,TB_p bank,WFormula_p selected)
{
	if (!selected)
	{
		return 0;
	}
	FormulaSet_p temporary_store = control->nd_temporary_formulas;
	long res = 0;
	WFormula_p generated;
	Term_p constant;
	
	//printf("\NMAX VAR CODE: %ld\n",TermFindMaxVarCode(selected->tformula));
	/*
	FunCode min_code = TermFindMaxVarCode(selected->tformula);
	assert(min_code < 0);
	min_code -= 2;
	Term_p freshvariable = VarBankFCodeFind(bank->vars,min_code);
	if (!freshvariable)
	{
		//printf("allocing a\n");
		freshvariable = VarBankVarAlloc(bank->vars,min_code,control->freshvars->sort_table->default_type);
	}
	*/
	Term_p freshvariable = VarBankGetFreshVar(control->freshvars,control->freshvars->sort_table->default_type);
	PStack_p stack = PStackAlloc();
	
	nd_label_symbols(control,selected->tformula);
	UpdateControlSymbols(control);
	res = nd_collect_subterms(control,control->signature,selected->tformula,stack);
	PStack_p duplicate_terms_removed = PStackRemoveDuplicatesTerm(stack);
	
	while (!PStackEmpty(duplicate_terms_removed))
	{
		
		constant = PStackPopP(duplicate_terms_removed);
		if (!constant) continue;
		if (!TFormulaVarIsFree(bank,selected->tformula,constant))
		{
			continue;
		}
		//relatively and absolutely flagged vars are handled in TableauUniversalIntroduction
		//printf("\nUniversalIntProcessTest\n");
		//WFormulaPrint(GlobalOut,selected,true);
		//printf("\nfreshvariable");
		//TermPrint(GlobalOut,freshvariable,control->signature,DEREF_NEVER);
		//printf("\nterm");
		//TermPrint(GlobalOut,constant,control->signature,DEREF_NEVER);
		generated = TableauUniversalIntroduction(control,bank,constant,freshvariable,selected);
		if (generated)
		{
			//printf("\nuniversal int done\n");
			//WFormulaPrint(GlobalOut,generated,true);
			FormulaSetInsert(temporary_store,generated);
			//exit(0);
		}
		//else printf("nothing generated\n");
	
	}
	PStackFree(stack);
	PStackFree(duplicate_terms_removed);
	return res;
}

//replace the terms of selected with existentially quantified variables
// need to check that they do not replace terms that are already bound

long TableauExistentialIntProcess(Tableau_p control,TB_p bank,WFormula_p selected)
{
	if (!selected)
	{
		return 0;
	}
	FormulaSet_p temporary_store = control->nd_temporary_formulas;
	long res = 0;
	WFormula_p generated;
	Term_p constant;
	
	//printf("\NMAX VAR CODE: %ld\n",TermFindMaxVarCode(selected->tformula));
	/*
	FunCode min_code = TermFindMaxVarCode(selected->tformula);
	assert(min_code < 0);
	min_code -= 2;
	Term_p freshvariable = VarBankFCodeFind(bank->vars,min_code);
	if (!freshvariable)
	{
		//printf("allocing a\n");
		freshvariable = VarBankVarAlloc(bank->vars,min_code,control->freshvars->sort_table->default_type);
	}
	*/
	Term_p freshvariable = VarBankGetFreshVar(control->freshvars,control->freshvars->sort_table->default_type);
	PStack_p stack = PStackAlloc();
	
	nd_label_symbols(control,selected->tformula);
	UpdateControlSymbols(control);
	res = nd_collect_subterms(control,control->signature,selected->tformula,stack);
	PStack_p duplicate_terms_removed = PStackRemoveDuplicatesTerm(stack);
	
	while (!PStackEmpty(duplicate_terms_removed))
	{
		
		constant = PStackPopP(duplicate_terms_removed);
		if (!constant) continue;
		if (!TFormulaVarIsFree(bank,selected->tformula,constant))
		{
			continue;
		}
		// no flags are needed for existential introduction
		generated = TableauExistentialIntroduction(control,bank,constant,freshvariable,selected);
		if (generated)
		{
			FormulaSetInsert(temporary_store,generated);
		}
	}
	
	PStackFree(stack);
	PStackFree(duplicate_terms_removed);
	return res;
}

long TableauAndElimProcess(Tableau_p control,TB_p bank,WFormula_p selected)
{
	//FormulaSet_p target = control->nd_derivation;
	FormulaSet_p temporary_store = control->nd_temporary_formulas;
	WFormula_p generated0 = TableauAndElimination(control,bank,selected,0);
	WFormula_p generated1 = TableauAndElimination(control,bank,selected,1);
	if (generated0)
	{
		FormulaSetInsert(temporary_store,generated0);
	}
	if (generated1)
	{
		FormulaSetInsert(temporary_store,generated1);
	}
	return 0;
}

long TableauOrElimProcess(Tableau_p control,TB_p bank,WFormula_p selected)
{
	WFormula_p handle;
	long counter = 0;
	FormulaSet_p target = control->nd_derivation;
	FormulaSet_p temporary_store = control->nd_temporary_formulas;
	handle = target->anchor->succ;
	//printf("\nNEW ITERATION\n");
	while(handle!=target->anchor)
	{
		WFormula_p generated = TableauOrElimination(control,bank,selected,handle);
		if (generated)
		{
			//printf("\n");
			//WFormulaPrint(GlobalOut,generated,true);
			FormulaSetInsert(temporary_store,generated);
			counter++;
		}
		else 
		{
			//printf("\nnull...\n");
		}
		handle = handle->succ;
	}
	return counter;
}

long TableauImplElimProcess(Tableau_p control,TB_p bank,WFormula_p selected)
{
	WFormula_p handle;
	FormulaSet_p target = control->nd_derivation;
	FormulaSet_p temporary_store = control->nd_temporary_formulas;
	handle = target->anchor->succ;
	long counter = 0;
	//printf("\nNEW ITERATION\n");
	while(handle!=target->anchor)
	{
		WFormula_p generated = TableauImplElimination(control,bank,selected,handle);
		if (generated)
		{
			FormulaSetInsert(temporary_store,generated);
			counter++;
		}
		else 
		{
			//printf("\nnull...\n");
		}
		handle = handle->succ;
	}
	return counter;
}

long TableauNegElimProcess(Tableau_p control,TB_p bank,WFormula_p selected)
{
	FormulaSet_p temporary_store = control->nd_temporary_formulas;
	WFormula_p generated = TableauNegationElimination(control,bank,selected);
	if (generated)
	{
		FormulaSetInsert(temporary_store,generated);
	}
	return 0;
}

// The below two methods need the substitution of arbitrary terms-  
// How to do this?  Need to read Tableau ATP paper again

long TableauUniversalElimProcess(Tableau_p control,TB_p bank,WFormula_p selected)
{
	//printf("\NMAX VAR CODE: %ld\n",TermFindMaxVarCode(selected->tformula));
	FormulaSet_p temporary_store = control->nd_temporary_formulas;
	FunCode min_code = TermFindMaxVarCode(selected->tformula);
	assert(min_code < 0);
	min_code -= 2;
	Term_p freshvariable = VarBankFCodeFind(bank->vars,min_code);
	if (!freshvariable)
	{
		//printf("allocing a\n");
		freshvariable = VarBankVarAlloc(bank->vars,min_code,control->freshvars->sort_table->default_type);
	}
	//Term_p freshvariable = VarBankGetFreshVar(control->freshvars,control->freshvars->sort_table->default_type);
	WFormula_p generated = TableauUniversalElimination(control,bank,selected,freshvariable);
	if (generated)
	{
		FormulaSetInsert(temporary_store,generated);
	}
	return 0;
}

/*  This doesn't work...
 * 
 * 
 * 
*/

long TableauExistentialElimProcess(Tableau_p control,TB_p bank,WFormula_p selected)
{
	FormulaSet_p temporary_store = control->nd_temporary_formulas;
	Term_p freshvariable = NULL;
	WFormula_p generated = TableauExistentialElimination(control,bank,selected,freshvariable);
	if (generated)
	{
		FormulaSetInsert(temporary_store,generated);
	}
	return 0;
}

//Check generated set for contradictory formulas
//Iterates through formulaset, checking the rest to see if they are the negation of handle

bool TableauFormulaSetCheckForContradictions(Tableau_p control, FormulaSet_p formulaset)
{
	TB_p bank = control->terms;
	WFormula_p handle = formulaset->anchor->succ;
	WFormula_p res = formulaset->anchor->succ;
	TFormula_p negated_handle,negated_res;
	while (handle != formulaset->anchor)
	{
		negated_handle = TFormulaFCodeAllocNoShare(bank,bank->sig->not_code,handle->tformula,NULL);
		while (res != formulaset->anchor)
		{
			Subst_p subst = SubstAlloc();
			
			negated_res = TFormulaFCodeAllocNoShare(bank,bank->sig->not_code,res->tformula,NULL);
			
			if (TableauUnify(control,subst,negated_handle,res->tformula) || 
				TableauUnify(control,subst,negated_res,handle->tformula))
			{
				SubstFree(subst);
				fprintf(GlobalOut, "\nFound contradiction!\n");
				WFormulaPrint(GlobalOut,handle,true);
				fprintf(GlobalOut, "\n");
				WFormulaPrint(GlobalOut,res,true);
				fprintf(GlobalOut, "\nend contradiction pair\n");
				return true;
			}
			TermTopFree(negated_res);
			SubstFree(subst);
			res = res->succ;
		}
		TermTopFree(negated_handle);
		res = formulaset->anchor->succ;
		handle = handle->succ;
	}
	return false;
}
/*
bool TableauAssumptionGoalIsReached(Tableau_p control, TableauAssumption_p derivation)
{
	WFormula_p handle = derivation->nd_derivation->anchor->succ;
	while (handle != derivation->nd_derivation->anchor)
	{
		Subst_p subst = SubstAlloc();
		if (TableauUnify(control,subst,handle->tformula,derivation->goal->tformula))
		{
			return true;
		}
		SubstFree(subst);
		handle = handle->succ;
	}
	return false;
}
*/
void TableauPInitializeDerivationGoal(Tableau_p input, FormulaSet_p source)
{
	WFormula_p handle = source->anchor->succ;
	WFormula_p goal = NULL;
	while(handle!=source->anchor)
	{
		if (FormulaQueryType(handle) == CPTypeNegConjecture)
		{
			if (handle->tformula->f_code != input->terms->sig->not_code)
			{
				printf("\nnegated conjecture is not a negation, searching for contradiction\n");
				//goal = handle;
				break;
			}
			goal = WTFormulaAlloc(input->terms,handle->tformula->args[0]);
			printf("\nFound negated goal, searching for direct proof:\n");
			//WFormulaPrint(GlobalOut,goal,true);
			//printf("\nExtracting negated conjecture:\n");
			FormulaSetExtractEntry(handle);
			//printf("\n");
			break;
		}
		else if (FormulaQueryType(handle) == CPTypeConjecture)
		{
			goal = handle;
			printf("\nFound goal, searching for direct proof:\n");
			//WFormulaPrint(GlobalOut,goal,true);
			//printf("\nExtracting conjecture:\n");
			FormulaSetExtractEntry(handle);
			//printf("\n");
			break;
		}
		handle = handle->succ;
	}
	if (!goal)
	{
		printf("\nFailed to find a goal!\n");
	}
	input->goal = goal;
}

bool TableauPDerivationGoalIsReached(Tableau_p control)
{
	WFormula_p handle = control->nd_generated->anchor->succ;
	//printf("\nformula in goal is reach %ld:\n",control->nd_generated->members);
	//WFormulaPrint(GlobalOut,handle,true);
	//printf("\n");
	//TFormulaTPTPPrint(GlobalOut,control->terms,handle->tformula,true,true);
	while (handle != control->nd_generated->anchor)
	{
		Subst_p subst = SubstAlloc();
		if (handle && TableauUnify(control,subst,handle->tformula,control->goal->tformula))
		{
			return true;
		}
		SubstFree(subst);
		handle = handle->succ;
	}
	return false;
}

void ContradictionTest(Tableau_p ndcontrol)
{
	TB_p bank = ndcontrol->terms;
	WFormula_p selected = TableauSelectHighestScoreRandomly(ndcontrol->nd_generated);
	printf("\nSelected:\n");
	WFormulaPrint(GlobalOut,selected,true);
	printf("\n");
	TableauGenerateAndScoreFormulas(ndcontrol,selected);
	TFormula_p s_tform = selected->tformula;
	TFormula_p s_neg = TFormulaFCodeAlloc(bank,bank->sig->not_code,s_tform,NULL);
	WFormula_p s_neg_formula = WTFormulaAlloc(bank,s_neg);
	FormulaSetInsert(ndcontrol->nd_generated,s_neg_formula);
	printf("\n");
	FormulaSetPrint(GlobalOut,ndcontrol->nd_generated,true);
	printf("\n");
	bool contra = TableauFormulaSetCheckForContradictions(ndcontrol,ndcontrol->nd_generated);
	printf("\n%d\n",contra);
}

void TableauResetState(Tableau_p ndcontrol)
{
	  FormulaSetFreeFormulas(ndcontrol->nd_derivation);
	  FormulaSetFreeFormulas(ndcontrol->nd_generated);
	  VarBankResetVCounts(ndcontrol->terms->vars);
	  VarBankResetVCounts(ndcontrol->freshvars);
}


