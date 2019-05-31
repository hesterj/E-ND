#include "naturaldeduction.h"

/*  Forward Declarations
 * 
*/

/*  Internal functions
 * 
 * 
 * 
*/

void ProofTest(ND_p ndcontrol)
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
   WFormula_p f1 = NDUniversalElimination(ndcontrol,ndcontrol->terms,start,y1);
   WFormula_p f2 = NDAndElimination(ndcontrol,ndcontrol->terms,f1,0);
   Term_p x = VarBankGetFreshVar(ndcontrol->terms->vars,STIndividuals);
   WFormula_p f3 = NDUniversalIntroduction(ndcontrol,ndcontrol->terms,y1,x,f2);
   Term_p y2 = VarBankGetFreshVar(ndcontrol->terms->vars,STIndividuals);
   WFormula_p f4 = NDUniversalElimination(ndcontrol,ndcontrol->terms,start,y2);
   WFormula_p f5 = NDAndElimination(ndcontrol,ndcontrol->terms,f4,1);
   WFormula_p f6 = NDUniversalIntroduction(ndcontrol,ndcontrol->terms,y2,x,f5);
   WFormula_p f7 = NDAndIntroduction(ndcontrol,ndcontrol->terms,f3,f6);
   WFormula_p f8 = NDImplIntroduction(ndcontrol,ndcontrol->terms,start,f7);
   
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
   
   bool success = NDUnify(ndcontrol,subst,f_renamed->tformula,goal->tformula);
   //bool success_2 = NDUnify(ndcontrol,subst,f8->tformula,f7->tformula);
   
   //printf("\nsuccess: %d success2: %d\n",success,success_2);
   printf("\nsuccess: %d\n",success);

}

/*  Unification algorithm from Handbook of Automated Reasoning p. 454
 * 
 *  Warning:  May damage the dag structure of terms
*/


bool NDUnify(ND_p control, Subst_p subst, Term_p s, Term_p t)
{
	//printf("\nAttempting to unify:\n");
	//TermPrint(GlobalOut,s,control->signature,DEREF_NEVER);
	//printf("\n");
	//TermPrint(GlobalOut,t,control->signature,DEREF_NEVER);
	//printf("\n");
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
				bool temp1 = NDUnify(control, subst, s->args[i],t->args[i]);
				if (!temp1) 
				{
					//printf("\ntemp1 fail\n");
					return false;
				}
			}
		}
		else
		{
			//printf("\nf_code fail\n");
			//printf("\narities: %d %d\n",s->arity,t->arity);
			//TermPrint(GlobalOut,s,control->signature,DEREF_NEVER);
			//printf("\n");
			//TermPrint(GlobalOut,t,control->signature,DEREF_NEVER);
			//printf("\n%s %s\n",SigFindName(control->signature,s->f_code),SigFindName(control->signature,t->f_code));
			return false;
		}
	}
	else if (!TermIsVar(s))
	{
		bool temp2 = NDUnify(control,subst,t,s);
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


// Print the term pointers contained in handle
/*
static void PStackPrintTerms(ND_p control, PStack_p handle)
{
	PStackPointer i;
	for(i=0; i<PStackGetSP(handle); i++)
	{
		printf("\n");
		Term_p term = PStackElementP(handle,i);
		if (term)
		{
			// This term print is bugged
			//TermPrint(GlobalOut,control->signature,term,DEREF_NEVER);
		}
		//TFormulaTPTPPrint(GlobalOut,control->terms,term,true,true);
	}
}
*/
/*  Collect subterms using the style of the nd_label method, reducing the number
 *  of formulas that need to be labelled.
 *  
 * 
*/

long nd_collect_subterms2(ND_p control, Sig_p sig, Term_p term, PStack_p collector)
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



void FormulaSetUpdateControlSymbols(ND_p control, FormulaSet_p target)
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

//NDSaturateLoop is a test method for checking how the inference rules work when applied multiple times

void NDSaturateLoop(ND_p ndcontrol, long loops)
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
		  
		  NDAndIntProcess(ndcontrol,ndcontrol->terms,handle);
		  NDOrIntProcess(ndcontrol,ndcontrol->terms,handle);
		  NDImplIntProcess(ndcontrol,ndcontrol->terms,handle);
		  NDNegIntProcess(ndcontrol,ndcontrol->terms,handle);
		  NDUniversalIntProcess(ndcontrol,ndcontrol->terms,handle);
		  NDExistentialIntProcess(ndcontrol,ndcontrol->terms,handle);
		  NDOrElimProcess(ndcontrol,ndcontrol->terms,handle);
		  NDAndElimProcess(ndcontrol,ndcontrol->terms,handle);
		  NDImplElimProcess(ndcontrol,ndcontrol->terms,handle);
		  NDNegElimProcess(ndcontrol,ndcontrol->terms,handle);
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

void NDGenerateAndScoreFormulas(ND_p ndcontrol,WFormula_p handle)
{
	
	NDAndIntProcess(ndcontrol,ndcontrol->terms,handle);
	NDOrIntProcess(ndcontrol,ndcontrol->terms,handle);
	NDImplIntProcess(ndcontrol,ndcontrol->terms,handle);
	NDNegIntProcess(ndcontrol,ndcontrol->terms,handle);
	NDUniversalIntProcess(ndcontrol,ndcontrol->terms,handle);
	NDExistentialIntProcess(ndcontrol,ndcontrol->terms,handle);
	NDOrElimProcess(ndcontrol,ndcontrol->terms,handle);
	NDAndElimProcess(ndcontrol,ndcontrol->terms,handle);
	NDImplElimProcess(ndcontrol,ndcontrol->terms,handle);
	NDNegElimProcess(ndcontrol,ndcontrol->terms,handle);
	
	//printf("\ndumping %ld previous formulas...",ndcontrol->nd_generated->members);
	//FormulaSetFreeFormulas(ndcontrol->nd_generated);
	//printf("\ninserting %ld temporary formulas...",ndcontrol->nd_temporary_formulas->members);
	FormulaSetUpdateControlSymbols(ndcontrol,ndcontrol->nd_temporary_formulas);
	FormulaSetInsertSet(ndcontrol->nd_generated,ndcontrol->nd_temporary_formulas);
}

void NDGenerateAndScoreFormulasSkeleton(ND_p ndcontrol,WFormula_p handle)
{
	//FormulaSetUpdateControlSymbols(ndcontrol,ndcontrol->nd_generated);
	//printf("\n");
	//WFormulaPrint(GlobalOut,handle,true);
	//printf("\n");
	
	NDAndIntProcess(ndcontrol,ndcontrol->terms,handle);
	NDOrIntProcess(ndcontrol,ndcontrol->terms,handle);
	NDImplIntProcess(ndcontrol,ndcontrol->terms,handle);
	NDNegIntProcess(ndcontrol,ndcontrol->terms,handle);
	NDUniversalIntProcess(ndcontrol,ndcontrol->terms,handle);
	NDExistentialIntProcess(ndcontrol,ndcontrol->terms,handle);
	NDOrElimProcess(ndcontrol,ndcontrol->terms,handle);
	NDAndElimProcess(ndcontrol,ndcontrol->terms,handle);
	NDImplElimProcess(ndcontrol,ndcontrol->terms,handle);
	NDNegElimProcess(ndcontrol,ndcontrol->terms,handle);
	
	//printf("\ndumping %ld previous formulas...",ndcontrol->nd_generated->members);
	//FormulaSetFreeFormulas(ndcontrol->nd_generated);
	//printf("\ninserting %ld temporary formulas...",ndcontrol->nd_temporary_formulas->members);
	if (ndcontrol->nd_temporary_formulas->members == 0)
	{
		printf("\nno generated formulas\n");
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

long nd_label_symbols(ND_p control,Term_p term)
{
	Sig_p sig = control->signature;
	//printf("\nlabelling\n");
	//TermPrint(GlobalOut,term,sig,DEREF_NEVER);
	//printf("\n%s\n",SigFindName(sig,term->f_code));
	//printf("\n%ld\n",term->f_code);
	//printf("\neqn: %ld neqn: %ld\n",sig->eqn_code,sig->neqn_code);
	//printf("\n%d\n",term->arity);
	/*
	if (term->arity == 2 && ((term->args[0]->f_code == SigFindFCode(sig,"$true"))
				|| (term->args[1]->f_code == SigFindFCode(sig,"$true"))
				|| (term->args[0]->f_code == SigFindFCode(sig,"$false"))
				|| (term->args[1]->f_code == SigFindFCode(sig,"$false"))))
	*/
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
											 || (term->f_code == sig->and_code))
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

long nd_collect_subterms(ND_p control, Sig_p sig, Term_p term, PStack_p collector)
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
/*
long nd_term_collect_subterms(Sig_p sig, Term_p term, PStack_p collector)
{
   long res = 0;
   int i;
   if (TermIsVar(term) || TermIsConst(term) || (term->arity == 0))
   {
	   PStackPushP(collector,term);
	   res += 1;
   }
   else if (SigIsFunction(sig,term->f_code))
   {
	   PStackPushP(collector,term);
	   res += 1;
	   for (i=0; i<term->arity; i++)
	   {
		   PStackPushP(collector,term->args[i]);
		   res += 1;
		   res += nd_term_collect_subterms(sig,term->args[i],collector);
	   }
   }
   else if (SigIsPredicate(sig,term->f_code) || (term->f_code == sig->eqn_code)
											 || (term->f_code == sig->qall_code)
											 || (term->f_code == sig->qex_code)
											 || (term->f_code == sig->impl_code)
											 || (term->f_code == sig->equiv_code)
											 || (term->f_code == sig->and_code)
											 || (term->f_code == sig->neqn_code)
											 || (term->f_code == sig->or_code)
											 || (term->f_code == sig->not_code))
   {
	   if (term->f_code == member)
	   {
		   for (i=0; i<term->arity; i++)
		   {
			   PStackPushP(collector,term->args[i]);
			   res += 1;
			   res += nd_term_collect_subterms(sig,term->args[i],collector);
		   }
	   }
	   for (i=0; i<term->arity; i++)
	   {
		   res += nd_term_collect_subterms(sig,term->args[i],collector);
	   }
   }
   return res;
}
*/


/*  Externally declared functions
 *  
 * 
 * 
*/

ND_p NDAlloc(ProofState_p initial)
{
	ND_p handle = NDCellAlloc();
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
	return handle;
}

void NDFree(ND_p initial)
{
	PStackFree(initial->derivation);
	PStackFree(initial->absolutely_flagged_variables);
	PStackFree(initial->relatively_flagged_variables);
	PStackFree(initial->predicates);
	PStackFree(initial->functions);
	
	FormulaSetFree(initial->nd_derivation);
	FormulaSetFree(initial->nd_generated);
	FormulaSetFree(initial->nd_temporary_formulas);
	WFormulaFree(initial->goal);
	NDCellFree(initial);
}

ND_p NDAllocAssumption(ND_p initial)
{
	ND_p handle = NDCellAlloc();
	handle->last_assumption = NULL;
	handle->derivation = PStackAlloc();  // leaking?
	handle->absolutely_flagged_variables = initial->absolutely_flagged_variables;
	handle->relatively_flagged_variables = initial->relatively_flagged_variables;
	handle->predicates = PStackAlloc();
	handle->functions = PStackAlloc();
	handle->nd_derivation = FormulaSetAlloc();
	FormulaSetCopyFormulas(handle->nd_derivation,initial->nd_derivation);
	handle->nd_generated = FormulaSetAlloc();
	handle->nd_temporary_formulas = FormulaSetAlloc();
	handle->generated_formulas = 0;
	handle->signature = initial->signature;
	handle->terms = initial->terms;
	handle->freshvars = initial->freshvars;
	handle->goal = NULL;
	return handle;
}

void NDAssumptionFree(ND_p initial)
{
	//FormulaSetFreeFormulas(initial->nd_derivation);
	//FormulaSetFreeFormulas(initial->nd_generated);
	//FormulaSetFreeFormulas(initial->nd_temporary_formulas);
	//WFormulaFree(initial->goal);
	PStackFree(initial->derivation);
	PStackFree(initial->predicates);
	PStackFree(initial->functions);
	FormulaSetFree(initial->nd_derivation);
	FormulaSetFree(initial->nd_generated);
	FormulaSetFree(initial->nd_temporary_formulas);
	NDCellFree(initial);
	//WFormulaFree(initial->last_assumption);
}

WFormula_p NDAndIntroduction(ND_p control,TB_p bank, WFormula_p a, WFormula_p b)
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

WFormula_p NDOrIntroduction(ND_p control,TB_p bank, WFormula_p a, WFormula_p b)
{
	TFormula_p a_tform = a->tformula;
	TFormula_p b_tform = b->tformula;
	TFormula_p a_or_b = TFormulaFCodeAlloc(bank,bank->sig->or_code,a_tform,b_tform);
	/*
	printf("\nor introduction\n");
	WFormulaPrint(GlobalOut,a,true);
	printf("\n");
	WFormulaPrint(GlobalOut,b,true);
	*/
	WFormula_p handle = WTFormulaAlloc(bank,a_or_b);
	return handle;
}

/*  a must be the most recent non discarded assumption occuring in the proof
 * 
 * 
*/

WFormula_p NDImplIntroduction(ND_p control,TB_p bank, WFormula_p a, WFormula_p b)
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

WFormula_p NDNegIntroduction(ND_p control,TB_p bank, WFormula_p a, WFormula_p b, WFormula_p c)
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
	//TFormula_p c_neg = TFormulaFCodeAlloc(bank,bank->sig->not_code,c_tform,NULL);
	/*
	if (TFormulaEqual(a_tform,b_neg) || TFormulaEqual(a_neg,b_tform))
	{
		TFormula_p c_neg = TFormulaFCodeAlloc(bank,bank->sig->not_code,c_tform,NULL);
		WFormula_p handle = WTFormulaAlloc(bank,c_neg);
		return handle;
	}
	*/
	Subst_p subst1 = SubstAlloc();  // leaking??
	Subst_p subst2 = SubstAlloc();  // leaking??
	if (NDUnify(control,subst1,a_tform,b_neg) || NDUnify(control,subst2,a_neg,b_tform))
	{
		TFormula_p c_neg = TFormulaFCodeAlloc(bank,bank->sig->not_code,c_tform,NULL);
		WFormula_p handle = WTFormulaAlloc(bank,c_neg);
		SubstDelete(subst1);
		SubstDelete(subst2);
		//TermTopFree(a_neg);
		//TermTopFree(b_neg);
		return handle;
	}
	SubstDelete(subst1);
	SubstDelete(subst2);
	//TermTopFree(a_neg);
	//TermTopFree(b_neg);
	//TermTopFree(c_neg);
	
	return NULL;
}

/*  Does not check if the ND rule is allowed!!!  Only does it if physically possible
 *  Return NULL if term is not a subterm of the formula
 *  Replaces term with variable, absolutely flags term
 *  Absolutely and relatively flags variables
*/

WFormula_p NDUniversalIntroduction(ND_p control,TB_p bank, Term_p term, Term_p variable, WFormula_p formula)
{
	
	TFormula_p handle = formula->tformula;
	TFormula_p new_tform,qall_new_tform;
	WFormula_p qall_new_form;
	
	if (!TermIsSubterm(handle,term,DEREF_NEVER))
	{
		return NULL; //term is not a subterm of the formula
	}
	PTree_p free_variables = NULL;
	PStack_p free_stack = PStackAlloc();
	TFormulaCollectFreeVars(bank, formula->tformula, &free_variables);
	PTreeToPStack(free_stack,free_variables);
	
	// push parameters to relatively flagged variables
	pstack_push_skip(control->relatively_flagged_variables,free_stack,term);
	// push variable being introduced to absolutely flagged variables
	PStackPushP(control->absolutely_flagged_variables,term);
	
	WFormula_p new_formula = FormulaMergeVars(formula,bank,term,variable);
	new_tform = new_formula->tformula;
	qall_new_tform = TFormulaQuantorAlloc(bank,bank->sig->qall_code,variable,new_tform);
	qall_new_form = WTFormulaAlloc(bank,qall_new_tform);
	
	WFormulaFree(new_formula);
	
	PStackFree(free_stack);
	PTreeFree(free_variables);
	return qall_new_form;
	
}

WFormula_p NDExistentialIntroduction(ND_p control,TB_p bank, Term_p term, Term_p variable, WFormula_p formula)
{
	TFormula_p handle = formula->tformula;
	TFormula_p new_tform,qex_new_tform;
	WFormula_p qex_new_form;
	
	if (!TermIsSubterm(handle,term,DEREF_NEVER))
	{
		return NULL; //term is not a subterm of the formula
	}
	WFormula_p new_formula = FormulaMergeVars(formula,bank,term,variable);
	
	new_tform = new_formula->tformula;
	qex_new_tform = TFormulaQuantorAlloc(bank,bank->sig->qex_code,variable,new_tform);
	qex_new_form = WTFormulaAlloc(bank,qex_new_tform);
	
	WFormulaFree(new_formula);
	
	return qex_new_form;
	
}

/* conjunct is A & B, select = 0 returns A, select = 0 returns B.
 * Return NULL if conjunct is not actually a conjunct
 * 
*/

// CHECK THIS

WFormula_p NDAndElimination(ND_p control,TB_p bank, WFormula_p conjunct, int select)
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

WFormula_p NDOrElimination(ND_p control,TB_p bank, WFormula_p a,WFormula_p b)
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

/* As NDOrElimination
 * 
 * 
 * 
 * 
*/

WFormula_p NDImplElimination(ND_p control,TB_p bank, WFormula_p a,WFormula_p b)
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

WFormula_p NDNegationElimination(ND_p control,TB_p bank, WFormula_p a)
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

WFormula_p NDUniversalElimination(ND_p control,TB_p bank, WFormula_p a, Term_p substitute)
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
	return target;
}

/*
 *   w_matrix??? fix
 * 
 * 
*/

WFormula_p NDExistentialElimination(ND_p control,TB_p bank, WFormula_p a, Term_p substitute)
{
	WFormula_p w_matrix,target;
	TFormula_p matrix;
	Term_p bound_variable;
	if (a->tformula->f_code != bank->sig->qex_code)
	{
		return NULL;
	}
	
	PTree_p free_variables = NULL;
	PStack_p free_stack = PStackAlloc();
	TFormulaCollectFreeVars(bank, a->tformula, &free_variables);
	PTreeToPStack(free_stack,free_variables);
	PStackPushStack(control->relatively_flagged_variables,free_stack);
	PStackPushP(control->absolutely_flagged_variables,substitute);
	
	bound_variable = a->tformula->args[0];
	matrix = a->tformula->args[1];
	w_matrix = WTFormulaAlloc(bank,matrix);
	target = FormulaMergeVars(w_matrix,bank,bound_variable,substitute);
	
	PStackFree(free_stack);
	PTreeFree(free_variables);
	return target;
}

/*  Make all possible and introductions with the ND_p and formula passed
 * 
 * 
*/

long NDAndIntProcess(ND_p control,TB_p bank,WFormula_p selected)
{
	WFormula_p handle;
	//FormulaSet_p target = control->nd_generated;
	FormulaSet_p target = control->nd_derivation;
	FormulaSet_p temporary_store = control->nd_temporary_formulas;
	handle = target->anchor->succ;
	long counter = 0;
	//printf("\nNEW ITERATION\n");
	while(handle!=target->anchor)
	{
		WFormula_p generated = NDAndIntroduction(control,bank,selected,handle);
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

long NDOrIntProcess(ND_p control,TB_p bank,WFormula_p selected)
{
	WFormula_p handle;
	FormulaSet_p target = control->nd_derivation;
	FormulaSet_p temporary_store = control->nd_temporary_formulas;
	handle = target->anchor->succ;
	//printf("\nNEW ITERATION\n");
	long counter = 0;
	while(handle!=target->anchor)
	{
		WFormula_p generated = NDOrIntroduction(control,bank,selected,handle);
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

long NDImplIntProcess(ND_p control,TB_p bank,WFormula_p selected)
{
	WFormula_p handle;
	FormulaSet_p target = control->nd_derivation;
	FormulaSet_p temporary_store = control->nd_temporary_formulas;
	handle = target->anchor->succ;
	//printf("\nNEW ITERATION\n");
	long counter = 0;
	while(handle!=target->anchor)
	{
		WFormula_p generated = NDImplIntroduction(control,bank,selected,handle);
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

long NDNegIntProcess(ND_p control,TB_p bank,WFormula_p selected)
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
			WFormula_p generated = NDNegIntroduction(control,bank,selected,handle,alt_handle);
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

long NDUniversalIntProcess(ND_p control,TB_p bank,WFormula_p selected)
{
	if (!selected)
	{
		return 0;
	}
	FormulaSet_p temporary_store = control->nd_temporary_formulas;
	long res = 0;
	WFormula_p generated;
	Term_p constant;
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
		//relatively and absolutely flagged vars are handled in NDUniversalIntroduction
		generated = NDUniversalIntroduction(control,bank,constant,freshvariable,selected);
		if (generated)
		{
			FormulaSetInsert(temporary_store,generated);
		}
	}
	
	PStackFree(stack);
	PStackFree(duplicate_terms_removed);
	return res;
}

//replace the terms of selected with existentially quantified variables
// need to check that they do not replace terms that are already bound

long NDExistentialIntProcess(ND_p control,TB_p bank,WFormula_p selected)
{
	if (!selected)
	{
		return 0;
	}
	FormulaSet_p temporary_store = control->nd_temporary_formulas;
	long res = 0;
	WFormula_p generated;
	Term_p constant;
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
		generated = NDExistentialIntroduction(control,bank,constant,freshvariable,selected);
		if (generated)
		{
			FormulaSetInsert(temporary_store,generated);
		}
	}
	
	PStackFree(stack);
	PStackFree(duplicate_terms_removed);
	return res;
}

long NDAndElimProcess(ND_p control,TB_p bank,WFormula_p selected)
{
	//FormulaSet_p target = control->nd_derivation;
	FormulaSet_p temporary_store = control->nd_temporary_formulas;
	WFormula_p generated0 = NDAndElimination(control,bank,selected,0);
	WFormula_p generated1 = NDAndElimination(control,bank,selected,1);
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

long NDOrElimProcess(ND_p control,TB_p bank,WFormula_p selected)
{
	WFormula_p handle;
	long counter = 0;
	FormulaSet_p target = control->nd_derivation;
	FormulaSet_p temporary_store = control->nd_temporary_formulas;
	handle = target->anchor->succ;
	//printf("\nNEW ITERATION\n");
	while(handle!=target->anchor)
	{
		WFormula_p generated = NDOrElimination(control,bank,selected,handle);
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

long NDImplElimProcess(ND_p control,TB_p bank,WFormula_p selected)
{
	WFormula_p handle;
	FormulaSet_p target = control->nd_derivation;
	FormulaSet_p temporary_store = control->nd_temporary_formulas;
	handle = target->anchor->succ;
	long counter = 0;
	//printf("\nNEW ITERATION\n");
	while(handle!=target->anchor)
	{
		WFormula_p generated = NDImplElimination(control,bank,selected,handle);
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

long NDNegElimProcess(ND_p control,TB_p bank,WFormula_p selected)
{
	FormulaSet_p temporary_store = control->nd_temporary_formulas;
	WFormula_p generated = NDNegationElimination(control,bank,selected);
	if (generated)
	{
		FormulaSetInsert(temporary_store,generated);
	}
	return 0;
}

// The below two methods need the substitution of arbitrary terms-  
// How to do this?  Need to read ND ATP paper again

long NDUniversalElimProcess(ND_p control,TB_p bank,WFormula_p selected)
{
	printf("\nunimplemented\n");
	return 0;
}

long NDExistentialElimProcess(ND_p control,TB_p bank,WFormula_p selected)
{
	printf("\nunimplemented\n");
	return 0;
}

//Check generated set for contradictory formulas
//Iterates through formulaset, checking the rest to see if they are the negation of handle

bool NDFormulaSetCheckForContradictions(ND_p control, FormulaSet_p formulaset)
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
			
			if (NDUnify(control,subst,negated_handle,res->tformula) || 
				NDUnify(control,subst,negated_res,handle->tformula))
			{
				//TermFree(negated_handle);
				SubstFree(subst);
				//TermFree(negated_res);
				//TermFree(negated_handle);
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

/*  A test saturation algorithm for natural deduction calculus
 * 
 * 
 * 
 * 
 * 
 * 
*/

int NDSaturate(ProofState_p state, ProofControl_p control, long
                  step_limit, long proc_limit, long unproc_limit, long
                  total_limit, long generated_limit, long tb_insert_limit,
                  long answer_limit)          
{
   ND_p ndcontrol = NDAlloc(state);
   WFormula_p selected = NULL;
   WFormula_p selected_copy = NULL;
   bool success = false;
   //int assumption_status = 0;
   
   /*  Initialize connection to Scoring Server
   */  
   
   	int socketDescriptor;
	struct sockaddr_in serverAddress;

	bzero(&serverAddress,sizeof(serverAddress));

	serverAddress.sin_family=AF_INET;
	serverAddress.sin_addr.s_addr=inet_addr("127.0.0.1");
	serverAddress.sin_port=htons(5500);

	socketDescriptor=socket(AF_INET,SOCK_STREAM,0);
	
	connect(socketDescriptor,(struct sockaddr*)&serverAddress,sizeof(serverAddress));
   
   /*  Initialize the proof state
   */
   
   FormulaSet_p axiom_archive = FormulaSetAlloc();
   
   //FormulaSetInsertSet(ndcontrol->nd_generated,state->f_axioms);
   FormulaSetCopyFormulas(ndcontrol->nd_generated,state->f_axioms);
   FormulaSetCopyFormulas(ndcontrol->nd_derivation,state->f_axioms);
   NDPInitializeDerivationGoal(ndcontrol,ndcontrol->nd_generated);
   FormulaSetUpdateControlSymbols(ndcontrol,ndcontrol->nd_generated);
   
   FormulaSetCopyFormulas(axiom_archive,ndcontrol->nd_generated);
   
   srand(time(0));
   printf("\n%ld\n",ndcontrol->nd_generated->members);
   int counter = 0;
   int success_state = 0;
   //int assumptioncounter = 0;
   /*  Begin Proof Search
   */
   
   restart:
   
   while (success == false)
   {
	  counter++;
	  int start_new_assumption = rand()%6;  // 1/6 chance of starting new assumption
	  
	  if (start_new_assumption == 0)
	  {
		  // assumption status is 0 if assumption attempt is abandoned
		  // 1 if contradiction found
		  // 2 if goal was reached by lhs of sequent assumption
		  printf("\nstart new assumption\n");
		  int assumption_status = 0;
		  assumption_status = NDStartNewAssumption(ndcontrol,socketDescriptor);
		  //assumptioncounter++;
		  printf("\nexit assumption\n");
		  if (assumption_status == 0)
		  {
			  printf("\nno assumption success\n");
		  }
		  if (assumption_status == 1)
		  {
			  printf("\nproof by contradiction\n");
			  success = true;
		  }
		  if (assumption_status == 2)
		  {
			  printf("\nreached goal in assumption\n");
			  success = true;
		  }
		  /*
		  if (assumptioncounter == 3)
		  {
			exit(0);
		  }
		  */
	  }
	  
	  
	  /*  Go through a socket to get the highest score from the scoring server
	   *  Message sent is the string representation of the formula in ND generated, message received is the corresponding score.  
	   *  Choose highest score...
	  */ 
	  selected = NDSelectHighestScoreRandomly(ndcontrol->nd_generated);
	  //selected = NDSelectHighestScoreThroughSocket(ndcontrol->nd_generated,socketDescriptor);
	  /*
	  */
	  selected_copy = WFormulaFlatCopy(selected);
	  FormulaSetInsert(ndcontrol->nd_derivation,selected_copy);
	  //printf("\ngenerated formulas in main loop: %ld\n",ndcontrol->nd_generated->members);
	  printf("\n");
	  WFormulaPrint(GlobalOut,selected,true);
	  //printf("\n___generating___\n");
	  NDGenerateAndScoreFormulas(ndcontrol,selected);
	  if (NDFormulaSetCheckForContradictions(ndcontrol,ndcontrol->nd_derivation))
	  {
		  //printf("\nfound contradiction\n");
		  success_state = 1;
		  success = true;
	  }
	  //printf("\nchecking for goal reach\n");
	  if ((ndcontrol->goal) && NDPDerivationGoalIsReached(ndcontrol))
	  {
		  //printf("\nreached goal\n");
		  success_state = 2;
		  success = true;
	  }
	  if (ndcontrol->nd_derivation->members > 40)
	  {
		  printf("\nmax derivation length\n");
		  NDResetState(ndcontrol);
		  FormulaSetCopyFormulas(ndcontrol->nd_generated,axiom_archive);
		  FormulaSetCopyFormulas(ndcontrol->nd_derivation,state->f_axioms);
		  goto restart;
	  }
   }
   
   //printf("\n Here is the derivation the loop succeeded in finding:\n");
   //FormulaSetPrint(GlobalOut,ndcontrol->nd_derivation,true);
   switch (success_state)
   {
	   case 0:
	      printf("\nfailure\n");
	      NDFree(ndcontrol);
	      FormulaSetFree(axiom_archive);
	      return 0;
	      
	   case 1: 
	      printf("\ncontradiction\n");
	      NDFree(ndcontrol);
	      FormulaSetFree(axiom_archive);
	      return 1;
	   case 2:
	      printf("\nreached goal\n");
	      NDFree(ndcontrol);
	      FormulaSetFree(axiom_archive);
	      return 2;
   }
   NDFree(ndcontrol);
   FormulaSetFree(axiom_archive);
   //FormulaSetFree(ndcontrol->nd_generated);
   //FormulaSetFree(ndcontrol->nd_temporary_formulas);
   return 0;
}

bool NDDerivationGoalIsReached(ND_p control, ND_Derivation_p derivation)
{
	WFormula_p handle = derivation->nd_derivation->anchor->succ;
	while (handle != derivation->nd_derivation->anchor)
	{
		Subst_p subst = SubstAlloc();
		if (NDUnify(control,subst,handle->tformula,derivation->goal->tformula))
		{
			return true;
		}
		SubstFree(subst);
		handle = handle->succ;
	}
	return false;
}

int NDStartNewAssumption(ND_p ndcontrol, int socketDescriptor)
{
	TFormula_p assumption = NULL;
	WFormula_p assumption_formula = NULL;
	bool success = false;
	WFormula_p selected = NULL;
	WFormula_p selected_copy = NULL;
	ND_p assumption_control = NDAllocAssumption(ndcontrol);
	int return_state = 0;
	
	// select the assumption
	// possible assumptions: negation of parent's goal, if goal is an implication 
	// can choose left hand side of implication
	
	if (ndcontrol->goal)  // if we are searching for contradiction there is no goal
	{
		assumption_control->goal = ndcontrol->goal;
		assumption = TFormulaFCodeAlloc(assumption_control->terms,
										assumption_control->terms->sig->not_code,
										assumption_control->goal->tformula,
										NULL);
		assumption_formula = WTFormulaAlloc(assumption_control->terms,assumption);
		
		
		printf("\nassumption_formula:\n");
		WFormulaPrint(GlobalOut,assumption_formula,true);
		
		FormulaSetInsert(assumption_control->nd_derivation,assumption_formula);
		assumption_control->last_assumption = assumption_formula;
	}
	
	//add the previous steps to our assumption branch
	FormulaSetCopyFormulas(assumption_control->nd_generated,ndcontrol->nd_derivation);
	
	//check to see that we have something to select from
	if (assumption_control->nd_generated->members == 0)
	{
		printf("\nno generated formulas in assumption, surfacing\n");
		return_state = 0;
		success = true; // skip the while loop and give up the assumtion: no axioms??
	}
	printf("\nentering assumption dive\n");
	// for now the only possible assumption is the negation of the parent's goal, done above
	while (success == false)
	{
		if (assumption_control->nd_generated->members == 0)
		{
			printf("\nout of generated formulas\n");
			return_state = 0;
			break;
		}
		// engage in new derivation beginning with assumption of first step
		// reuse much from the main loop
		int start_new_assumption = rand()%6;  // 1/6 chance of starting new assumption
	    
		if (start_new_assumption == 0)
		{
			// assumption status is 0 if assumption attempt is abandoned
			// 1 if contradiction found
			// 2 if goal was reached by lhs of sequent assumption
			printf("start new assumption\n");
			int assumption_status = 0;
			assumption_status = NDStartNewAssumption(ndcontrol,socketDescriptor);
			//printf("\nexit assumption\n");
			if (assumption_status == 0)
			{
				printf("no assumption success\n");
			}
			if (assumption_status == 1)
			{
				printf("\nproof by contradiction\n");
				success = true;
			}
			if (assumption_status == 2)
			{
				printf("\nreached goal in assumption\n");
				success = true;
			}
		}
		
		//selected = NULL;
		selected = NDSelectHighestScoreRandomly(assumption_control->nd_generated);
		if (!selected)
		{
			printf("NULL selected in assumption");
			break;
		}
		//selected = NDSelectHighestScoreThroughSocket(ndcontrol->nd_generated,socketDescriptor);
		selected_copy = WFormulaFlatCopy(selected);
		FormulaSetInsert(assumption_control->nd_derivation,selected_copy);
		printf("\n");
		WFormulaPrint(GlobalOut,selected,true);
		NDGenerateAndScoreFormulasSkeleton(assumption_control,selected);
		
		if (NDFormulaSetCheckForContradictions(assumption_control,assumption_control->nd_derivation))
		{
			printf("\nAssumption led to contradiction\n");
			success = true;
			return_state = 1;
		}
		if ((ndcontrol->goal) && NDPDerivationGoalIsReached(assumption_control))
		{
			printf("\nreached goal of assumption\n");
			success = true;
			return_state = 2;
		}
		if (assumption_control->nd_derivation->members > 50)
		{
			printf("\nexcess derivation size: %ld\n",assumption_control->nd_derivation->members);
			break;
		}
	}
	NDAssumptionFree(assumption_control);
	printf("\nsurface\n");
	//exit(0);
	// change ndcontrol appropriately
	// 1) if we obtained a contradiction, add the negation of the assumption to the parent derivation
	// 2) if we obtained the goal, set our assumption as the new goal of parent
	// free the unnecessary parts of the current derivation
	return return_state;
}

void NDPInitializeDerivationGoal(ND_p input, FormulaSet_p source)
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
			printf("\nFound negated goal:\n");
			WFormulaPrint(GlobalOut,goal,true);
			//printf("\nExtracting negated conjecture:\n");
			FormulaSetExtractEntry(handle);
			printf("\n");
			break;
		}
		if (FormulaQueryType(handle) == CPTypeConjecture)
		{
			goal = handle;
			printf("\nFound goal:\n");
			WFormulaPrint(GlobalOut,goal,true);
			//printf("\nExtracting conjecture:\n");
			FormulaSetExtractEntry(handle);
			printf("\n");
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

bool NDPDerivationGoalIsReached(ND_p control)
{
	WFormula_p handle = control->nd_derivation->anchor->succ;
	while (handle != control->nd_derivation->anchor)
	{
		Subst_p subst = SubstAlloc();
		if (NDUnify(control,subst,handle->tformula,control->goal->tformula))
		{
			return true;
		}
		SubstFree(subst);
		handle = handle->succ;
	}
	return false;
}

void ContradictionTest(ND_p ndcontrol)
{
	TB_p bank = ndcontrol->terms;
	WFormula_p selected = NDSelectHighestScoreRandomly(ndcontrol->nd_generated);
	printf("\nSelected:\n");
	WFormulaPrint(GlobalOut,selected,true);
	printf("\n");
	NDGenerateAndScoreFormulas(ndcontrol,selected);
	TFormula_p s_tform = selected->tformula;
	TFormula_p s_neg = TFormulaFCodeAlloc(bank,bank->sig->not_code,s_tform,NULL);
	WFormula_p s_neg_formula = WTFormulaAlloc(bank,s_neg);
	FormulaSetInsert(ndcontrol->nd_generated,s_neg_formula);
	printf("\n");
	FormulaSetPrint(GlobalOut,ndcontrol->nd_generated,true);
	printf("\n");
	bool contra = NDFormulaSetCheckForContradictions(ndcontrol,ndcontrol->nd_generated);
	printf("\n%d\n",contra);
}

void NDResetState(ND_p ndcontrol)
{
	  FormulaSetFreeFormulas(ndcontrol->nd_derivation);
	  FormulaSetFreeFormulas(ndcontrol->nd_generated);
	  VarBankResetVCounts(ndcontrol->terms->vars);
	  VarBankResetVCounts(ndcontrol->freshvars);
}
