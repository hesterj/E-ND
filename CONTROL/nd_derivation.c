
#include "naturaldeduction.h"

ND_Derivation_p NDDerivationAlloc(ProofState_p initial, WFormula_p goal)
{
	ND_Derivation_p handle = NDDerivationCellAlloc();
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
	
	handle->goal = goal;
	
	return handle;
}

void NDScoreFormulaRandomly(WFormula_p input)
{
	float score = (float)rand()/(float)(RAND_MAX);
	input->score = score;
}

void NDScoreFormulaSetRandomly(FormulaSet_p input)
{
	WFormula_p handle = input->anchor->succ;
	while(handle!=input->anchor)
	{
		NDScoreFormulaRandomly(handle);
		//WFormulaPrint(GlobalOut,handle,true);
		//printf("\n%f\n",handle->score);
		handle = handle->succ;
	}
}

WFormula_p NDSelectHighestScoreRandomly(FormulaSet_p input)
{
	NDScoreFormulaSetRandomly(input);
	printf("\nsuccessfully scored.  seleccting highest score\n");
	WFormula_p handle = input->anchor->succ;
	WFormula_p res = input->anchor->succ;
	float maxscore = res->score;
	while(handle!=input->anchor)
	{
		if (handle->score > maxscore)
		{
			res = handle;
			maxscore = res->score;
		}
		handle = handle->succ;
	}
	//printf("\nMax score: %f\n",maxscore);
	//WFormulaPrint(GlobalOut,res,true);
	//printf("\n");
	return res;
}

void NDInitializeDerivationGoal(ND_Derivation_p input, FormulaSet_p source)
{
	WFormula_p handle = source->anchor->succ;
	WFormula_p goal = NULL;
	while(handle!=source->anchor)
	{
		if (FormulaQueryType(handle) == CPTypeNegConjecture)
		{
			goal = WTFormulaAlloc(input->terms,handle->tformula->args[0]);
			printf("\nFound goal:\n");
			WFormulaPrint(GlobalOut,goal,true);
			break;
		}
		if (FormulaQueryType(handle) == CPTypeConjecture)
		{
			goal = handle;
			printf("\nFound goal:\n");
			WFormulaPrint(GlobalOut,goal,true);
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


