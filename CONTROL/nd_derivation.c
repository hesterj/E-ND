
#include "naturaldeduction.h"

/*
NDAssumption_p NDAssumptionAlloc(WFormula_p goal, WFormula_p assumption)
{
	NDAssumption_p handle = NDAssumptionCellAlloc();
	
	handle->nd_derivation = FormulaSetAlloc();
	handle->goal = goal;
	handle->assumption = assumption;
	
	return handle;
}

void NDAssumptionFree(NDAssumption_p junk)
{
	FormulaSetFree(junk->nd_derivation);
	// what to do with goal/assumption?  junk formulaset to stop valgrind warnings?
	NDAssumptionCellFree(junk);
}
*/
void NDScoreFormulaRandomly(WFormula_p input)
{
	float score = (float)rand()/(float)(RAND_MAX);
	//float denom = (float) input->tformula->v_count;
	//denom += (float) input->tformula->f_count;
	//score = score/denom;
	//score = (float)rand()*score;
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
	//printf("\nsuccessfully scored.  seleccting highest score\n");
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
/*
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
			printf("\nExtracting negated conjecture:");
			FormulaSetExtractEntry(handle);
			printf("\n");
			break;
		}
		if (FormulaQueryType(handle) == CPTypeConjecture)
		{
			goal = handle;
			printf("\nFound goal:\n");
			WFormulaPrint(GlobalOut,goal,true);
			printf("\nExtracting conjecture:");
			FormulaSetExtractEntry(handle);
			break;
		}
		handle = handle->succ;
	}
	if (!goal)
	{
		printf("\nFailed to find a goal!\n");
		exit(0);
	}
	input->goal = goal;
}
*/
/*  Send a formula through the socket specified by socketDescriptor, then receive the score
 *  int MUST be a socketDescriptor
*/

WFormula_p NDSelectHighestScoreThroughSocket(FormulaSet_p input, int socketDescriptor)
{
	char sendBuffer[1000],recvBuffer[1000];
	WFormula_p handle = input->anchor->succ;
	WFormula_p selected = input->anchor->succ;
	float highestscore = 0;
	
	sending:
	while(1)
	{
		bzero(&sendBuffer,sizeof(sendBuffer));
		char *formula = WFormulaPrintString(handle);
		ssize_t sent = send(socketDescriptor,formula,strlen(formula)+1,0);
		if (sent > 0)
		{
			FREE(formula);
			break;
		}
	}

	while(1)
	{
		bzero(&recvBuffer,sizeof(recvBuffer));
		ssize_t received = recv(socketDescriptor,recvBuffer,sizeof(recvBuffer),0);
		if (received > 0)
		{
			float score = strtod(recvBuffer,0);
			if (score > highestscore)
			{
				selected = handle;
				highestscore = score;
			}
			handle = handle->succ;
			if (handle == input->anchor)
			{
				return selected;
			}
			goto sending;
		}
	}
	printf("\nscoring error, returning selected");
	return selected;
}

/*  Buffer size could become a problem....
 *  Long formulas could cause overflow
 * 
*/

char *WFormulaPrintString(WFormula_p input)
{
	char *formulabuffer = malloc(sizeof(char)*1024);
	FILE *container = fopen("/dev/shm/form.dat","w");
	WFormulaPrint(container,input,true);
	fclose(container);
	container = fopen("/dev/shm/form.dat","r");
	char *ptr = fgets(formulabuffer,1024,container);
	if (!ptr)
	{
		printf("WFormulaPrintString Error\n");
	}
	fclose(container);
	return formulabuffer;
}

// INCOMPLETE!
/*
bool NDCheckIfFormulaIsInstantiationOfExistential(ND_p control, WFormula_p existential,WFormula_p instantiation)
{
	FunCode funcode = existential->tformula->fun_code;
	if (funcode != control->signature->qex_code) return false;
	return true;
}
*/

