
#include "naturaldeduction.h"
#include <arpa/inet.h>

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

/*
 *   This is a skeleton of the idea and doesn't work at this point
 * 
 * 
*/

WFormula_p NDSelectHighestScoreThroughSocket(FormulaSet_p input, int port)
{
	#define MAX_BUFFER 1024
	int SERVER_PORT = port;
	
	int serverFd, connectionFd;
	struct sockaddr_in servaddr;
	char formulabuffer[MAX_BUFFER+1];
	
	serverFd = socket(AF_INET,SOCK_STREAM, 0);
	
	memset(&servaddr, 0, sizeof(servaddr));
	servaddr.sin_family = AF_INET;
	servaddr.sin_addr.s_addr = htonl(INADDR_ANY);
	servaddr.sin_port = htons(SERVER_PORT);
	
	bind ( serverFd,
		(struct sockaddr *)&servaddr, sizeof(servaddr));
		
	listen(serverFd, 5);
	
	WFormula_p handle = input->anchor->succ;
	printf("\nawaiting a connection\n");
	while(1)
	{
		connectionFd = accept(serverFd,
			(struct sockaddr *)NULL, NULL);
			
		if (connectionFd >= 0) 
		{
			snprintf(formulabuffer,MAX_BUFFER,"\ntest\n");
			write(connectionFd,formulabuffer,strlen(formulabuffer) );
			break;
			//send the score
			//await response
		}
	}
	close(connectionFd);
	
	printf("\nWingo\n");
	return (WFormula_p) NULL;
}


