#ifndef DERIVATION

#define DERIVATION

#include <clb_os_wrapper.h>
#include <cio_signals.h>
#include <ccl_fcvindexing.h>
#include <che_heuristics.h>
#include <che_axiomscan.h>
#include <che_to_autoselect.h>
#include <cco_clausesplitting.h>
#include <cco_forward_contraction.h>
#include <cco_interpreted.h>
#include <ccl_satinterface.h>
#include <zfc.h>
#include <cio_multiplexer.h>
#include <cco_eserver.h>

typedef struct derivationcell 
{
	PStack_p derivation;
	PStack_p absolutely_flagged_variables;
	PStack_p relatively_flagged_variables;
	
	PStack_p predicates;
	PStack_p functions;
	
	WFormula_p goal;
	
	FormulaSet_p nd_derivation;
	FormulaSet_p nd_generated;
	FormulaSet_p nd_temporary_formulas;
	long generated_formulas;
	VarBank_p     freshvars;
	TB_p          terms;
	Sig_p         signature;
	
}NDDerivation, *ND_Derivation_p;

#define NDDerivationCellAlloc() (NDDerivation*)SizeMalloc(sizeof(NDDerivation))
ND_Derivation_p NDDerivationAlloc(ProofState_p initial,WFormula_p goal);
WFormula_p NDSelectHighestScoreRandomly(FormulaSet_p input);
void NDScoreFormulaRandomly(WFormula_p input);
void NDScoreFormulaSetRandomly(FormulaSet_p input);
void NDInitializeDerivationGoal(ND_Derivation_p input, FormulaSet_p source);

WFormula_p NDSelectHighestScoreThroughSocket(FormulaSet_p input, int port);
WFormula_p NDSelectHighestScoreThroughFile(FormulaSet_p input);
char *WFormulaPrintString(WFormula_p input);

#endif
