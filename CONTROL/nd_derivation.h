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

typedef struct assumptioncell 
{
	WFormula_p goal;
	WFormula_p assumption;
	FormulaSet_p nd_derivation;
	
}NDAssumption, *NDAssumption_p;

#define NDAssumptionCellAlloc() (NDAssumption*)SizeMalloc(sizeof(NDAssumption))
#define NDAssumptionCellFree(junk) SizeFree(junk,sizeof(NDAssumption))
NDAssumption_p NDAssumptionAlloc(WFormula_p goal,WFormula_p assumption);
void NDAssumptionFree(NDAssumption_p junk);

WFormula_p NDSelectHighestScoreRandomly(FormulaSet_p input);
void NDScoreFormulaRandomly(WFormula_p input);
void NDScoreFormulaSetRandomly(FormulaSet_p input);
void NDInitializeDerivationGoal(NDAssumption_p input, FormulaSet_p source);

WFormula_p NDSelectHighestScoreThroughSocket(FormulaSet_p input, int port);
WFormula_p NDSelectHighestScoreThroughFile(FormulaSet_p input);
char *WFormulaPrintString(WFormula_p input);

#endif
