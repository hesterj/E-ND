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
/*
typedef struct assumptioncell 
{
	WFormula_p goal;
	WFormula_p assumption;
	FormulaSet_p nd_derivation;
	
}TableauAssumption, *TableauAssumption_p;

#define TableauAssumptionCellAlloc() (TableauAssumption*)SizeMalloc(sizeof(TableauAssumption))
#define TableauAssumptionCellFree(junk) SizeFree(junk,sizeof(TableauAssumption))
TableauAssumption_p TableauAssumptionAlloc(WFormula_p goal,WFormula_p assumption);
void TableauAssumptionFree(TableauAssumption_p junk);
*/
WFormula_p TableauSelectHighestScoreRandomly(FormulaSet_p input);
void TableauScoreFormulaRandomly(WFormula_p input);
void TableauScoreFormulaSetRandomly(FormulaSet_p input);
//bool TableauCheckIfFormulaIsInstantiationOfExistential(Tableau_p control, WFormula_p existential, WFormula_p instantiation); //cant be in this file
//void TableauInitializeDerivationGoal(TableauAssumption_p input, FormulaSet_p source);

WFormula_p TableauSelectHighestScoreThroughSocket(FormulaSet_p input, int port);
WFormula_p TableauSelectHighestScoreThroughFile(FormulaSet_p input);
long TableauFormulaWeight(WFormula_p input);
char *WFormulaPrintString(WFormula_p input);

bool FormulaSetContainsFormula(FormulaSet_p set, WFormula_p formula);

#endif
