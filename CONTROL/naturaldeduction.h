#ifndef NATURALDEDUCTION

#define NATURALDEDUCTION

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
#include <nd_derivation.h>
#include <time.h>
#include <arpa/inet.h>

typedef struct tableau 
{
	PStack_p derivation;
	PStack_p absolutely_flagged_variables;
	PStack_p relatively_flagged_variables;
	
	PStack_p predicates;
	PStack_p functions;
	
	FormulaSet_p nd_derivation;
	FormulaSet_p nd_generated;
	FormulaSet_p nd_temporary_formulas;
	FormulaSet_p branch_formulas; // the formulas that are exlusive to this branch
	
	long generated_formulas;
	VarBank_p     freshvars;
	TB_p          terms;
	Sig_p         signature;
	
	WFormula_p goal;
	WFormula_p last_assumption;
	
	bool active;
	
   struct nd_set_cell* set;      /* Is the formula in a set? */
   struct tableau* pred;        /* For fomula sets = doubly  */
   struct tableau* succ;        /* linked lists */
	
}Tableau, *Tableau_p;

/*
typedef struct connectioncell
{
	
}
*/

#define TableauCellAlloc() (Tableau*)SizeMalloc(sizeof(Tableau))
#define TableauCellFree(junk) SizeFree(junk, sizeof(Tableau))
Tableau_p TableauAlloc(ProofState_p initial);
Tableau_p TableauAllocAssumption(Tableau_p initial);
void TableauAssumptionControlFree(Tableau_p initial);
void TableauFree(Tableau_p initial);
void TableauCloseAssumption(Tableau_p initial);

WFormula_p TableauAndIntroduction(Tableau_p control, TB_p bank, WFormula_p a, WFormula_p b);
WFormula_p TableauOrIntroduction(Tableau_p control, TB_p bank, WFormula_p a, WFormula_p b);
WFormula_p TableauImplIntroduction(Tableau_p control,TB_p bank, WFormula_p a, WFormula_p b);
WFormula_p TableauNegIntroduction(Tableau_p control,TB_p bank, WFormula_p a, WFormula_p b, WFormula_p c);
WFormula_p TableauUniversalIntroduction(Tableau_p control,TB_p bank, Term_p term, Term_p variable, WFormula_p formula);
WFormula_p TableauExistentialIntroduction(Tableau_p control,TB_p bank, Term_p term, Term_p variable, WFormula_p formula);

WFormula_p TableauAndElimination(Tableau_p control,TB_p bank, WFormula_p conjunct, int select);
WFormula_p TableauOrElimination(Tableau_p control,TB_p bank, WFormula_p a,WFormula_p b);
WFormula_p TableauImplElimination(Tableau_p control,TB_p bank, WFormula_p a,WFormula_p b);
WFormula_p TableauNegationElimination(Tableau_p control,TB_p bank, WFormula_p a);
WFormula_p TableauUniversalElimination(Tableau_p control,TB_p bank, WFormula_p a, Term_p substitute);
WFormula_p TableauExistentialElimination(Tableau_p control,TB_p bank, WFormula_p a, Term_p substitute);  // Quine
WFormula_p TableauExistentialElimination2(Tableau_p control,TB_p bank, WFormula_p existential, WFormula_p psi);  //Gentzen

long TableauAndIntProcess(Tableau_p control,TB_p bank,WFormula_p selected);
long TableauOrIntProcess(Tableau_p control,TB_p bank,WFormula_p selected);
long TableauImplIntProcess(Tableau_p control,TB_p bank,WFormula_p selected);
long TableauNegIntProcess(Tableau_p control,TB_p bank,WFormula_p selected);
long TableauUniversalIntProcess(Tableau_p control,TB_p bank,WFormula_p selected);
long TableauExistentialIntProcess(Tableau_p control,TB_p bank,WFormula_p selected);

WFormula_p TableauEqualityIntroduction(Tableau_p control, TB_p bank, Term_p term);
WFormula_p TableauEqualityEliminationLeft(Tableau_p control, TB_p bank, WFormula_p substituted, WFormula_p equality);
WFormula_p TableauEqualityEliminationRight(Tableau_p control, TB_p bank, WFormula_p substituted, WFormula_p equality);
long TableauEqualityEliminationProcess(Tableau_p control, TB_p bank, WFormula_p selected);

long TableauOrElimProcess(Tableau_p control,TB_p bank,WFormula_p selected);
long TableauAndElimProcess(Tableau_p control,TB_p bank,WFormula_p selected);
long TableauImplElimProcess(Tableau_p control,TB_p bank,WFormula_p selected);
long TableauNegElimProcess(Tableau_p control,TB_p bank,WFormula_p selected);
long TableauUniversalElimProcess(Tableau_p control,TB_p bank,WFormula_p selected);
long TableauExistentialElimProcess(Tableau_p control,TB_p bank,WFormula_p selected);


/*
int TableauSaturate(ProofState_p state, ProofControl_p control, long
                  step_limit, long proc_limit, long unproc_limit, long
                  total_limit,  long generated_limit, long tb_insert_limit,
                  long answer_limit);
*/
void TableauGenerateAndScoreFormulas(Tableau_p ndcontrol, WFormula_p handle);
int TableauStartNewAssumption(Tableau_p ndcontrol, int socketDescriptor);

//void TableauProofSearch(Tableau_p control,Tableau_Derivation_p derivation);
bool TableauFormulaSetCheckForContradictions(Tableau_p control, FormulaSet_p formulaset);
bool TableauUnify(Tableau_p control, Subst_p subst, Term_p s, Term_p t);
//bool TableauAssumptionCheckForContradictions(TableauAssumption_p derivation);
//bool TableauAssumptionGoalIsReached(Tableau_p control,TableauAssumption_p derivation);

void TableauPInitializeDerivationGoal(Tableau_p input, FormulaSet_p source);
bool TableauPDerivationGoalIsReached(Tableau_p control);

void pstack_push_skip(PStack_p target, PStack_p source, Term_p skip);
long nd_term_collect_subterms(Sig_p sig, Term_p term, PStack_p collector);
long nd_collect_subterms(Tableau_p control, Sig_p sig, Term_p term, PStack_p collector);
long nd_collect_subterms2(Tableau_p control, Sig_p sig, Term_p term, PStack_p collector);
long nd_label_symbols(Tableau_p control,Term_p term);
void TableauSaturateLoop(Tableau_p ndcontrol, long loops);
void ProofTest(Tableau_p ndcontrol);
void ContradictionTest(Tableau_p ndcontrol);

void TableauResetState(Tableau_p ndcontrol);
                  
// inline functions
                  
static __inline__ bool PStackFindInt(PStack_p res, FunCode handle);
static __inline__ bool PStackFindTerm(PStack_p res, Term_p handle);
static __inline__ bool FunCodeIsPredicate(Tableau_p res, FunCode handle);
static __inline__ bool FunCodeIsFunction(Tableau_p res, FunCode handle);
static __inline__ PStack_p PStackRemoveDuplicatesInt(PStack_p handle);
static __inline__ PStack_p PStackRemoveDuplicatesTerm(PStack_p handle);
static __inline__ void PStackPrintFunCodes(Tableau_p control, PStack_p handle);
static __inline__ void UpdateControlSymbols(Tableau_p control);
//static void PStackPrintTerms(Tableau_p control, PStack_p handle);

#define TableauAbsolutelyFlagTerm(control,term) PStackPushP(control->absolutely_flagged_variables,term)
#define TableauRelativelyFlagTerms(control,stack) PStackPushStack(control->relatively_flagged_variables,stack)
#define TableauTermIsAbsolutelyFlagged(control,term) PStackFindTerm(control->absolutely_flagged_variables,term)
#define TableauTermIsRelateivelyFlagged(control,term) PStackFindTerm(control->relatively_flagged_variables,term)

// remove duplicates in the predicates and function stacks

void FormulaSetUpdateControlSymbols(Tableau_p control, FormulaSet_p target);

/*  Inline function definitions
*/


static __inline__ void UpdateControlSymbols(Tableau_p control)
{
   PStack_p predicates_duplicates_removed = PStackRemoveDuplicatesInt(control->predicates);
   PStack_p functions_duplicates_removed = PStackRemoveDuplicatesInt(control->functions);
   control->predicates = predicates_duplicates_removed;
   control->functions = functions_duplicates_removed;
}

//  check if funcode is predicate symbol

static __inline__ bool FunCodeIsPredicate(Tableau_p res, FunCode handle)
{
	return PStackFindInt(res->predicates,handle);
}

// check if funcode is function symbol

static __inline__ bool FunCodeIsFunction(Tableau_p res, FunCode handle)
{
	return PStackFindInt(res->functions,handle);
}

//  returns true if handle is an element of res

static __inline__ bool PStackFindInt(PStack_p res, FunCode handle)
{
   PStackPointer i;

   for(i=0; i<PStackGetSP(res); i++)
   {
      if (PStackElementInt(res,i) == handle)
      {
		  return true;
	  }
   }
   return false;
}

//  look for duplicate Term_p in res

static __inline__ bool PStackFindTerm(PStack_p res, Term_p handle)
{
   PStackPointer i;

   for(i=0; i<PStackGetSP(res); i++)
   {
      if (TermStructEqual(PStackElementP(res,i),handle))
      {
		  return true;
	  }
   }
   return false;
}

// returns copy of handle with duplicates removed

static __inline__ PStack_p PStackRemoveDuplicatesInt(PStack_p handle)
{
	PStackPointer i;
	PStack_p res = PStackAlloc();
	for(i=0; i<PStackGetSP(handle); i++)
	{
		if (!PStackFindInt(res,PStackElementInt(handle,i)))
		{
			PStackPushInt(res,PStackElementInt(handle,i));
		}
	}
	PStackFree(handle);
	return res;
}

// unfinished

static __inline__ PStack_p PStackRemoveDuplicatesTerm(PStack_p handle)
{
	PStackPointer i;
	PStack_p res = PStackAlloc();
	for(i=0; i<PStackGetSP(handle); i++)
	{
		if (!PStackFindTerm(res,PStackElementP(handle,i)))
		{
			PStackPushP(res,PStackElementP(handle,i));
		}
	}
	return res;
}

// print the funcodes in the stack handle

static __inline__ void PStackPrintFunCodes(Tableau_p control, PStack_p handle)
{
	PStackPointer i;
	for(i=0; i<PStackGetSP(handle); i++)
	{
		printf("\n%s",SigFindName(control->signature,PStackElementInt(handle,i)));
	}
}



#endif
