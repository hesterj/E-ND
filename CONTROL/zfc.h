#ifndef ZFC

#define ZFC

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

long compute_schemas_tform(ProofControl_p control, 
						   TB_p bank, 
						   OCB_p ocb, 
						   Clause_p clause,
						   ClauseSet_p store, 
						   VarBank_p freshvars, 
						   ProofState_p state);
TFormula_p tformula_comprehension(TB_p bank, 
								  ProofState_p state, 
								  PStack_p freevars, 
								  TFormula_p input);
ClauseSet_p tformula_replacement(TB_p bank, 
								ProofState_p state, 
								ClauseSet_p final,
								PStack_p freevars, 
								TFormula_p input,
								Clause_p clause);
Clause_p ClauseMergeVars(Clause_p clause,  TB_p bank, Term_p x, Term_p y);

WFormula_p WFormula_Comprehension(TB_p bank, 
								  ProofState_p state, 
								  PStack_p freevars, 
								  WFormula_p input);
WFormula_p FormulaMergeVars(WFormula_p formula,  TB_p bank, Term_p x, Term_p y);

#endif
