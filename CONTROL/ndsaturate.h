#ifndef TableauSATURATE

#define TableauSATURATE

#include <nd_derivation.h>
#include <ndset.h>
#include <naturaldeduction.h>

int TableauSaturate(ProofState_p state, ProofControl_p control, long
                  step_limit, long proc_limit, long unproc_limit, long
                  total_limit,  long generated_limit, long tb_insert_limit,
                  long answer_limit);
                 
int TableauStartNewAssumption(Tableau_p ndcontrol, int socketDescriptor);
bool TableauFormulaAlreadyKnown(Tableau_p control, WFormula_p formula);

#endif
