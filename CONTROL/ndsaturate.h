#ifndef NDSATURATE

#define NDSATURATE

#include <nd_derivation.h>
#include <ndset.h>
#include <naturaldeduction.h>

int NDSaturate(ProofState_p state, ProofControl_p control, long
                  step_limit, long proc_limit, long unproc_limit, long
                  total_limit,  long generated_limit, long tb_insert_limit,
                  long answer_limit);
                 
int NDStartNewAssumption(ND_p ndcontrol, int socketDescriptor);

#endif
