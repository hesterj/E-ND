/*-----------------------------------------------------------------------

File  : che_hcb.h

Author: Stephan Schulz

Contents
 
  Heuristic control blocks, describing heuristics for clause
  selection.

  Copyright 1998, 1999 by the author.
  This code is released under the GNU General Public Licence.
  See the file COPYING in the main CLIB directory for details.
  Run "eprover -h" for contact information.

Changes

<1> Fri Jun  5 22:25:02 MET DST 1998
    New
<2> Wed Dec 16 23:17:21 MET 1998
    Integrate HeuristicParms stuff

-----------------------------------------------------------------------*/

#ifndef CHE_HCB

#define CHE_HCB

#include <clb_dstacks.h>
#include <ccl_paramod.h>
#include <ccl_splitting.h>
#include <che_to_weightgen.h>
#include <che_to_precgen.h>
#include <ccl_unit_simplify.h>
#include <che_wfcbadmin.h>
#include <che_litselection.h>


/*---------------------------------------------------------------------*/
/*                    Data type declarations                           */
/*---------------------------------------------------------------------*/


/* Possible ways to handle AC */

typedef enum
{
   NoACHandling,
   ACDiscardAll,
   ACKeepUnits,
   ACKeepOrientable
}ACHandlingType;


/* External parameters for heuristics and proof control */

typedef struct heuristic_parms_cell
{
   char                *heuristic_name;
   PStack_p            wfcb_definitions;
   PStack_p            hcb_definitions;
   TermOrdering        ordertype;
   TOWeightGenMethod   to_weight_gen;
   TOPrecGenMethod     to_prec_gen;
   char*               to_pre_prec;
   long                to_const_weight;
   long                filter_limit;
   long                filter_copies_limit;
   long                reweight_limit;
   long                delete_bad_limit;
   rlim_t              mem_limit;
   ACHandlingType      ac_handling;
   bool                ac_res_aggressive;
   bool                forward_context_sr;
   bool                forward_context_sr_aggressive;
   bool                backward_context_sr;
   bool                no_lit_cmp;
   RewriteLevel        forward_demod;
   bool                prefer_general;
   bool                er_varlit_destructive;
   bool                er_strong_destructive;
   bool                er_aggressive;
   bool                prefer_initial_clauses;
   bool                select_on_proc_only;
   bool                inherit_paramod_lit;
   bool                inherit_goal_pm_lit;
   LiteralSelectionFun selection_strategy;
   long                pos_lit_sel_min; 
   long                pos_lit_sel_max; 
   long                neg_lit_sel_min; 
   long                neg_lit_sel_max; 
   long                all_lit_sel_min; 
   long                all_lit_sel_max; 
   long                weight_sel_min;
   SplitClassType      split_clauses;
   SplitType           split_method;
   bool                split_aggressive;
   UnitSimplifyType    unproc_simplify;
   bool                use_tptp_sos;
}HeuristicParmsCell, *HeuristicParms_p;



/* An HCBCell describes a heuristic for clause selection. There are
   two main elemenats: A list of clause evaluation functions
   (described by a WFCB-List and a clause selection function (whose
   data is kept in the HBCCell). */

typedef struct hcb_cell
{
   /* List and number of weight function used by the heuristic. Take
      care: The list of WFCBs is ordered in the opposite direction
      from the evaluation in a clause, i.e. the _last_ WCFB will
      create the _first_ evaluation. */
   PDArray_p       wfcb_list;
   int             wfcb_no;

   /* Evaluation currently used for selection. This refers to the
      order of evaluations in the clause. See above!       */
   int             current_eval;

   /* Switching for HCBStandardClauseSelect and possibly other
      selection functions: Whenever select_count modulo
      select_switch[wfcb_no-1] reaches select_switch[current_eval],
      current_eval is increased modulo wfcb_no. */
   PDArray_p       select_switch;
   long            select_count;
   
   /* Selection function, this function is called to select an
      unprocessed clause from the set */
   Clause_p        (*hcb_select)(struct hcb_cell* hcb, ClauseSet_p
				 set);
   
   /* Some HCB selection or evaluation functions may need data of
      their own. If yes, their creation function can allocate data,
      and needs to register a cleanup-function here. This function is
      only called if data != NULL. */
   GenericExitFun  hcb_exit;
   void*           data;
}HCBCell, *HCB_p;

#define HCB_DEFAULT_HEURISTIC "Default"
#define DEFAULT_FILTER_LIMIT LONG_MAX
#define DEFAULT_FILTER_COPIES_LIMIT LONG_MAX
#define DEFAULT_REWEIGHT_INTERVAL LONG_MAX
#define DEFAULT_DELETE_BAD_LIMIT LONG_MAX

typedef Clause_p (*ClauseSelectFun)(HCB_p hcb, ClauseSet_p set);


/*---------------------------------------------------------------------*/
/*                Exported Functions and Variables                     */
/*---------------------------------------------------------------------*/

#define HeuristicParmsCellAlloc() \
   (HeuristicParmsCell*)SizeMalloc(sizeof(HeuristicParmsCell))
#define HeuristicParmsCellFree(junk) \
   SizeFree(junk, sizeof(HeuristicParmsCell))

HeuristicParms_p HeuristicParmsAlloc(void);
void             HeuristicParmsFree(HeuristicParms_p junk);


#define HCBCellAlloc() (HCBCell*)SizeMalloc(sizeof(HCBCell))
#define HCBCellFree(junk)        SizeFree(junk, sizeof(HCBCell))

HCB_p    HCBAlloc(void);
void     HCBFree(HCB_p junk);
long     HCBAddWFCB(HCB_p hcb, WFCB_p wfcb, long steps);
void     HCBClauseEvaluate(HCB_p hcb, Clause_p clause);
Clause_p HCBStandardClauseSelect(HCB_p hcb, ClauseSet_p set);
Clause_p HCBSingleWeightClauseSelect(HCB_p hcb, ClauseSet_p set);

long     HCBClauseSetDelProp(HCB_p hcb, ClauseSet_p set, long number,
			     ClauseProperties prop);
long HCBClauseSetDeleteBadClauses(HCB_p hcb, ClauseSet_p set, long
				  number);

#endif

/*---------------------------------------------------------------------*/
/*                        End of File                                  */
/*---------------------------------------------------------------------*/





