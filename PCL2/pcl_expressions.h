/*-----------------------------------------------------------------------

File  : pcl_expressions.h

Author: Stephan Schulz

Contents
 
  PCL2 expressions and uexpressions.

  Copyright 1998, 1999 by the author.
  This code is released under the GNU General Public Licence.
  See the file COPYING in the main CLIB directory for details.
  Run "eprover -h" for contact information.

Changes

<1> Mon Mar 27 15:10:31 MET DST 2000
    New

-----------------------------------------------------------------------*/

#ifndef PCL_EXPRESSIONS

#define PCL_EXPRESSIONS

#include <can_infstate.h>
#include <pcl_idents.h>
#include <pcl_positions.h>

/*---------------------------------------------------------------------*/
/*                    Data type declarations                           */
/*---------------------------------------------------------------------*/


typedef enum
{
   PCLOpNoOp,
   PCLOpInitial,
   PCLOpQuote,
   PCLOpParamod,
   PCLOpEResolution,
   PCLOpEFactoring,
   PCLOpSimplifyReflect,
   PCLOpACResolution,
   PCLOpRewrite,
   PCLOpURewrite,
   PCLOpClauseNormalize,
   PCLOpSplitClause
}PCLOpcodes;


typedef struct pclexprcell
{
   PCLOpcodes op;
   long       arg_no;
   PDArray_p  args; /* 2 Words per arg: argument, position */
}PCLExprCell, *PCLExpr_p;


#define PCL_VAR_ARG -1

/*---------------------------------------------------------------------*/
/*                Exported Functions and Variables                     */
/*---------------------------------------------------------------------*/

#define PCLExprCellAlloc() (PCLExprCell*)SizeMalloc(sizeof(PCLExprCell))
#define PCLExprCellFree(junk)        SizeFree(junk, sizeof(PCLExprCell))

#define PCLExprArg(expr,i)     PDArrayElementP((expr)->args,2*(i))
#define PCLExprArgInt(expr,i)  PDArrayElementInt((expr)->args,2*(i))
#define PCLExprArgPos(expr,i)  PDArrayElementP((expr)->args,2*(i)+1)

PCLExpr_p PCLExprAlloc();
void      PCLExprFree(PCLExpr_p junk);

PCLExpr_p PCLExprParse(Scanner_p in, bool mini);
#define   PCLFullExprParse(in) PCLExprParse((in),false)
#define   PCLMiniExprParse(in) PCLExprParse((in),true)

void      PCLExprPrint(FILE* out, PCLExpr_p expr, bool mini);
#define   PCLFullExprPrint(out, expr) PCLExprPrint((out),(expr),false)
#define   PCLMiniExprPrint(out, expr) PCLExprPrint((out),(expr),true)

/* MiniExprs are the same basic data type. However, MiniPCL-Ids are
   just plain longs, not full PCL identifiers */

void      PCLMiniExprFree(PCLExpr_p junk);

#endif

/*---------------------------------------------------------------------*/
/*                        End of File                                  */
/*---------------------------------------------------------------------*/





