/*-----------------------------------------------------------------------

File  : ccl_formula_wrapper.c

Author: Stephan Schulz

Contents

  Wrapped formula code.

  Copyright 1998-2003 by the author.
  This code is released under the GNU General Public Licence.
  See the file COPYING in the main CLIB directory for details.
  Run "eprover -h" for contact information.

Changes

<1> Thu Nov 13 01:43:38 GMT 2003
    New

-----------------------------------------------------------------------*/

#include "ccl_formula_wrapper.h"



/*---------------------------------------------------------------------*/
/*                        Global Variables                             */
/*---------------------------------------------------------------------*/

long global_formula_counter = LONG_MIN;

/*---------------------------------------------------------------------*/
/*                      Forward Declarations                           */
/*---------------------------------------------------------------------*/


/*---------------------------------------------------------------------*/
/*                         Internal Functions                          */
/*---------------------------------------------------------------------*/



/*---------------------------------------------------------------------*/
/*                         Exported Functions                          */
/*---------------------------------------------------------------------*/

/*-----------------------------------------------------------------------
//
// Function: DefaultWFormulaAlloc()
//
//   Allocate and return a wrapped formula cell with all values
//   initialized to rational default values.
//
// Global Variables: -
//
// Side Effects    : Memory operations
//
/----------------------------------------------------------------------*/

WFormula_p DefaultWFormulaAlloc()
{
   WFormula_p handle = WFormulaCellAlloc();
   
   handle->properties = WPIgnoreProps; 
   handle->ident      = 0;
   handle->info       = NULL;
   handle->formula    = 0;
   handle->set        = NULL;
   handle->pred       = NULL;
   handle->succ       = NULL;

   return handle;
}

/*-----------------------------------------------------------------------
//
// Function: WFormulaAlloc()
//
//   Allocate a wrapped formula given the essential information. id
//   will automagically be set to a new value.
//
// Global Variables: FormulaIdentCounter
//
// Side Effects    : Via DefaultWFormulaAlloc()
//
/----------------------------------------------------------------------*/

WFormula_p WFormulaAlloc(Formula_p formula)
{
   WFormula_p handle = DefaultWFormulaAlloc();
   
   handle->formula = FormulaGetRef(formula);
   handle->ident   = ++global_formula_counter;   
   
   return handle;
}


/*-----------------------------------------------------------------------
//
// Function: WFormulaFree()
//
//   Free a wrapped formula.
//
// Global Variables: -
//
// Side Effects    : Memory operations
//
/----------------------------------------------------------------------*/

void WFormulaFree(WFormula_p form)
{
   assert(form);
   assert(form->formula);
   assert(!form->set);
   assert(!form->pred);
   assert(!form->succ);
   
   FormulaRelRef(form->formula);
   FormulaFree(form->formula);
   ClauseInfoFree(form->info);
   WFormulaCellFree(form);
}


/*-----------------------------------------------------------------------
//
// Function: WFormulaTPTPParse()
//
//   Parse a formula in TPTP format.
//
// Global Variables: -
//
// Side Effects    : Input
//
/----------------------------------------------------------------------*/

WFormula_p WFormulaTPTPParse(Scanner_p in, TB_p terms)
{
   char*              name;
   Formula_p          form;
   WFormulaProperties type;
   WFormula_p         handle;
   ClauseInfo_p       info;

   info = ClauseInfoAlloc(NULL, DStrView(AktToken(in)->source), 
                          AktToken(in)->line, 
                          AktToken(in)->column); 
   AcceptInpId(in, "input_formula");
   AcceptInpTok(in, OpenBracket);  
   CheckInpTok(in, Name|PosInt);
   info->name = DStrCopy(AktToken(in)->literal);
   name = DStrCopy(AktToken(in)->literal);
   NextToken(in);
   AcceptInpTok(in, Comma);
   CheckInpId(in, "axiom|hypothesis|negated_conjecture|conjecture|lemma|unknown");
   if(TestInpId(in, "conjecture"))
   {
      type = WPTypeConjecture;
   }
   else if(TestInpId(in, "negated_conjecture"))
   {
      type = WPTypeNegConjecture;
   }
   else if(TestInpId(in, "hypothesis"))
   {
      type = WPTypeHypothesis;
   }
   else
   {
      type = WPTypeAxiom;
   }
   NextToken(in);
   AcceptInpTok(in, Comma);
   form = FormulaTPTPParse(in, terms); /* TSTP = TPTP! */
   AcceptInpTok(in, CloseBracket);
   AcceptInpTok(in, Fullstop);
   handle = WFormulaAlloc(form);
   FormulaSetType(handle, type);
   FormulaSetProp(handle, WPInitial|WPInputFormula);
   handle->info = info;

   return handle;
}

/*-----------------------------------------------------------------------
//
// Function: FormulaTPTPPrint()
//
//   Print a formula in TPTP format.
//
// Global Variables: -
//
// Side Effects    : 
//
/----------------------------------------------------------------------*/

void WFormulaTPTPPrint(FILE* out, WFormula_p form, bool fullterms)
{
   char *typename;
   char prefix;
   long id;

   switch(FormulaQueryType(form))
   {
   case WPTypeAxiom:
         typename = "axiom";
	 break;
   case WPTypeHypothesis:
	 typename = "hypothesis";
	 break;       
   case WPTypeConjecture:
   case WPTypeNegConjecture:
	 typename = "conjecture";
	 break;
   default:
	 typename = "unknown";
	 break;
   }   
   if(form->ident < 0)
   {
      id = form->ident - LONG_MIN;
      prefix = 'i';
   }
   else
   {
      id = form->ident;
      prefix = 'e';
   }
   fprintf(out, "input_formula(f%c_%ld,%s,", prefix, id, typename);
   FormulaTPTPPrint(out, form->formula,fullterms);
   fprintf(out,").");   
}


/*-----------------------------------------------------------------------
//
// Function: WFormulaTSTPParse()
//
//   Parse a formula in TSTP format.
//
// Global Variables: -
//
// Side Effects    : Input
//
/----------------------------------------------------------------------*/

WFormula_p WFormulaTSTPParse(Scanner_p in, TB_p terms)
{
   char*              name;
   Formula_p          form;
   WFormulaProperties type = WPTypeAxiom;
   WFormulaProperties initial = WPInputFormula;
   WFormula_p         handle;
   ClauseInfo_p       info;

   info = ClauseInfoAlloc(NULL, DStrView(AktToken(in)->source), 
                          AktToken(in)->line, 
                          AktToken(in)->column); 
      
   AcceptInpId(in, "fof");
   AcceptInpTok(in, OpenBracket);
   CheckInpTok(in, Name|PosInt);
   info->name = DStrCopy(AktToken(in)->literal);
   name = DStrCopy(AktToken(in)->literal);
   NextToken(in);
   AcceptInpTok(in, Comma);
   
   /* This is hairy! E's internal types do not map very well to
      TSTP types, and E uses the "initial" properties in ways that
      make it highly desirable that anything in the input is
      actually initial (the CPInitialProperty is actually set in
      all clauses in the initial unprocessed clause set. So we
      ignore the "derived" modifier, and use CPTypeAxiom for plain
      clauses. */
   if(TestInpId(in, "axiom|definition|knowledge|assumption|"
                "hypothesis|conjecture|negated_conjecture|"
                "lemma|unknown|plain"))
   {
      type = ClauseTypeParse(in, 
                             "axiom|definition|knowledge|assumption|"
                             "hypothesis|conjecture||negated_conjecture|"
                             "lemma|unknown|plain");
      if(TestInpTok(in, Hyphen))
      {
         AcceptInpTok(in, Hyphen);
         AcceptInpId(in, "derived");
         initial = WPIgnoreProps;
      }
   }
   else
   {
      AcceptInpId(in, "derived");
      initial = WPIgnoreProps;
      type = WPTypeAxiom;
   } 
   AcceptInpTok(in, Comma);
   form = FormulaTPTPParse(in, terms); /* TSTP = TPTP! */
   if(TestInpTok(in, Comma))
   {
      AcceptInpTok(in, Comma);
      TSTPSkipSource(in);
      if(TestInpTok(in, Comma))
      {
         AcceptInpTok(in, Comma);
         CheckInpTok(in, OpenSquare);
         ParseSkipParenthesizedExpr(in);
      }
   }
   AcceptInpTok(in, CloseBracket);
   AcceptInpTok(in, Fullstop);
   handle = WFormulaAlloc(form);
   FormulaSetType(handle, type);
   FormulaSetProp(handle, initial|WPInitial);
   handle->info = info;

   return handle;
}




/*-----------------------------------------------------------------------
//
// Function: WFormulaTSTPPrint()
//
//   Print a formula in TSTP format. If !complete, leave of the
//   trailing ")." for adding optional stuff.
//
// Global Variables: -
//
// Side Effects    : Output
//
/----------------------------------------------------------------------*/

void WFormulaTSTPPrint(FILE* out, WFormula_p form, bool fullterms,
		       bool complete)
{
   char *typename = NULL;
   char *derived = NULL; 
   char prefix;
   long id;

   switch(FormulaQueryType(form))
   {
   case WPTypeAxiom:
         if(FormulaQueryProp(form, WPInputFormula))
         {
            typename = "axiom";
         }
         break;
   case WPTypeHypothesis:
         typename = "hypothesis";
         break;      
   case WPTypeConjecture:
         typename = "conjecture";
         break;
   case WPTypeLemma:
         typename = "lemma";
         break; 
   case WPTypeNegConjecture:
         typename = "negated_conjecture";
         break;
   default:
	 break;
   }   
   if(!FormulaQueryProp(form, CPInputClause))
   {
      derived = "derived";
   }

   if(form->ident < 0)
   {
      id = form->ident - LONG_MIN;
      prefix = 'i';
   }
   else
   {
      id = form->ident;
      prefix = 'c';
   }
   fprintf(out, "fof(%c_0_%ld,", prefix, id);
   PrintDashedStatuses(out, typename, derived, "plain");
   fprintf(out, ",");   
   FormulaTPTPPrint(out, form->formula,fullterms);
   if(complete)
   {
      fprintf(out, ").");
   }
}


/*-----------------------------------------------------------------------
//
// Function: WFormulaParse()
//
//   Parse a formula in any supported input format.
//
// Global Variables: -
//
// Side Effects    : Input
//
/----------------------------------------------------------------------*/

WFormula_p WFormulaParse(Scanner_p in, TB_p terms)
{
   WFormula_p wform = NULL;

   if(ClausesHaveDisjointVariables)
   {
      VarBankClearExtNamesNoReset(terms->vars);
   }   
   switch(ScannerGetFormat(in))
   {
   case LOPFormat:
         Error("LOP currently does not support full FOF!", OTHER_ERROR);
         break;
   case TPTPFormat:
         wform = WFormulaTPTPParse(in, terms);
         break;
   case TSTPFormat:
         wform = WFormulaTSTPParse(in, terms);
         break;
   default:
         assert(false);
         break;
   }
   return wform;
}

/*-----------------------------------------------------------------------
//
// Function: WFormulaPrint()
//
//   Print a (wrapped) formula in the current output format.
//
// Global Variables: OutputFormat
//
// Side Effects    : Output
//
/----------------------------------------------------------------------*/

void WFormulaPrint(FILE* out, WFormula_p form, bool fullterms)
{
   switch(OutputFormat)
   {
   case LOPFormat:
      Warning("Currently no LOP FOF format, using TPTP");
   case TPTPFormat:
      WFormulaTPTPPrint(out, form, fullterms);
      break;
   case TSTPFormat:
      WFormulaTSTPPrint(out, form, fullterms, true);
      break;
   default:
         assert(false&& "Unknown output format");
         break;
   }
}


/*-----------------------------------------------------------------------
//
// Function: FormulaSetAlloc()
//
//   Allocate and initialize a formula set.
//
// Global Variables: -
//
// Side Effects    : Memory operations
//
/----------------------------------------------------------------------*/

FormulaSet_p FormulaSetAlloc()
{
   FormulaSet_p set = FormulaSetCellAlloc();

   set->members = 0;
   set->anchor  = WFormulaCellAlloc();
   set->anchor->succ = set->anchor;
   set->anchor->pred = set->anchor;
   
   return set;
}

/*-----------------------------------------------------------------------
//
// Function: FormulaSetFreeFormulas(set)
//
//   Free all formulas in set.
//
// Global Variables: -
//
// Side Effects    : Memory operations
//
/----------------------------------------------------------------------*/

void FormulaSetFreeFormulas(FormulaSet_p set)
{
   assert(set);

   while(!FormulaSetEmpty(set))
   {
      FormulaSetDeleteEntry(set->anchor->succ);
   }
}

/*-----------------------------------------------------------------------
//
// Function: FormulaSetFree(set)
//
//   Free a formula set (and all its formulas).
//
// Global Variables: -
//
// Side Effects    : Memory operations
//
/----------------------------------------------------------------------*/

void FormulaSetFree(FormulaSet_p set)
{
   assert(set);

   FormulaSetFreeFormulas(set);   
   WFormulaCellFree(set->anchor);
   FormulaSetCellFree(set);
}


/*-----------------------------------------------------------------------
//
// Function: FormulaSetInsert()
//
//   Insert newnode into set.
//
// Global Variables: -
//
// Side Effects    : -
//
/----------------------------------------------------------------------*/

void FormulaSetInsert(FormulaSet_p set, WFormula_p newform)
{
   assert(set);
   assert(newform);
   assert(!newform->set);
   
   newform->succ = set->anchor;
   newform->pred = set->anchor->pred;
   set->anchor->pred->succ = newform;
   set->anchor->pred = newform;
   newform->set = set;
   set->members++;
}

/*-----------------------------------------------------------------------
//
// Function: FormulaSetExtractEntry()
//
//   Extract a given formula from a formula set and return it.
//
// Global Variables: -
//
// Side Effects    : -
//
/----------------------------------------------------------------------*/

WFormula_p FormulaSetExtractEntry(WFormula_p form)
{
   assert(form);
   assert(form->set);

   form->pred->succ = form->succ;
   form->succ->pred = form->pred;
   form->set->members--;
   form->set = NULL;
   form->succ = NULL;
   form->pred = NULL;

   return form;
}

/*-----------------------------------------------------------------------
//
// Function: FormulaSetExtractFirst()
//
//   Extract and return the first formula from set, if any, otherwise
//   return NULL.
//
// Global Variables: 
//
// Side Effects    : 
//
/----------------------------------------------------------------------*/

WFormula_p FormulaSetExtractFirst(FormulaSet_p set)
{
   assert(set);

   if(FormulaSetEmpty(set))
   {
      return NULL;
   }
   return FormulaSetExtractEntry(set->anchor->succ);
}


/*-----------------------------------------------------------------------
//
// Function: FormulaSetDeleteEntry()
//
//   Delete an element of a formulaset.
//
// Global Variables: 
//
// Side Effects    : 
//
/----------------------------------------------------------------------*/

void FormulaSetDeleteEntry(WFormula_p form)
{
   assert(form);

   FormulaSetExtractEntry(form);
   WFormulaFree(form);
}



/*-----------------------------------------------------------------------
//
// Function: FormulaSetPrint()
//
//   Print a set of formulae.
//
// Global Variables: OutputFormat
//
// Side Effects    : -
//
/----------------------------------------------------------------------*/

void FormulaSetPrint(FILE* out, FormulaSet_p set, bool fullterms)
{
   WFormula_p handle;
   
   handle = set->anchor->succ;
   
   while(handle!=set->anchor)
   {
      WFormulaPrint(out, handle, fullterms);
      fputc('\n', out);
      handle = handle->succ;
   }
}



/*---------------------------------------------------------------------*/
/*                        End of File                                  */
/*---------------------------------------------------------------------*/


