/*-----------------------------------------------------------------------

File  : cte_termbanks.c

Author: Stephan Schulz

Contents
 
  Functions for term banks (efficient dag-representations for term
  sets). 

  Bindings (i.e. values in term->binding) make only sense in dynamical
  contexts, not in (mostly) static term banks. Thus, bindings are
  followed whenever a term is treated as an individual term, but not
  when they form part of a term bank and are manipulated as such.  

  Copyright 1998, 1999 by the author.
  This code is released under the GNU General Public Licence.
  See the file COPYING in the main CLIB directory for details.
  Run "eprover -h" for contact information.

Changes

<1> Sat Nov 15 16:26:30 MET 1997
    New
<2> Fri Oct  2 20:35:41 MET DST 1998
    Variables are now longer in the term trees and have lost superterm
    information -> 20% Speedup!
<3> You cannot take references for variables anymore. This requires
    that no variables are ever replaced (but this is a requirement
    anyways), but deals with a strange bug (and may speed up the code
    even more).
<4> Sat Apr  6 21:42:35 CEST 2002
    Changed for new rewriting. No Superterms anymore! References are
    fully passive. Deletion does not work any more, I'm working on a
    mark-and-sweep garbage collector for terms instead.

-----------------------------------------------------------------------*/

#include "cte_termbanks.h"



/*---------------------------------------------------------------------*/
/*                        Global Variables                             */
/*---------------------------------------------------------------------*/

bool TBPrintInternalInfo = false; /* Print internal information about
				     term nodes, e.g. the flag field */
bool TBPrintDetails = false;      /* Collect potentially expensive
				     information (number of nodes,
				     number of unshared nodes, size of
				     various sub-data structures) and
				     print them if required */


/*---------------------------------------------------------------------*/
/*                      Forward Declarations                           */
/*---------------------------------------------------------------------*/


/*---------------------------------------------------------------------*/
/*                         Internal Functions                          */
/*---------------------------------------------------------------------*/

/*-----------------------------------------------------------------------
//
// Function: tb_print_dag()
//
//   Print the terms as a dag in the order of insertion.
//
// Global Variables: TBPrintInternalInfo
//
// Side Effects    : Output
//
/----------------------------------------------------------------------*/

static void tb_print_dag(FILE *out, NumTree_p in_index, Sig_p sig)
{
   Term_p term;

   if(!in_index)
   {
      return;
   }
   tb_print_dag(out, in_index->lson, sig);
   term = in_index->val1.p_val;
   fprintf(out, "*%ld : ", term->entry_no);

   if(TermIsVar(term))
   {
      fprintf(out, "X%ld", -term->f_code);
   }
   else
   {
      fprintf(out, SigFindName(sig, term->f_code));
      if(!TermIsConst(term))
      {
	 int i;
	 
	 assert(term->arity>=1);
	 assert(term->args);
	 putc('(', out);
	 
	 fprintf(out, "*%ld", TBCellIdent(term->args[0]));
	 for(i=1; i<term->arity; i++)
	 {
	    putc(',', out);
	    fprintf(out, "*%ld", TBCellIdent(term->args[i]));
	 }
	 putc(')', out);
      }
   }
   if(TBPrintInternalInfo)
   {
      fprintf(out, "\t/*  Properties: %10d */",
	      term->properties);
   }
   fprintf(out, "\n");
   tb_print_dag(out, in_index->rson, sig);
}

/*-----------------------------------------------------------------------
//
// Function: tb_termtop_insert()
//
//   Insert a term into the term bank for which the subterms are
//   already in the term bank. Will reuse or destroy the top cell!
//
// Global Variables: TBSupportReplace
//
// Side Effects    : Changes term bank
//
/----------------------------------------------------------------------*/

static Term_p tb_termtop_insert(TB_p bank, Term_p t)
{
   Term_p new;

   assert(t);
   assert(!TermIsVar(t));

   new = TermCellStoreInsert(&(bank->term_store), t, bank->prop_mask);
   
   if(new) /* Term node already existed, just add properties */
   {
      new->properties = (new->properties | t->properties)/*& bank->prop_mask*/; 
      TermTopFree(t);
      return new;
   }
   else
   {
      int i;

      t->entry_no     = ++(bank->in_count);
      TermCellAssignProp(t,TPGarbageFlag, bank->garbage_state);      
      TermCellSetProp(t, TPIsShared); /* Now it becomes a shared cell! */

      t->weight = DEFAULT_FWEIGHT;
      for(i=0; i<t->arity; i++)
      {
	 assert(TermIsShared(t->args[i])||TermIsVar(t->args[i]));
	 t->weight+=t->args[i]->weight;
      }
      assert(TermStandardWeight(t) == 
	     TermWeight(t, DEFAULT_VWEIGHT, 
			DEFAULT_FWEIGHT));
   }
   return t;
}


/*-----------------------------------------------------------------------
//
// Function: tb_parse_cons_list()
//
//   Parse a LOP list into an (shared) internal $cons list.
//
// Global Variables: -
//
// Side Effects    : Input, Memory operations
//
/----------------------------------------------------------------------*/

static Term_p tb_parse_cons_list(Scanner_p in, TB_p bank)
{
   Term_p   handle;
   Term_p   current;
   PStack_p stack;
   
   assert(SigSupportLists);
   
   stack = PStackAlloc();
   AcceptInpTok(in, OpenSquare);

   handle = DefaultSharedTermCellAlloc();
   current = handle;
   
   if(!TestInpTok(in, CloseSquare))
   {

      current->f_code = SIG_CONS_CODE;
      current->arity = 2;
      current->args = TermArgArrayAlloc(2);
      current->args[0] = TBTermParse(in, bank); 
      current->args[1] = DefaultSharedTermCellAlloc();
      current = current->args[1];
      PStackPushP(stack, current);
      
      while(TestInpTok(in, Comma))
      {
         NextToken(in);
         current->f_code = SIG_CONS_CODE;             
         current->arity = 2;                          
         current->args = TermArgArrayAlloc(2);
         current->args[0] = TBTermParse(in, bank); 
         current->args[1] = TermDefaultCellAlloc();
         current = current->args[1];      
	 PStackPushP(stack, current);
      }
      current = PStackPopP(stack);
   }
   AcceptInpTok(in, CloseSquare);
   current->f_code = SIG_NIL_CODE;             
   
   /* Now insert the list into the bank */
   handle = tb_termtop_insert(bank, current);

   while(!PStackEmpty(stack))
   {
      current = PStackPopP(stack);
      current->args[1] = handle;
      handle = tb_termtop_insert(bank, current);
   }
   
   PStackFree(stack);
   return handle;
}
   


/*---------------------------------------------------------------------*/
/*                         Exported Functions                          */
/*---------------------------------------------------------------------*/

/*-----------------------------------------------------------------------
//
// Function: TBAlloc()
//
//   Allocate an empty, initialized termbank.
//
// Global Variables: -
//
// Side Effects    : Memory operations
//
/----------------------------------------------------------------------*/

TB_p TBAlloc(TermProperties prop_mask, Sig_p sig)
{
   TB_p handle;
   Term_p t, term;

   handle = TBCellAlloc();

   handle->prop_mask = prop_mask;
   handle->in_count = 0;
   handle->rewrite_steps = 0;
   handle->ext_index = PDIntArrayAlloc(1,100000);
   handle->garbage_state = TPIgnoreProps;
   handle->sig = sig;
   handle->vars = VarBankAlloc();
   TermCellStoreInit(&(handle->term_store)); 

   term = TermDefaultCellAlloc();
   term->f_code = SIG_TRUE_CODE;
   TermCellSetProp(term, TPPredPos);
   t = TBInsert(handle, term, DEREF_NEVER);
   TermGetRef(&(handle->true_term), t);
   TermFree(term);

   return handle;
}


/*-----------------------------------------------------------------------
//
// Function: TBFree()
//
//   Free a term bank (if the signature alread has been
//   extracted). Voids all pointers to terms in the bank!
//
// Global Variables: -
//
// Side Effects    : Memory operations.
//
/----------------------------------------------------------------------*/

void TBFree(TB_p junk)
{
   assert(!junk->sig);
   
   /* printf("TBFree(): %ld\n", TermCellStoreNodes(&(junk->term_store)));
    */
   TermCellStoreExit(&(junk->term_store));
   PDArrayFree(junk->ext_index);
   VarBankFree(junk->vars);
   
   TBCellFree(junk);
}


/*-----------------------------------------------------------------------
//
// Function: TBTermNodes()
//
//   Return the number of term nodes (variables and non-variables) in
//   the term bank.
//
// Global Variables: -
//
// Side Effects    : -
//
/----------------------------------------------------------------------*/

long TBTermNodes(TB_p bank)
{
   assert(TermCellStoreNodes(&(bank->term_store))==
	  TermCellStoreCountNodes(&(bank->term_store)));
   return TermCellStoreNodes(&(bank->term_store))+
      PDArrayMembers(bank->vars->f_code_index);
}

/*-----------------------------------------------------------------------
//
// Function: DefaultSharedTermCellAlloc()
//
//   Return a reasonably initialized term cell for shared terms.
//
// Global Variables: -
//
// Side Effects    : Memory Operations
//
/----------------------------------------------------------------------*/

Term_p DefaultSharedTermCellAlloc(void)
{
   Term_p handle;

   handle = TermDefaultCellAlloc();
   TermCellSetProp(handle, TPIsShared);
   
   return handle;
}

/*-----------------------------------------------------------------------
//
// Function: TermGetRef()
//
//   Make ref a registered pointer to term, i.e. a pointer the term.
//   This is a left-over from the old rewriting, and probably could be
//   replaced by a simple assignment. I'm leaving it in because a) I'm
//   lazy and b) I might want to revert to reference counting at some
//   time. 
//
// Global Variables: -
//
// Side Effects    : Changes *ref.
//
/----------------------------------------------------------------------*/

void TermGetRef(Term_p *ref, Term_p term)
{
   assert(ref);
   assert(term);
   
   *ref = term;
}


/*-----------------------------------------------------------------------
//
// Function: TermReleaseRef()
//
//   !!! This is now a dummy. See TermGetRef above. !!!
//   Remove the external reference. Does not change the reference - it
//   can still be used, but will no longer be updated. This allows
//   TBDelete() to be called on this term easily. 
//
// Global Variables: -
//
// Side Effects    : Changes reference tree of term.
//
/----------------------------------------------------------------------*/

void TermReleaseRef(Term_p *ref)
{
   assert(ref);
   assert(*ref);
}


/*-----------------------------------------------------------------------
//
// Function: TBTermStructEqual()
//
//   Tests, wether two terms in the same termbank are structurally
//   identical (ignoring bindings).
//
// Global Variables: -
//
// Side Effects    : -
//
/----------------------------------------------------------------------*/

bool TBTermStructEqual(Term_p t1, Term_p t2)
{
   PStack_p stack = PStackAlloc();
   int i;
   bool termeq = true;

   PStackPushP(stack, t1);
   PStackPushP(stack, t2);
   
   while(!PStackEmpty(stack))
   {
      t2 = PStackPopP(stack);
      t1 = PStackPopP(stack);

      if(t1 == t2)
      {
	 continue;
      }
      else if(t1->f_code != t2->f_code)
      {
	 termeq = false;
	 break;
      }
      assert(t1->arity == t2->arity);
      for(i=0; i<t1->arity; i++)
      {
	 PStackPushP(stack, t1->args[i]);
	 PStackPushP(stack, t2->args[i]);
      }
   }
   PStackFree(stack);
   return termeq;
}

/*-----------------------------------------------------------------------
//
// Function: TBInsert()
//
//  Insert the term into the termbank. The original term will remain
//  untouched. The routine returns a pointer to a new, shared term of
//  the same structure.
//
//  TermProperties are masked with bank->prop_mask.
//
// Global Variables: -
//
// Side Effects    : Changes term bank
//
/----------------------------------------------------------------------*/

Term_p TBInsert(TB_p bank, Term_p term, DerefType deref)
{
   int    i;
   Term_p t;

   assert(term);

   term = TermDeref(term, &deref);

   t = TermEquivCellAlloc(term, bank->vars); /* This is an unshared
						term cell at the
						moment, */
   if(!TermIsVar(t))
   {
      assert(SysDateIsCreationDate(t->rw_data.nf_date[0]));
      assert(SysDateIsCreationDate(t->rw_data.nf_date[1]));
      
      for(i=0; i<t->arity; i++)
      {
	 t->args[i] = TBInsert(bank, t->args[i], deref);
      }
      t = tb_termtop_insert(bank, t);
   }
   return t;
}

/*-----------------------------------------------------------------------
//
// Function: TBInsertNoProps()
//
//   As TBInsert, but will set all properties of the new term to 0
//   first. 
//
// Global Variables: TBSupportReplace
//
// Side Effects    : Changes term bank
//
/----------------------------------------------------------------------*/

Term_p TBInsertNoProps(TB_p bank, Term_p term, DerefType deref)
{
   int    i;
   Term_p t;

   assert(term);

   term = TermDeref(term, &deref);

   t = TermEquivCellAlloc(term, bank->vars); /* This is an unshared
						term cell at the
						moment */
   if(!TermIsVar(t))
   {
      t->properties    = TPIgnoreProps;
      assert(SysDateIsCreationDate(t->rw_data.nf_date[0]));
      assert(SysDateIsCreationDate(t->rw_data.nf_date[1]));
      
      for(i=0; i<t->arity; i++)
      {
	 t->args[i] = TBInsertNoProps(bank, t->args[i], deref);
      }
      t = tb_termtop_insert(bank, t);
   }
   return t;
}


/*-----------------------------------------------------------------------
//
// Function: TBInsertInstantiated()
//
//   Insert a term into the termbank under the assumption that it is a
//   right side of a rule (or equation) instantiated with terms from
//   the bank - i.e. don't insert terms that are bound to variables,
//   but assume that they are in the term bank. Properties are deleted.
//
// Global Variables: TBSupportReplace
//
// Side Effects    : Changes term bank
//
/----------------------------------------------------------------------*/

Term_p TBInsertInstantiated(TB_p bank, Term_p term)
{
   int    i;
   Term_p t;

   assert(term);

   if(term->binding)
   {
      assert(TBFind(bank, term->binding));
      return term->binding;
   }
   
   t = TermEquivCellAlloc(term, bank->vars); /* This is an unshared
						term cell at the
						moment */
   if(!TermIsVar(t))
   {
      t->properties    = TPIgnoreProps;
      assert(SysDateIsCreationDate(t->rw_data.nf_date[0]));
      assert(SysDateIsCreationDate(t->rw_data.nf_date[1]));
      
      for(i=0; i<t->arity; i++)
      {
	 t->args[i] = TBInsertInstantiated(bank, t->args[i]);
      }
      t = tb_termtop_insert(bank, t);
   }
   return t;
}


/*-----------------------------------------------------------------------
//
// Function: TBTermtopInsert()
//
//   See tb_termtop_insert, for export without hurting inlining
//   capabilities. 
//
// Global Variables: -
//
// Side Effects    : Changes bank
//
/----------------------------------------------------------------------*/

Term_p TBTermtopInsert(TB_p bank, Term_p t)
{
   return tb_termtop_insert(bank,t);
}


/*-----------------------------------------------------------------------
//
// Function: TBFind()
//
//   Find a term in the term cell bank and return it.
//
// Global Variables: -
//
// Side Effects    : -
//
/----------------------------------------------------------------------*/

Term_p TBFind(TB_p bank, Term_p term)
{
   if(TermIsVar(term))
   {
      return VarBankFCodeFind(bank->vars, term->f_code);
   }
   return TermCellStoreFind(&(bank->term_store), term, bank->prop_mask);
}


#ifdef NEVER_DEFINED
/*-----------------------------------------------------------------------
//
// Function: TBDelete()
//
//   Delete a term and it's subterms from the term bank. This function
//   does _not_ follow bindings (it would make little sense...). In
//   fact, with the new rewriting, it makes little sense at all, and
//   should probably be delete right away. I'll put in an
//   assert(false) to catch all problems -- in fact, I'm commenting it
//   out so the compilter tells me where to remove calls! Duh!
//
// Global Variables: -
//
// Side Effects    : Changes term bank
//
/----------------------------------------------------------------------*/

bool TBDelete(TB_p bank, Term_p term)
{
   int i;
   Term_p old;

   assert(false); /* Should never be called with the new rewriting
		     anymore. */
   assert(term);

   if(TermIsVar(term)||TermIsTrueTerm(term))
   {
      return false;
   }   
   
   if(term->arity)
   {
      assert(term->args);
      for(i=0; i<term->arity; i++)
      {
	 TBDelete(bank, term->args[i]);
      }
      old = TermCellStoreExtract(&(bank->term_store), term,
				 bank->prop_mask);
      assert(!TermIsVar(old));
      TermTopFree(old);	 
      return true;
   }
   return false;
}
#endif

/*-----------------------------------------------------------------------
//
// Function: TBPrintBankInOrder()
//
//   Print the DAG in the order of ascending entry_no. 
//
// Global Variables: TBPrintTermsFlat
//
// Side Effects    : Output
//
/----------------------------------------------------------------------*/

void TBPrintBankInOrder(FILE* out, TB_p bank)
{
   NumTree_p tree = NULL;
   long i;
   PStack_p stack;
   Term_p   cell;
   IntOrP   dummy;

   for(i=0; i<TERM_STORE_HASH_SIZE; i++)
   {
      stack = TermTreeTraverseInit(bank->term_store.store[i]);
      while((cell = TermTreeTraverseNext(stack)))
      {
	 dummy.p_val = cell;
	 NumTreeStore(&tree, cell->entry_no,dummy, dummy);
      }
      TermTreeTraverseExit(stack);
   }   
   tb_print_dag(out, tree, bank->sig);
   NumTreeFree(tree);
}

/*-----------------------------------------------------------------------
//
// Function: TBPrintTermCompact()
//
//   Print a term bank term. Introduce abbreviations for all subterms
//   encountered. Subterms with TPOutputFlag are not 
//   printed, but are assumed to be known. Does _not_ follow bindings
//   (they are temporary and as such make little sense in the term
//   bank context) 
//
// Global Variables: -
//
// Side Effects    : Output, set TPOutputFlag in subterms printed with
//                   abbreviation.
//
/----------------------------------------------------------------------*/

void TBPrintTermCompact(FILE* out, TB_p bank, Term_p term)
{
   int i;
   
   if(TermCellQueryProp(term, TPOutputFlag))
   {	 
      fprintf(out, "*%ld", term->entry_no);
   }
   else
   {
      if(TermIsVar(term))
      {
	 fprintf(out, "X%ld", -term->f_code);
      }
      else
      {
	 if(TermCellIsAnyPropSet(term, bank->prop_mask))
	 {
	    fprintf(out, "*%ld|%d:",
		    term->entry_no,term->properties&bank->prop_mask);
	 }
	 else
	 {
	    fprintf(out, "*%ld:", term->entry_no);
	 }
	 TermCellSetProp(term, TPOutputFlag);
	 fprintf(out, SigFindName(bank->sig, term->f_code));
	 if(!TermIsConst(term))
	 {
	    fputc('(',out);
	    assert(term->args && (term->arity>0));
	    TBPrintTermCompact(out, bank, term->args[0]);
	    for(i=1;i<term->arity;i++)
	    {
	       fputc(',', out);
	       TBPrintTermCompact(out, bank, term->args[i]);
	    }
	    fputc(')',out);
	 }
      }
   }
}


/*-----------------------------------------------------------------------
//
// Function: TBPrintTerm()
//
//   Print a term from a term bank either in compact form (with
//   abbreviations) or as a conventional term.
//
// Global Variables: -
//
// Side Effects    : By the called functions
//
/----------------------------------------------------------------------*/

void TBPrintTerm(FILE* out, TB_p bank, Term_p term, bool fullterms)
{
   if(fullterms)
   {
      TBPrintTermFull(out, bank, term);
   }
   else
   {
      TBPrintTermCompact(out, bank, term);
   }
}



/*-----------------------------------------------------------------------
//
// Function:  TBPrintBankTerms()
//
//   Print the terms inserted into the term bank with abbreviations.
//
// Global Variables: -
//
// Side Effects    : Output, changes by TBPrintTermCompact()
//
/----------------------------------------------------------------------*/

void TBPrintBankTerms(FILE* out, TB_p bank)
{
   PStack_p stack = PStackAlloc();
   Term_p term;
   int i;

   for(i=0; i<TERM_STORE_HASH_SIZE; i++)
   {      
      PStackPushP(stack, bank->term_store.store[i]);
      
      while(!PStackEmpty(stack))
      {
	 term = PStackPopP(stack);
	 if(term)
	 {
	    PStackPushP(stack, term->lson);
	    PStackPushP(stack, term->rson);
	    if(TermCellQueryProp(term, TPTopPos))
	    {
	       TBPrintTermCompact(out, bank, term);
	       fprintf(out, "\n");
	    }
	 }
      }
   }
   PStackFree(stack);
}


/*-----------------------------------------------------------------------
//
// Function: TBTermParse()
//
//   Parse a term from the given scanner object directly into the
//   termbank. Supports abbreviations. This function will _not_ set
//   the TPTopPos property on top terms while parsing
//
// Global Variables: -
//
// Side Effects    : Input, memory operations, changes termbank.
//
/----------------------------------------------------------------------*/

Term_p TBTermParse(Scanner_p in, TB_p bank)
{
   Term_p     handle;
   DStr_p     id;
   DStr_p     source_name, errpos;
   long       line, column;
   StreamType type;

   source_name = DStrGetRef(AktToken(in)->source);
   type        = AktToken(in)->stream_type;
   line = AktToken(in)->line;
   column = AktToken(in)->column;

   /* Test for abbreviation */
   if(TestInpTok(in, Mult))
   {
      long           abbrev;
      TermProperties properties = TPIgnoreProps;
      
      NextToken(in);
      abbrev = ParseInt(in);
      
      if(TestInpTok(in, Colon|Pipe))
      { /* This _defines_ the abbrev! */
	 if(PDArrayElementP(bank->ext_index, abbrev))
	 {
	    /* Error: Abbreviation defined twice */
	    errpos = DStrAlloc();
	    DStrAppendStr(errpos, PosRep(type, source_name, line, column));
	    DStrAppendStr(errpos, "Abbreviation *");
	    DStrAppendInt(errpos, abbrev);
	    DStrAppendStr(errpos, " already defined");
	    Error(DStrView(errpos), SYNTAX_ERROR);
	    DStrFree(errpos);
	 }
	 if(TestInpTok(in, Pipe))
	 {
	    NextToken(in);
	    properties = ParseInt(in);
	 }
	 NextToken(in);
	 handle = TBTermParse(in, bank); /* Elegant, aint it? */
	 
	 if(properties)
	 { 
	    TermGetRef(&handle, handle);
	    TBRefSetProp(bank, &handle, properties);
	    TermReleaseRef(&handle);
	 }
	 /* printf("# Term %ld = %ld\n", abbrev, handle->entry_no); */
	 PDArrayAssignP(bank->ext_index, abbrev, handle);
      }
      else
      { /* This references the abbrev */
	 
	 handle = PDArrayElementP(bank->ext_index, abbrev);
	 if(!handle)
	 {
	    /* Error: Undefined abbrev */ 
	    errpos = DStrAlloc();
	    DStrAppendStr(errpos, PosRep(type, source_name, line, column));
	    DStrAppendStr(errpos, "Abbreviation *");
	    DStrAppendInt(errpos, abbrev);
	    DStrAppendStr(errpos, " undefined");
	    Error(DStrView(errpos), SYNTAX_ERROR);
	    DStrFree(errpos);  
	 }
      }
   }
   else
   {
      /* Normal term stuff, bloated because of the nonsensical SETHEO
	 syntax */
      
      if(SigSupportLists && TestInpTok(in, OpenSquare))
      {
	 handle =  tb_parse_cons_list(in, bank);
      }
      else
      {
	 id = DStrAlloc();
	 
#ifdef SAFELOGIC
	 if(SigInterpreteNumbers(bank->sig) && TestInpTok(in, PosInt))
	 {
	    Term_p tmp;
	    tmp = TermIntRepresentation(bank->sig, AktToken(in)->numval);
	    handle = TBInsert(bank, tmp, DEREF_NEVER);
	    TermFree(tmp);
	    AcceptInpTok(in, PosInt);
	 }
	 else
#endif	 
	 if(TermParseOperator(in, id))
	 {
	    handle = VarBankExtNameAssertAlloc(bank->vars, DStrView(id));
	 }
	 else
	 {
	    handle = DefaultSharedTermCellAlloc();
	 
	    if(TestInpTok(in, OpenBracket))
	    {
	       handle->arity = TBTermParseArgList(in, &(handle->args),
						  bank);
	    }
	    else
	    {
	       handle->arity = 0;
	    }
	    handle->f_code = SigInsertId(bank->sig, DStrView(id),
					 handle->arity, normal);
	    if(!handle->f_code)
	    {
	       errpos = DStrAlloc();
	       DStrAppendStr(errpos, PosRep(type, source_name, line, column));
	       DStrAppendStr(errpos, DStrView(id));
	       DStrAppendStr(errpos, " used with arity ");
	       DStrAppendInt(errpos, (long)handle->arity);
	       DStrAppendStr(errpos, ", but registered with arity ");
	       DStrAppendInt(errpos, 
			     (long)(bank->sig)->
			     f_info[SigFindFCode(bank->sig, DStrView(id))].arity);
	       Error(DStrView(errpos), SYNTAX_ERROR);
	       DStrFree(errpos);
	    }
	    handle = tb_termtop_insert(bank, handle);		 
	 }
	 DStrFree(id);
      }
   }
   DStrReleaseRef(source_name);

   return handle;
}



/*-----------------------------------------------------------------------
//
// Function: TBTermParseArgList()
//
//   Parse a list of terms (comma-separated and enclosed in brackets)
//   into an array of (shared) term pointers. See TermParseArgList()
//   in cte_terms.c for more.
//
// Global Variables: -
//
// Side Effects    : Input, memory operations, changes term bank
//
/----------------------------------------------------------------------*/

int TBTermParseArgList(Scanner_p in, Term_p** arg_anchor, TB_p bank) 
{
   Term_p *handle;
   int    arity;
   int    size;
   int    i;

   AcceptInpTok(in, OpenBracket);
   if(TestInpTok(in, CloseBracket))
   {
      NextToken(in);
      *arg_anchor = NULL;
      return 0;
   }
   size = TERMS_INITIAL_ARGS;
   handle = (Term_p*)SizeMalloc(size*sizeof(Term_p));
   arity = 0;
   handle[arity] = TBTermParse(in, bank);
   arity++;
   while(TestInpTok(in, Comma))
   {
      NextToken(in);
      if(arity==size)
      {
         size+=TERMS_INITIAL_ARGS;
         handle = (Term_p*)SecureRealloc(handle, size*sizeof(Term_p));
     }
      handle[arity] = TBTermParse(in, bank);
      arity++;
   }
   AcceptInpTok(in, CloseBracket);
   *arg_anchor = TermArgArrayAlloc(arity);
   for(i=0;i<arity;i++)
   {
      (*arg_anchor)[i] = handle[i];
   }
   SizeFree(handle, size*sizeof(Term_p));
   
   return arity;
}


/*-----------------------------------------------------------------------
//
// Function: TBRefSetProp()
//
//   Make ref point to a term of the same structure as *ref, but with
//   properties prop set. Properties do not work for variables!
//
// Global Variables: -
//
// Side Effects    : Changes bank, *ref
//
/----------------------------------------------------------------------*/

void TBRefSetProp(TB_p bank, TermRef ref, TermProperties prop)
{
   Term_p term, new;

   assert(!TermIsVar(*ref));
   
   term = *ref;
   if(TermCellQueryProp(term, prop)||TermIsVar(term))
   {
      return;
   }
   
   new = TermTopCopy(term);
   /* new->properties = new->properties&bank->prop_mask; Bad and wrong!*/
   TermReleaseRef(ref);
   TermCellSetProp(new, prop);
   new = tb_termtop_insert(bank, new);
   TermGetRef(ref, new);
   /* We cannot delete the old term anymore - will this be a problem?
      If yes, think (but I think no) */
   /* TBDelete(bank, term); */
}



/*-----------------------------------------------------------------------
//
// Function: TBRefDelProp()
//
//   Make ref point to a term of the same structure as *ref, but with
//   properties prop deleted. If the term is a variable, do nothing!
//
// Global Variables: -
//
// Side Effects    : Changes bank, *ref
//
/----------------------------------------------------------------------*/

void TBRefDelProp(TB_p bank, TermRef ref, TermProperties prop)
{
   Term_p term, new;
      
   term = *ref;
   if(!TermCellIsAnyPropSet(term, prop)||TermIsVar(term))
   {
      return;
   }
   new = TermTopCopy(term);
   TermReleaseRef(ref);
   TermCellDelProp(new, prop);
   new = tb_termtop_insert(bank, new);
   TermGetRef(ref, new);
   /* TBDelete(bank, term); See above */
}


/*-----------------------------------------------------------------------
//
// Function: TBTermDelPropCount()
//
//   Delete properties prop in term, return number of term cells with
//   this property. Does assume that all subterms of a term without
//   this property also do not carry it!
//
// Global Variables: 
//
// Side Effects    : 
//
/----------------------------------------------------------------------*/

long TBTermDelPropCount(Term_p term, TermProperties prop)
{
   long count = 0;
   int i;
   PStack_p stack = PStackAlloc();

   PStackPushP(stack, term);
   while(!PStackEmpty(stack))
   {
      term = PStackPopP(stack);
      if(TermCellQueryProp(term, prop))
      {
	 TermCellDelProp(term, prop);
	 count++;
	 for(i=0; i<term->arity; i++)
	 {
	    PStackPushP(stack, term->args[i]);
	 }
      }
   }
   PStackFree(stack);
   return count;
}


/*-----------------------------------------------------------------------
//
// Function: TBGCMarkTerm()
//
//   Mark a term as used for the garbage collector.
//
// Global Variables: -
//
// Side Effects    : Marks the term, memory operations
//
/----------------------------------------------------------------------*/

void TBGCMarkTerm(TB_p bank, Term_p term)
{
   PStack_p stack = PStackAlloc();   
   int i;

   assert(bank);
   assert(term);
   
   PStackPushP(stack, term);
   while(!PStackEmpty(stack))
   {
      term = PStackPopP(stack);
      if(!TBTermCellIsMarked(bank,term))
      {
	 TermCellFlipProp(term, TPGarbageFlag);
	 for(i=0; i<term->arity; i++)
	 {
	    PStackPushP(stack, term->args[i]);
	 }
	 if(TermIsRewritten(term))
	 {
	    PStackPushP(stack, TermRWReplaceField(term));
	 }
      }
   }
   PStackFree(stack);
}


/*-----------------------------------------------------------------------
//
// Function: TBGCSweep()
//
//   Sweep the term bank and free all unmarked term
//   cells. bank->true_term will be marked automatically. Returns the
//   number of term cells recovered.
//
// Global Variables: -
//
// Side Effects    : Memory operations, flips bank->garbage_state
//
/----------------------------------------------------------------------*/

long TBGCSweep(TB_p bank)
{
   long recovered = 0;
   
   assert(bank);
   assert(!TermIsRewritten(bank->true_term));
   TBGCMarkTerm(bank, bank->true_term);
  
   VERBOUT("Garbage collection started.\n");
   recovered = TermCellStoreGCSweep(&(bank->term_store),
				    bank->garbage_state,
				    bank->prop_mask);
   VERBOSE(fprintf(stderr, "Garbage collection reclaimed %ld unused term cells.\n",recovered););
#ifdef PRINT_SOMEERRORS_STDOUT
   if(OutputLevel)
   {
      fprintf(GlobalOut, 
	      "# Garbage collection reclaimed %ld unused term cells.\n",
	      recovered);
   }
#endif	 
   bank->garbage_state =
      bank->garbage_state?TPIgnoreProps:TPGarbageFlag;

   return recovered;
}


/*---------------------------------------------------------------------*/
/*                        End of File                                  */
/*---------------------------------------------------------------------*/






