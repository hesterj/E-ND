#include "ndset.h"

TableauSet_p TableauSetAlloc(void)
{
   TableauSet_p set = TableauSetCellAlloc();

   set->members = 0;
   set->anchor  = TableauCellAlloc();
   set->anchor->succ = set->anchor;
   set->anchor->pred = set->anchor;
   set->identifier = DStrAlloc();

   return set;
}

void         TableauSetFree(TableauSet_p set)
{
   assert(set);

   TableauSetFreeTableaus(set);
   TableauCellFree(set->anchor);
   DStrFree(set->identifier);
   TableauSetCellFree(set);
}

void         TableauSetFreeTableaus(TableauSet_p set)
{
   assert(set);

   while(!TableauSetEmpty(set))
   {
      TableauSetDeleteEntry(set->anchor->succ);
   }
}

void		 TableauSetDeleteEntry(Tableau_p nd)
{
   assert(nd);

   TableauSetExtractEntry(nd);
   TableauFree(nd);
}

Tableau_p   TableauSetExtractEntry(Tableau_p nd)
{
   assert(nd);
   assert(nd->set);

   nd->pred->succ = nd->succ;
   nd->succ->pred = nd->pred;
   nd->set->members--;
   nd->set = NULL;
   nd->succ = NULL;
   nd->pred = NULL;

   return nd;
}

void         TableauSetInsert(TableauSet_p set, Tableau_p newnd)
{
   assert(set);
   assert(newnd);
   assert(!newnd->set);

   newnd->succ = set->anchor;
   newnd->pred = set->anchor->pred;
   set->anchor->pred->succ = newnd;
   set->anchor->pred = newnd;
   newnd->set = set;
   set->members++;
}
