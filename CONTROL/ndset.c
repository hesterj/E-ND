#include "ndset.h"

NDSet_p NDSetAlloc(void)
{
   NDSet_p set = NDSetCellAlloc();

   set->members = 0;
   set->anchor  = NDCellAlloc();
   set->anchor->succ = set->anchor;
   set->anchor->pred = set->anchor;
   set->identifier = DStrAlloc();

   return set;
}

void         NDSetFree(NDSet_p set)
{
   assert(set);

   NDSetFreeNDs(set);
   NDCellFree(set->anchor);
   DStrFree(set->identifier);
   NDSetCellFree(set);
}

void         NDSetFreeNDs(NDSet_p set)
{
   assert(set);

   while(!NDSetEmpty(set))
   {
      NDSetDeleteEntry(set->anchor->succ);
   }
}

void		 NDSetDeleteEntry(ND_p nd)
{
   assert(nd);

   NDSetExtractEntry(nd);
   NDFree(nd);
}

ND_p   NDSetExtractEntry(ND_p nd)
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

void         NDSetInsert(NDSet_p set, ND_p newnd)
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
