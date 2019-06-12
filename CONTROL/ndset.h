#ifndef NDSET

#define NDSET


#include <clb_plist.h>
#include <naturaldeduction.h>

typedef struct nd_set_cell
{
   ND_p anchor;
   long       members;
   DStr_p     identifier;
}NDSetCell, *NDSet_p;

typedef struct nd_assumption_set_cell
{
   NDAssumption_p anchor;
   long       members;
   DStr_p     identifier;
}NDAssumptionSetCell, *NDAssumptionSet_p;

#define NDSetCellAlloc()    (NDSetCell*)SizeMalloc(sizeof(NDSetCell))
#define NDSetCellFree(junk) SizeFree(junk, sizeof(NDSetCell))
#define      NDSetEmpty(set)\
             ((set)->anchor->succ == (set)->anchor)

NDSet_p NDSetAlloc(void);
void         NDSetFreeNDs(NDSet_p set);
void         NDSetFree(NDSet_p set);
void		 NDSetDeleteEntry(ND_p nd);
ND_p   NDSetExtractEntry(ND_p form);
void         NDSetInsert(NDSet_p set, ND_p newnd);

#endif
