#ifndef TableauSET

#define TableauSET


#include <clb_plist.h>
#include <naturaldeduction.h>

typedef struct nd_set_cell
{
   Tableau_p anchor;
   long       members;
   DStr_p     identifier;
}TableauSetCell, *TableauSet_p;
/*
typedef struct nd_assumption_set_cell
{
   TableauAssumption_p anchor;
   long       members;
   DStr_p     identifier;
}TableauAssumptionSetCell, *TableauAssumptionSet_p;
*/
#define TableauSetCellAlloc()    (TableauSetCell*)SizeMalloc(sizeof(TableauSetCell))
#define TableauSetCellFree(junk) SizeFree(junk, sizeof(TableauSetCell))
#define      TableauSetEmpty(set)\
             ((set)->anchor->succ == (set)->anchor)

TableauSet_p TableauSetAlloc(void);
void         TableauSetFreeTableaus(TableauSet_p set);
void         TableauSetFree(TableauSet_p set);
void		 TableauSetDeleteEntry(Tableau_p nd);
Tableau_p   TableauSetExtractEntry(Tableau_p form);
void         TableauSetInsert(TableauSet_p set, Tableau_p newnd);

#endif
