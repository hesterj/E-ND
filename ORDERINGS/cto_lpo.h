/*-----------------------------------------------------------------------

File  : cto_lpo.h

Author: Stephan Schulz and Joachim Steinbach

Contents
 
  Definitions for implementing a lexicographic path ordering.

  Copyright 1998, 1999 by the author.
  This code is released under the GNU General Public Licence.
  See the file COPYING in the main CLIB directory for details.
  Run "eprover -h" for contact information.

Changes

<1> Thu May 28 12:14:31 MET DST 1998
    New
<2> Tue Sep 15 08:50:54 MET DST 1998
    Changed

-----------------------------------------------------------------------*/

#ifndef CTO_LPO

#define CTO_LPO

#include <cto_ocb.h>


/*---------------------------------------------------------------------*/
/*                    Data type declarations                           */
/*---------------------------------------------------------------------*/




/*---------------------------------------------------------------------*/
/*                Exported Functions and Variables                     */
/*---------------------------------------------------------------------*/

extern long   LPORecursionDepthLimit;

bool          LPOGreater(OCB_p ocb, Term_p s, Term_p t,
			 DerefType deref_s, DerefType deref_t);
CompareResult LPOCompare(OCB_p ocb, Term_p s, Term_p t,
			 DerefType deref_s, DerefType deref_t);

#endif

/*---------------------------------------------------------------------*/
/*                        End of File                                  */
/*---------------------------------------------------------------------*/
