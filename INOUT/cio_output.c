/*-----------------------------------------------------------------------

File  : cio_output.c

Author: Stephan Schulz

Contents
 
  Simple functions for secure opening of output files with -
  convention and error checking. Much simpler than the input, because
  much less can go wrong with output...

  Copyright 1998, 1999 by the author.
  This code is released under the GNU General Public Licence.
  See the file COPYING in the main CLIB directory for details.
  Run "eprover -h" for contact information.

Changes

<1> Fri Nov 28 11:55:59 MET 1997
    New

-----------------------------------------------------------------------*/


#include <cio_output.h>



/*---------------------------------------------------------------------*/
/*                        Global Variables                             */
/*---------------------------------------------------------------------*/


long  OutputLevel = 1;
FILE* GlobalOut;

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
// Function: OutOpen()
//
//   Open a file for writing and return it, with error checking. "-"
//   and NULL are both taken to mean stdout.
//
// Global Variables: -
//
// Side Effects    : Opens file
//
/----------------------------------------------------------------------*/

FILE* OutOpen(char* name)
{
   FILE* out;

   if(name && strcmp(name,"-")!= 0)
   {
      VERBOUTARG("Output file is ", name);
      
      if(! (out = fopen(name,"w")))
      {
	 TmpErrno = errno; /* Save error number, the following call to
			    sprintf() can theoretically alter  the
			    value !*/
	 sprintf(ErrStr, "Cannot open file %s", name);
         SysError(ErrStr, FILE_ERROR);
      }
   }
   else
   {
      VERBOUT("Output is going to <stdout>\n");
      out = stdout;
   }
   clearerr(out); 
   return out;
}


/*-----------------------------------------------------------------------
//
// Function: OutClose()
//
//   Close the file, checking for errors. If stdout, just flush
//   it. Error messages are bound to be short, but errors should only
//   result from program errors or extremely obscure circumstances.
//
// Global Variables: -
//
// Side Effects    : Closes file
//
/----------------------------------------------------------------------*/

void OutClose(FILE* file)
{
   fflush(file);
   if(ferror(file))
   {
      Error("Output stream to be closed reports error (probably file"
	    " system full or quota exceeded)",FILE_ERROR);
   }
   
   VERBOUT("Closing output\n");
   if(file != stdout)
   {
      if(fclose(file) != 0)
      {
         TmpErrno = errno;
         SysError("Error while closing file", FILE_ERROR);
      }
   }
}


/*---------------------------------------------------------------------*/
/*                        End of File                                  */
/*---------------------------------------------------------------------*/


