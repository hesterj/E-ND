/*-----------------------------------------------------------------------

File  : clb_stringtrees.c

Author: Stephan Schulz

Contents
 
  Functions for string-indexed SPLAY trees.

  Copyright 1998, 1999 by the author.
  This code is released under the GNU General Public Licence.
  See the file COPYING in the main CLIB directory for details.
  Run "eprover -h" for contact information.

Changes

<1> Thu Sep 25 02:36:58 MET DST 1997
    New
<2> Thu Apr  8 17:36:18 MET DST 1999
    Replaced AVL trees with splay trees (I didn't know AVL was still
    here ;-)

-----------------------------------------------------------------------*/

#include "clb_stringtrees.h"



/*---------------------------------------------------------------------*/
/*                        Global Variables                             */
/*---------------------------------------------------------------------*/


/*---------------------------------------------------------------------*/
/*                      Forward Declarations                           */
/*---------------------------------------------------------------------*/


/*---------------------------------------------------------------------*/
/*                         Internal Functions                          */
/*---------------------------------------------------------------------*/

/*-----------------------------------------------------------------------
//
// Function: splay_tree() 
//
//   Perform the splay operation on tree at node with key.
//
// Global Variables: -
//
// Side Effects    : Changes tree
//
/----------------------------------------------------------------------*/

static StrTree_p splay_tree(StrTree_p tree, char* key) 
{
   StrTree_p   left, right, tmp;
   StrTreeCell new;
   int         cmpres;

   if (!tree) 
   {
      return tree;
   }
   
   new.lson = NULL;
   new.rson = NULL;
   left = &new;
   right = &new;
   
   for (;;) 
   {
      cmpres = strcmp(key, tree->key);
      if (cmpres < 0) 
      {
         if(!tree->lson)
         {
            break;
         }
         if(strcmp(key, tree->lson->key) < 0)
         {
            tmp = tree->lson;
            tree->lson = tmp->rson;
            tmp->rson = tree;
            tree = tmp;
            if (!tree->lson)
            {
               break;
            }
         }
         right->lson = tree;
         right = tree;
         tree = tree->lson;
      } 
      else if(cmpres > 0)
      {
         if (!tree->rson)
         {
            break;
         }
         if(strcmp(key, tree->rson->key) > 0) 
         {
            tmp = tree->rson;
            tree->rson = tmp->lson;
            tmp->lson = tree;
            tree = tmp;
            if (!tree->rson) 
            {
               break;
            }
         }
         left->rson = tree;
         left = tree;
         tree = tree->rson;
      }
      else 
      {
         break;
      }
   }
   left->rson = tree->lson;
   right->lson = tree->rson;
   tree->lson = new.rson;
   tree->rson = new.lson;
   
   return tree;
}




/*---------------------------------------------------------------------*/
/*                         Exported Functions                          */
/*---------------------------------------------------------------------*/

/*-----------------------------------------------------------------------
//
// Function: StrTreeCellAllocEmpty()
//
//   Allocate a empty, initialized StrTreeCell. Pointers to children
//   are NULL, int values are 0 (and pointer values in ANSI-World
//   undefined, in practice NULL on 32 bit machines)(This comment is
//   superfluous!). 
//
// Global Variables: -
//
// Side Effects    : Memory operations
//
/----------------------------------------------------------------------*/

StrTree_p StrTreeCellAllocEmpty(void)
{
   StrTree_p handle = StrTreeCellAlloc();
   
   handle->val1.i_val = handle->val2.i_val = 0;
   handle->lson       = handle->rson       = NULL;

   return handle;
}

/*-----------------------------------------------------------------------
//
// Function: StrTreeFree()
//
//   Free a stringtree (including the keys, but not potential objects
//   pointed to in the val fields
//
// Global Variables: -
//
// Side Effects    : Memory operations
//
/----------------------------------------------------------------------*/

void StrTreeFree(StrTree_p junk)
{
   if(!junk)
   {
      return;
   }
   StrTreeFree(junk->lson);
   StrTreeFree(junk->rson);
   FREE(junk->key);
   StrTreeCellFree(junk);
}


/*-----------------------------------------------------------------------
//
// Function: StrTreeInsert()
//
//   If an entry with key *new->key exists in the tree return a
//   pointer to it. Otherwise insert *new in the tree and return
//   NULL. 
//
// Global Variables: -
//
// Side Effects    : Changes the tree
//
/----------------------------------------------------------------------*/

StrTree_p StrTreeInsert(StrTree_p *root, StrTree_p new)
{
   int cmpres;
   if (!*root) 
   {
      new->lson = new->rson = NULL;
      *root = new;
      return NULL;
   }
   *root = splay_tree(*root, new->key);

   cmpres = strcmp(new->key, (*root)->key);
   
   if (cmpres < 0) 
   {
      new->lson = (*root)->lson;
      new->rson = *root;
      (*root)->lson = NULL;
      *root = new;
      return NULL;
   } 
   else if(cmpres > 0) 
   {
      new->rson = (*root)->rson;
      new->lson = *root;
      (*root)->rson = NULL;
      *root = new;
      return NULL;
   }
   return *root;
}


/*-----------------------------------------------------------------------
//
// Function: StrTreeStore()
//
//   Insert a cell associating key with val1 and val2 into the
//   tree. Return false if an entry for this key exists, true
//   otherwise. 
//
// Global Variables: -
//
// Side Effects    : Changes tree
//
/----------------------------------------------------------------------*/

bool StrTreeStore(StrTree_p *root, char* key, IntOrP val1, IntOrP val2)
{
   StrTree_p handle, new;

   handle = StrTreeCellAlloc();
   handle->key = SecureStrdup(key);
   handle->val1 = val1;
   handle->val2 = val2;
   
   new = StrTreeInsert(root, handle);

   if(new)
   {
      FREE(handle->key);
      StrTreeCellFree(handle);
      return false;
   }
   return true;
}


/*-----------------------------------------------------------------------
//
// Function: StrTreeFind()
//
//   Find the entry with key key in the tree and return it. Return
//   NULL if no such key exists.
//
// Global Variables: -
//
// Side Effects    : -
//
/----------------------------------------------------------------------*/

StrTree_p StrTreeFind(StrTree_p *root, char* key)
{
   if(*root)
   {
      *root = splay_tree(*root, key);  
      if(strcmp((*root)->key,key)==0)
      {
         return *root;
      }
   }
   return NULL;
}


/*-----------------------------------------------------------------------
//
// Function: StrTreeExtractEntry()
//
//   Find the entry with key key, remove it from the tree, rebalance
//   the tree, and return the pointer to the removed element. Return
//   NULL if no matching element exists.
//
// Global Variables: -
//
// Side Effects    : Changes the tree
//
/----------------------------------------------------------------------*/


StrTree_p StrTreeExtractEntry(StrTree_p *root, char* key)
{
   StrTree_p x, cell;

   if (!(*root))
   {
      return NULL;
   }
   *root = splay_tree(*root, key);
   if(strcmp(key, (*root)->key)==0)
   {
      if (!(*root)->lson)
      {
         x = (*root)->rson;
      } 
      else
      {
         x = splay_tree((*root)->lson, key);
         x->rson = (*root)->rson;
      }
      cell = *root;
      cell->lson = cell->rson = NULL;
      *root = x;
      return cell;
   }
   return NULL;
}


/*-----------------------------------------------------------------------
//
// Function: StrTreeDeleteEntry()
//
//   Delete the entry with key key from the tree. 
//
// Global Variables: -
//
// Side Effects    : By StrTreeExtract(), memory operations
//
/----------------------------------------------------------------------*/

bool StrTreeDeleteEntry(StrTree_p *root, char* key)
{
   StrTree_p cell;
   
   cell = StrTreeExtractEntry(root, key);
   if(cell)
   {
      StrTreeFree(cell);
      return true;
   }
   return false;
}

AVL_TRAVERSE_DEFINITION(StrTree, StrTree_p)

/*---------------------------------------------------------------------*/
/*                        End of File                                  */
/*---------------------------------------------------------------------*/


