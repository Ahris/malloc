/**mm.c - Malloc implementation written by Alice Wang and Shyamolee
 *
 * This implementation uses explicit seglists. The seglists are sorted
 * by last use and find fit uses first fit to find an appropriate block
 * to allocate. An allocated block has a word sized header and footer
 * to hold their size and allocated bit. A free block has a 3 word header
 * and a single word footer to hold the size. Pointers are passed around
 * and are assumed to be referencing to the block's payload in most cases.
 * Coalesce is called every time we want to insert a block. Realloc is
 * implemented using mm_malloc and mm_free and checks for simple edge
 * cases.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include <limits.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
        /* Team name */
        "costumes",
        /* First member's full name */
        "Alice Wang",
        /* First member's email address */
        "",
        /* Second member's full name (leave blank if none) */
        "Shyamolee",
        /* Second member's email address (leave blank if none) */
        ""
};

/* Double word (8) alignment */
#define ALIGNMENT 8

/* Rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define MAX_HEAP (20*(1<<20))  /* 20 MB */

/* Basic constants and macros */
#define WSIZE 4                     /* word size (bytes) */
#define DSIZE 8                     /* doubleword size (bytes) */
#define CHUNKSIZE (1<<12)           /* initial heap size (bytes) */
#define OVERHEAD 8                  /* overhead of header and footer (bytes) */
#define NUM_SEG_LISTS 21
#define OVERHEAD_HDR (3*WSIZE)      /* free block's header size */
#define OVERHEAD_FTR (1*WSIZE)      /* free block's footer size */
#define MIN_BLOCK_SIZE 16

#define MAX(x, y) ((x) > (y)? (x) : (y))
#define MIN(x, y) ((x) < (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))  

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* 
 * Locates seglist n, for n between (0, 21]. 
 * Each seglist pointer takes up 1 WSIZE
 * Uses the base address of our heap, 
 * compensates for heap buffer, and adds the approprite
 * seglist offset.
 */
#define GET_LIST(n) (char *)GET((((char*)mem_heap_lo() + 2*WSIZE) + n*WSIZE))
#define GET_LIST_ADDR(n) (((char*)mem_heap_lo() + 2*WSIZE) + n*WSIZE)

/* 
 * Given the block ptr bp of an allocated block, 
 * computes address of the block's header and footer. 
 * Note- Both the allocated header and allocated footer are sized WSIZE 
 */
#define HDRP(bp)       ((char *)(bp) - WSIZE)  
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 
 * Given the block ptr bp of a free block, 
 * computes address of the block's header and footer 
 * Note- Both the free header is sized 3*WSIZE and the free footer is 1*WSIZE
 */
#define HDRP_FREE(bp)       ((char *)(bp) - 3*WSIZE)  
#define FTRP_FREE(bp)       ((char *)(bp) + GET_SIZE(HDRP_FREE(bp)) - OVERHEAD_HDR - OVERHEAD_FTR)

/* Getting the next block of a free block. Uses explicit lists
 * bp should be the payload of the free block
 */
#define NEXT_BLKP(bp) (char*)((char *)(bp) - 1*WSIZE)
#define PREV_BLKP(bp) (char*)((char *)(bp) - 2*WSIZE)

/* Set the prev and next in a free block. bp is the free block's payload */
#define SET_PREV_IN_FREE_BLOCK(bp, value) PUT(PREV_BLKP(bp), value)
#define SET_NEXT_IN_FREE_BLOCK(bp, value) PUT(NEXT_BLKP(bp), value)

/* 
 * Seg list ranges are defined as follows: For x ranging from 4 to 25
 * The Upper range is (2^(x+1)) exclusive
 * The lower range is 2^(x) inclusive
 * X begins at 3, so that the smallest block size accomodates 
 * free blocks with the minimum size of 16
 */
#define FIND_UPPER_RANGE(n) (2<<(n+4))
#define FIND_LOWER_RANGE(n) (2<<(n+3))

/* Returns the pointer to the head of blocks prev and next in heap, 
 * given the bp of a free block.
 * It is used in conjunction with GET_ALLOC */
#define GET_PREV_ADDR_IN_HEAP_FREE(bp)          (char *)((char*)bp - 3*WSIZE - GET_SIZE((char *)(bp) - 4 * WSIZE))
#define GET_NEXT_ADDR_IN_HEAP_FREE(bp)          (char *)((char*)bp - 3*WSIZE + GET_SIZE(HDRP_FREE(bp)))

/* Takes in the bp pointer to a free payload.  
 * return the address in the heap of the previous footer used in coalesce.  */
#define GET_PREV_FOOTER_IN_HEAP_FREE(bp) (char*) ((char*)bp - 4*WSIZE)

 /* Converts the allocated base pointer to the 
 * free base pointer by offsetting by 2 WSIZES */
#define ALLOC_TO_FREE(bp) ((char *) (bp) + 2*WSIZE)
#define FREE_TO_ALLOC(bp) ((char * )(bp) - 2*WSIZE)  


static char *heap_listp;
static char *heap_list_head;
static char *mem_brk;

static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void deleteFromSegList(void *bp);
static void insertIntoSegList(void *bp);
static void *getPrevBlockInHeapFree(void * bp);
static void *getNextBlockInHeapFree(void * bp);
static void *get_list_addr(int n);
static void *get_list(int n);
static void mm_check();



/*
 * extend_heap - Takes in words, which is the size to increase the heap by
 *               Note that void* bp points to the start of the new space
 *               Returns the payload of the newly assigned free block, after
 *               coallesced with its neighbors
 */
static void *extend_heap(size_t words) {
    char *bp; 
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;

    if ((int)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0)); 
    PUT(FTRP(bp), PACK(size, 0));    
    PUT(HDRP(bp)+size, PACK(0,1));

    return coalesce(ALLOC_TO_FREE(bp));
} 



/*
 * mm_init - initialize the malloc package.
 *           First allocated enough space for the prologue, epilogue and
 *           NUM_SEG_LISTS. After correcntly intersting the set up info,
 *           the heap is extended by the default CHUNKSIZE.
 */
int mm_init(void)
{
    int i;

    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(NUM_SEG_LISTS*WSIZE + 5*WSIZE)) == (void *)-1) {
        return -1;
    }
    
    // Setting the heap header to be used in pointer methods
    heap_list_head = (char*)heap_listp + 2*WSIZE;

    // 2 word sized buffer 
    PUT(heap_listp + (0*WSIZE), 0);
    PUT(heap_listp + (1*WSIZE), 0);   
    heap_listp += 2*WSIZE;

    /* Initializes the seglist pointers to null */
    for (i = 0; i < NUM_SEG_LISTS; ++i) {
        PUT(get_list_addr(i), (int) NULL);
    }

    heap_listp += NUM_SEG_LISTS*WSIZE;

    PUT(heap_listp + (0*WSIZE), PACK(DSIZE, 1));  /* prologue header */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));  /* prologue footer */
    PUT(heap_listp + (2*WSIZE), PACK(0, 1));      /* epilogue header */

    if(extend_heap(CHUNKSIZE/WSIZE) == NULL) { 
        return -1;
    }

    return 0;
}



/*
 * mm_malloc - Allocate a block by searching through the seglists to find a fit.
 *             Always allocate a block whose size is a multiple of the alignment.
 *             Return the payload pointer to an allocated block
 */
void *mm_malloc(size_t size) {
    size_t asize;             /* adjusted block size */
    size_t extendsize;        /* amount to extend heap if no fit */
    char *bp;                 /* pointer to the newly allocated space*/ 
    char * foundBlock = NULL; /* pointer to the block to allocate */

    /* Can't malloc for 0 bytes  */
    if (size <= 0) {
        return NULL;
    }

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = DSIZE + OVERHEAD;
    else
        asize = DSIZE * ((size + (OVERHEAD) + (DSIZE-1)) / DSIZE);

    foundBlock = find_fit(asize);

    if (foundBlock != NULL) {
        place(foundBlock, asize);
        return FREE_TO_ALLOC(foundBlock); 
    }

    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);

    //mm_check();
 
    return FREE_TO_ALLOC(bp);
}




/* find_fit - Takes in the aligned size of the free block to find in the seglists.
 *            Returns the pointer to the payload of the free block that can fit 
 *            the requested size. 
 */
void *find_fit(size_t asize) {
    int n;
    char *bp;  

    // Go through all of the seglists
    for(n = 0; n < NUM_SEG_LISTS; ++n) {
        // if the requested size belongs in the range of this seglist
        if(asize < FIND_UPPER_RANGE(n) && get_list(n) != NULL) {
            // Go through all of the blocks in the seg list to find one that fits
            for(bp = get_list(n); bp != NULL; bp = ((char *)GET(NEXT_BLKP(bp)))) {
                if(!GET_ALLOC(HDRP_FREE(bp)) && (asize <= GET_SIZE(HDRP_FREE(bp)))) {
                    return bp;
                }
            }
        }
    }

    return NULL;
}




/*
 * mm_free - bp is an allocated block. Will now free it by removing from
 *           the seglist by changing its allocated bits. And then add it 
 *           to the seglists using the call to coalesce.
 *           void* bp points to the allocated payload.
 */
void mm_free(void* bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    bp = ALLOC_TO_FREE(bp); 
    coalesce(bp);
    //mm_check();
}




/*
 * place - Pass in the pointer to the payload of the free block that fits
 *         and pass in the size. Place allocates the free block. Splice
 *         the block passed in if it's too big, otherwise just allocate it
 *         by changing its tags.
 */
void place(void *bp, size_t asize) {
    size_t freeBlockSize = GET_SIZE(HDRP_FREE(bp));
    char* otherPointer;    

    deleteFromSegList(bp);

    // The size request by the user fits snugly into the found free block
    if (freeBlockSize == asize || freeBlockSize-asize <= MIN_BLOCK_SIZE ) {
        PUT(HDRP_FREE(bp), PACK(freeBlockSize, 1));
        PUT(FTRP_FREE(bp), PACK(freeBlockSize, 1));
    } else {
        /* The block is too big - break it up into 2 smaller blocks */
        // Allocated the first part
        PUT(HDRP_FREE(bp), PACK(asize, 1));
        PUT(FTRP_FREE(bp), PACK(asize, 1));

        // Free the extra space
        otherPointer = (char*) bp + asize;
        PUT(HDRP_FREE(otherPointer), PACK(freeBlockSize-asize, 0));
        PUT(FTRP_FREE(otherPointer), PACK(freeBlockSize-asize, 0));
        insertIntoSegList((char*)(otherPointer));
    }

    //mm_check();
}




/* deleteFromSegList - Takes in a free block and removes it from the seglist
 *                     void* bp should point to the payload of the free block
 *                     Find the seglist the free block belongs to by size and 
 *                     then remove it with a call to deleteFromSegList.
 *                     Change the prev and next pointers of its prev, next 
 *                     and list head as necessary.
 */
void deleteFromSegList(void *bp) {
    int size = GET_SIZE(HDRP_FREE(bp));
    int n;
    int foundList = 0;
    int prevExists = ((char *)GET(PREV_BLKP(bp))) != NULL;
    int nextExists = ((char *)GET(NEXT_BLKP(bp))) != NULL;
    char* holder;
    char* holder2;

    // Loop through all of the seg lists to find the list bp is from
    for (n=0; n < NUM_SEG_LISTS ; n++) {
        if (size >= (FIND_LOWER_RANGE(n)) && size < (FIND_UPPER_RANGE(n))) {
            foundList = n;
            break;
        }
    }

    if (!prevExists && !nextExists) {
        // Case 1: item to be deleted is the only one in the list

        PUT(get_list_addr(foundList), (int) NULL);
        PUT(NEXT_BLKP(bp), (int) NULL);
        PUT(PREV_BLKP(bp), (int) NULL);
    } else if (!prevExists && nextExists) {
        // Case 2: item to be deleted is the first element in the list

        PUT((char *)get_list_addr(foundList), (int)GET(NEXT_BLKP(bp)));
        holder = (char *)GET(NEXT_BLKP(bp));
        PUT(PREV_BLKP(holder), (int) NULL);
        PUT(PREV_BLKP(bp), (int) NULL);
        PUT(NEXT_BLKP(bp), (int) NULL);
    } else if (prevExists && !nextExists) {
        // Case 3: item to be deleted is the last element to be deleted

        holder = (char *)(char *)GET(PREV_BLKP(bp));
        PUT(PREV_BLKP(bp), (int) NULL);
        PUT(NEXT_BLKP(bp), (int) NULL);
        PUT(NEXT_BLKP(holder), (int) NULL);
    } else {
        //Case 4: item to be deleted is in the middle of a list
        holder = (char *)GET(PREV_BLKP(bp));
        holder2 = (char *)GET(NEXT_BLKP(bp));

        PUT(NEXT_BLKP(holder), (int)holder2);
        PUT(PREV_BLKP(holder2), (int)holder);
        PUT(PREV_BLKP(bp), (int) NULL);
        PUT(NEXT_BLKP(bp), (int) NULL);
    }

}



/**
 * insertIntoSeglist - void* bp is the free block we want to insert into the 
 *                     seg lists. Find the seglist it belongs to and insert in
 *                     according to last use. Change the prev and next pointers 
 *                     of its prev, next and list head as necessary.
 *                     void* bp should point to the payload of the free block
 **/
void insertIntoSegList(void *bp) {
    int size = GET_SIZE(HDRP_FREE(bp));
    char* currentBlock;
    int n;
    int foundList = -1;

    // Loop through all of the seglists to find the list bp belongs to
    for (n = 0; n < NUM_SEG_LISTS; ++n) {
        if(size < FIND_UPPER_RANGE(n)) {
            foundList = n;
            break;
        }
    }

    /* The free block we're looking at in the seglist */
    currentBlock = get_list(foundList);

    if(currentBlock == NULL) {
        // Insert as the first and only  block in the list
        PUT(PREV_BLKP(bp), (int) NULL);
        PUT(NEXT_BLKP(bp), (int) NULL);
        PUT(get_list_addr(foundList), (int)bp);

    } else {
        // Insert bp as the first element in the seglist 
        // Blocks are sorted by last use

        PUT(PREV_BLKP(bp), (int) NULL);
        PUT(NEXT_BLKP(bp), (int)currentBlock);
        PUT(PREV_BLKP(currentBlock), (int)bp);
        PUT(get_list_addr(foundList), (int)bp);
    }
}



/*
 * mm_realloc - Realloc handles the resizing of an allocated block, 
 *              as requested by a user.
 *              Inputs: void* ptr a the pointer to the payload of 
 *              an allocated block size_t size is the user requested 
 *              size for a new version of the block at ptr.
 *              Returns: the pointer to the block at ptr.
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *otherPtr;
    size_t asize;
    int oldPayload;
    int payload;
    int newPayloadSize;
    char* freePtr;
    char* nextBlockPHead;
    char* nextBlockPPayload;
    int bigSize;

    /* Calculate adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = DSIZE + OVERHEAD;
    else
        asize = DSIZE * ((size + (OVERHEAD) + (DSIZE-1)) / DSIZE); 

    if (ptr == NULL) {
        // Case 1: Reallocing a null blocks just calls malloc
        return mm_malloc(size);
    } else if (size <= 0) {

        // Case 2: Reallocing a size of 0 frees the block
        mm_free(ptr);
        return NULL;
    } else {

        freePtr = ALLOC_TO_FREE(ptr);
        int mySize = GET_SIZE(HDRP_FREE(freePtr));
        nextBlockPHead = (char *)FTRP(ptr)+WSIZE;
        nextBlockPPayload = (char*)nextBlockPHead + 3*WSIZE;
        int next_alloc = GET_ALLOC(nextBlockPHead);
        bigSize = mySize + GET_SIZE(nextBlockPHead);

        // Case 3: reallocing to a smaller size returns original block
        if(mySize > asize) {
            return ptr;
        }
 
        // Case 4: Try to expand your block to ptr's physical next block
        //         in memory of the combined size is big enough to hold
        //         the requested size
        if(!next_alloc && (bigSize) >= asize) {
            // Join with next block

            deleteFromSegList(nextBlockPPayload);
            PUT(HDRP_FREE(freePtr), PACK(bigSize, 1));
            PUT(FTRP_FREE(freePtr), PACK(bigSize, 1));

            //mm_check();

            return ptr;

        } else {

            oldPayload = GET_SIZE(HDRP(ptr)) - 2*WSIZE;
            otherPtr = mm_malloc(size);
            
            // Safetly check to see if malloc ran out of space
            if(otherPtr == NULL) {
                return NULL;
            }

            // Move the memory over to the newly malloc'ed block
            newPayloadSize = GET_SIZE(HDRP(otherPtr)) - 2*WSIZE;
            payload = MIN(oldPayload, newPayloadSize);
            memmove(otherPtr, ptr, payload);

            mm_free(ptr);

            //mm_check();

            return otherPtr;
        }
    }
}



/*
 * coalesce - Input: Pointer to the payload of a newly freed block. 
 *            Checks the newly freed block's neighbors in memory. 
 *            If there are any unallocated neighbors, the newly freed 
 *            block and the unallocated neighbor(s) are coallesced.
 *            Side effects: Changes boundary allocation tags of bp and 
 *            size blocks of bp and its neighbors
 *            Returns: the base pointer of the free block.
 */
static void *coalesce(void *bp)
{
    size_t size = GET_SIZE(HDRP_FREE(bp));

    // Checks to see if bp's predecessor and successor is allocated.
    // 1 if allocated; 0 if free. 
    size_t prev_alloc = GET_ALLOC((char*)(bp) - 4*WSIZE);
    size_t next_alloc = GET_ALLOC((char*)(bp) - 3*WSIZE + size);

    // Temporary storage variables for next and prev pointers
    char* holderNextBlock;
    char* holderPrevBlock;

    if(GET_ALLOC(HDRP_FREE(bp)) == 1) {
        return bp;
    }

    if (prev_alloc && next_alloc) {                         /* Case 1 */
        // If both of bp's neighbors are allocated, bp 
        // cannot be coalesced and is simply inserted into a seg list.    

        insertIntoSegList(bp); 
        return bp;
    }

    /* In the following three cases, 
       we want to merge any adjacent freed blocks 
       with the bp block we just freed */

    if (prev_alloc && !next_alloc) {                        /* Case 2 */
        /* BP's predecessor is allocated, but its successor is not--
         * Merge BP with its successor */
        holderNextBlock = (char*)(bp) + size;  
        size += GET_SIZE(HDRP_FREE(holderNextBlock));
        deleteFromSegList(holderNextBlock);
        PUT(HDRP_FREE(bp), PACK(size, 0));
        PUT(FTRP_FREE(bp), PACK(size, 0));
        insertIntoSegList(bp);
        return(bp);


    } else
        if (!prev_alloc && next_alloc) {                    /* Case 3 */
            /* BP's predecessor is not allocated, but its successor--
             * Merge BP with its predecessor */
            holderPrevBlock = getPrevBlockInHeapFree(bp);
            size += GET_SIZE(HDRP_FREE(holderPrevBlock));
            deleteFromSegList(holderPrevBlock);
            PUT(HDRP_FREE(holderPrevBlock), PACK(size, 0));
            PUT(FTRP_FREE(holderPrevBlock), PACK(size, 0));
            insertIntoSegList(holderPrevBlock);
            return(holderPrevBlock);

        } else {                                            /* Case 4 */
            /* BP's predecessor and successor are free blocks--
             * Merge all bp with both of them */
            holderNextBlock = getNextBlockInHeapFree(bp);
            holderPrevBlock = getPrevBlockInHeapFree(bp);
            size += GET_SIZE(HDRP_FREE(holderPrevBlock)) +
                     GET_SIZE(HDRP_FREE(holderNextBlock));
            deleteFromSegList(holderPrevBlock);
            deleteFromSegList(holderNextBlock);
            PUT(HDRP_FREE(holderPrevBlock), PACK(size, 0));
            PUT(FTRP_FREE(holderPrevBlock), PACK(size, 0));
            insertIntoSegList(holderPrevBlock);
            return(holderPrevBlock);
        }
}




/* 
 * Locates seglist n, for n between (0, 21]. 
 * Each seglist pointer takes up 1 WSIZE
 * Uses the base address of our heap, 
 * compensates for heap buffer, and adds the approprite
 * seglist offset.
 */
static void* get_list_addr(int n) {
    return (char*)(((char*)heap_list_head) + n*WSIZE);
}




/* 
 * Returns the first element, a free block, in seg list n
 */
static void * get_list(int n){
    return (char *) GET(((char*)heap_list_head) + n*WSIZE);
}




/* Getting the prev block from a free block
 * bp is pointing to the payload of a free block
 * Return the start of payload of the prev/next block */
static void *getPrevBlockInHeapFree(void * bp) {
    char * prevStartP = (char *)((char*)bp - 3*WSIZE 
               - GET_SIZE((char *)(bp) - 4 * WSIZE));

    if(GET_ALLOC(prevStartP)) {
        return prevStartP + 1*WSIZE;
    } else {
        return prevStartP + 3*WSIZE;
    }      
}



/* Getting the next block from an free block
 * bp is pointing to the payload of an free block
 * Return the start of the payload of the prev/next block */
static void *getNextBlockInHeapFree(void * bp) {
    char * nextStartP = (char *)((char*)bp - 
          3*WSIZE + GET_SIZE(HDRP_FREE(bp)));

    if(GET_ALLOC(nextStartP)) {
        return nextStartP + 1*WSIZE;
    } else {
        return nextStartP + 3*WSIZE;
    }  
}



 /*
  * mm_check: Used for debugging. Checks that the allocation of free 
  *           blocks and their respective size, allocated bits, prev, 
  *           and next pointers are being set as expected. It iterates 
  *           through all 21 seg lists, checking that their elements exist 
  *           within the bounds of the current heap, that they have a zero 
  *           unallocated bit, and successfully linked to other members
  *           in their list. Additionally, mm_check makes sure that freeing 
  *           occurs as expected and that at no time does a member of the 
  *           free list uncoallesced, unallocated neighbors in physical memory.
  */
void mm_check() {
    char * list;
    char * nextP;
    char * prevP;
    char * nextBlock;
    char * prevBlock;
    char * nextPLinkBack;
    char * prevPLinkForward;
    int count;
    int i;

    // Loops through all of the segregated lists
    for (i = 0 ; i < NUM_SEG_LISTS ; ++i ) {

        // list is the value of the pointer in the heap
        // checking to make sure the heap pointers are in 
        // the proper range of the heap
        if(get_list_addr(i) <= heap_list_head || 
            get_list_addr(i) >=  mem_brk) {
            return 0;
        } else {
            list = get_list(i);
        }

        count = 0;
        // Iterates through all free blocks in this seg list
        while(list != NULL) {
            // Check the allocated bit is marked free
            if(GET_ALLOC(HDRP_FREE(list)) != 0)
                return 0;

            // Checking if the next/prev pointers of the free list are valid
            // Checks if these three elements doubly linked
            nextP = GET(NEXT_BLKP(list));
            prevP = GET(PREV_BLKP(list));
            nextPLinkBack = GET(PREV_BLKP(nextP));
            prevPLinkForward = GET(NEXT_BLKP(prevP));

            if(GET_ALLOC(HDRP_FREE(nextP)) == 1 ||
                          nextPLinkBack != list || 
                         prevPLinkForward != list) {
                return 0;
            } 

            // Checking if the contiguous block is all alloced
            nextBlock = (char*)list - 3*WSIZE + GET_SIZE(HDRP_FREE(list));
            prevBlock = (char*)list - 4*WSIZE;

            if(GET_ALLOC(prevBlock) == 0 || GET_ALLOC(nextBlock) == 0)
                return 0;
            else {
                list = (char *)GET(NEXT_BLKP(list));
                ++count;
            }
        }
    }
    return 1;
}

