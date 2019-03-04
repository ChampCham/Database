
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

team_t team = {
    /* Team name */
    "SEEDAENGPENSEETAWAN",
    /* First member's full name */
    "Banyawat Kruythong Champ",
    /* First member's email address */
    "banyawat.kry@student.mahidol.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};
/* Basic constants and macros: */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
//#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~(ALIGNMENT-1))
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define LISTLIMIT   20 /* Number of segregated lists */
#define WSIZE       4             /* Word and header/footer size (bytes) */ //line:
#define DSIZE       8             /* Doubleword size (bytes) */
#define INITCHUNKSIZE (1<<6)
#define CHUNKSIZE  (1 << 12)      /* Extend heap by this amount (bytes) */
#define REALLOC_BUFFER  (1<<7)

#define MAX(x, y)  ((x) > (y) ? (x) : (y))
#define MIN(x, y)  ((x) < (y) ? (x) : (y))

/* Pack a size and allocated bit into a word. */
#define PACK(size, alloc)  ((size) | (alloc & 0x1))

/* Read and write a word at address p */
//#define GET(p)       (*(unsigned int *)(p))
static inline size_t GET(void *p) {
    return  *(size_t *)p;
}

// Preserve reallocation bit
#define PUT(p, val)       (*(unsigned int *)(p) = (val) | GET_TAG(p))

//#define PUT(p, val)  (*(unsigned int *)(p) = (val))
// Clear reallocation bit
static inline void PUT_NOTAG (void *p, size_t val){
  *((size_t *)p) = val;
}

// Store predecessor or successor pointer for free blocks
#define SET_PTR(p, ptr) (*(unsigned int *)(p) = (unsigned int)(ptr))


/* Read the size and allocated fields from address p. */
#define GET_SIZE(p)   (GET(p) & ~0x7)
#define GET_ALLOC(p)  (GET(p) & 0x1)
#define GET_TAG(p)  (GET(p) & 0x2)

/* Adjust reallocation tag */
static inline size_t REMOVE_RATAG(void *p){
    return GET(p) & 0x2;
}
static inline size_t SET_RATAG(void *p){
    return GET(p) | 0x2;
}




/* Given block ptr bp, compute address of its header and footer. */
#define HDRP(bp)  ((char *)(bp) - WSIZE)
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks. */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
//#define NEXT_BLKP(bp)  ((void *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
//#define PREV_BLKP(bp) ((void *)(bp) - GET_SIZE((void *)(bp) - DSIZE))

/* Global variables: */
static char *heap_listp=0; /* Pointer to first block */
static void *segregated_free_lists[LISTLIMIT]; /* Array of pointers to segregated free lists */
/* Function prototypes for internal helper routines: */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
//static void *find_fit(size_t asize);
static void *place(void *bp, size_t asize);

/* Function prototypes for heap consistency checker routines: */
static void checkblock(void *bp);
static void checkheap(int verbose);
static void printblock(void *bp);

///*myMacros */
///*Pointer to get NEXT and PREVIOUS pointer of free_list*/
//#define NEXT_PTR(p)  (*(char **)(p + WSIZE))
//#define PREV_PTR(p)  (*(char **)(p))

////Address of free block's predecessor and successor entries
//static inline void* PRED_PTR(void *ptr){
//    return ((char *)(ptr));
//}
//
//static inline void* SUCC_PTR(void *ptr){
//    return ((char*)(ptr) + WSIZE);
//}
//
//// Address of free block's predecessor and successor on the segregated list
//#define SUCC(p)  (*(char **)(p + WSIZE))
//#define PRED(p)  (*(char **)(p))
//

// Address of free block's predecessor and successor entries
static inline void* PRED_PTR(void *ptr){
    return ((char *)(ptr));
}

static inline void* SUCC_PTR(void *ptr){
    return ((char*)(ptr) + WSIZE);
}

// Address of free block's predecessor and successor on the segregated list
static inline void* PRED(void *ptr){
    return (*(char **)(ptr));
}

static inline void* SUCC(void *ptr){
    return (*(char **)(SUCC_PTR(ptr)));
}


/* myVariables */
// Pointer pointing to starting of explicit free list
static char* freeListPtr=0;

/* myMethods */
// Function prototypes for next_fit and best_fit
//static void *next_fit(size_t asize);
//static void *best_fit(size_t asize);

// Functions prototypes for adding and deleting free memory blocks in free_list
static void free_list_add(void* ptr, size_t size);
static void free_list_delete(void* ptr);





/*
 * mm_init - Initialize the memory manager
 */
/* $begin mminit */
int mm_init(void)
{

    int list; /* List Counter*/
    char *heap_start; /* Pointer to beginning of heap */


    /* Initialize array of pointers to segregated free lists */
    for (list = 0; list < LISTLIMIT; list++) {
        segregated_free_lists[list] = NULL;
    }

    /* Create the initial empty heap */
    if ((long)(heap_start= mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;


    PUT(heap_start, 0);                          /* Alignment padding */
    PUT(heap_start + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_start + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_start + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
    //heap_listp += (2*WSIZE);

    // Initialize freeListPtr to point to starting of free memory in heap
	//freeListPtr=heap_listp;

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    //if (extend_heap(CHUNKSIZE/WSIZE) == NULL) /*Cannot extend the heap*/
    if (extend_heap(INITCHUNKSIZE) == NULL) /*Cannot extend the heap*/
        return -1;
    return 0;
}
/* $end mminit */


/*
 * mm_malloc - Allocate a block with at least size bytes of payload
 */
/* $begin mmmalloc */
void *mm_malloc(size_t size)
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp = NULL;  /* Block pointer */
    int list = 0; /* List counter */


    //if (heap_listp == 0){
    //    mm_init();
    //}


    /* Ignore size 0 cases */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = ALIGN(size+DSIZE);




    /* Search the free list for a fit */
    size_t fitsize = asize;


    while (list < LISTLIMIT) {
        if ((list == LISTLIMIT - 1) || ((fitsize <= 1) && (segregated_free_lists[list] != NULL))) {
            bp = segregated_free_lists[list];
            // Ignore blocks that are too small or marked with the reallocation bit
            while ((bp != NULL) && ((asize > GET_SIZE(HDRP(bp))) || (GET_TAG(HDRP(bp)))))
            {
                bp = PRED(bp);
            }
            if (bp != NULL)
                break;
        }

        fitsize >>= 1;
        list++;
    }

   // if ((bp = find_fit(asize)) != NULL) {
   //     place(bp, asize);
   //     return bp;
   // }

    /* No fit found (ptr == NULL). Get more memory and place the block */
    if (bp == NULL){
        extendsize = MAX(asize,CHUNKSIZE);
        if ((bp = extend_heap(extendsize)) == NULL)  /*extended heap*/
            return NULL;
    }

    bp = place(bp, asize);
    return bp;

}


/* $end mmmalloc */

/* $begin mmplace */
static void *place(void *bp, size_t asize)
{
	size_t ptr_size = GET_SIZE(HDRP(bp));
	size_t remainder = ptr_size - asize;

    free_list_delete(bp); // free block is deleted from free_list

    if (remainder <= DSIZE * 2) {
		PUT(HDRP(bp), PACK(ptr_size, 1));
		PUT(FTRP(bp), PACK(ptr_size, 1));
	}else if (asize >= 100) {
        /* split block */
        PUT(HDRP(bp), PACK(remainder, 0)); /* Block header */
        PUT(FTRP(bp), PACK(remainder, 0)); /* Block footer */
        PUT_NOTAG(HDRP(NEXT_BLKP(bp)), PACK(asize, 1)); /* Next header */
        PUT_NOTAG(FTRP(NEXT_BLKP(bp)), PACK(asize, 1)); /* Next footer */
        free_list_add(bp, remainder);
        return NEXT_BLKP(bp);
    }else{/* Split block */
        PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		//bp = NEXT_BLKP(bp);  //Next block
		PUT_NOTAG(HDRP(NEXT_BLKP(bp)), PACK(remainder, 0));
		PUT_NOTAG(FTRP(NEXT_BLKP(bp)), PACK(remainder, 0));
		free_list_add(NEXT_BLKP(bp),remainder);  //Insert_node
		//coalesce(bp);

    }

	return bp;
}
/* $end mmplace */


/*
 * find_fit - Find a fit for a block with asize bytes
 */
//static void *find_fit(size_t asize)
//{
//    void *bp;
//
//    //for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) { /*start block pointer at 0 to the end where block size = -1*/
//    for (bp = freeListPtr; GET_ALLOC(HDRP(bp)) == 0; bp = NEXT_BLKP(bp)) { /*start block pointer from the first free block  to the end where allocated bit != 0 (Not free)*/
//        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {  /*If allocated bit is 0 and asize <= the block size*/
//            return bp;
//        }
//    }
//    return NULL; /* No fit */
//}


/*static void *next_fit(size_t asize)
{
	char *temp=freeListPtr;
	for(;GET_SIZE(HDRP(freeListPtr)) > 0;freeListPtr=NEXT_BLKP(freeListPtr))
		if (!GET_ALLOC(HDRP(freeListPtr)) && asize <= GET_SIZE(HDRP(freeListPtr)))
			return freeListPtr;
	for(freeListPtr=heap_listp;freeListPtr<temp;freeListPtr=NEXT_BLKP(freeListPtr))
		if (!GET_ALLOC(HDRP(freeListPtr)) && asize <= GET_SIZE(HDRP(freeListPtr)))
			return freeListPtr;
	return NULL;
}*/

/*static void *best_fit(size_t asize)
{
	void *bp;
	int flag=0;
	unsigned int min;
	for(bp=heap_listp;GET_SIZE(HDRP(bp)) > 0;bp=NEXT_BLKP(bp))
	{
		if (!GET_ALLOC(HDRP(bp)) && asize <= GET_SIZE(HDRP(bp)))
		{
			if(flag==0)
			{
				min=GET_SIZE(HDRP(bp));
				freeListPtr=bp;
				flag=1;
			}
			else
			{
				if(GET_SIZE(HDRP(bp))<min)
				{
					min=GET_SIZE(HDRP(bp));
					freeListPtr=bp;
				}
			}
		}
	}
	if(flag==1)
		return freeListPtr;
	return NULL;
}*/

/*
 * mm_free - Free a block
 */
/* $begin mmfree */
void mm_free(void *bp)
{

    //if (bp == 0)
    //    return;


    size_t size = GET_SIZE(HDRP(bp));
    REMOVE_RATAG(HDRP(NEXT_BLKP(bp))); /* Unset the reallocation tag on the next block */
    /* $end mmfree */
    //if (heap_listp == 0){
   //     mm_init();
   // }

    /* Adjust the allocation status in boundary tags */
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    /* Insert new block into appropriate list */
    free_list_add(bp, size);

    /* Coalesce free block */
    coalesce(bp);
    return;
}

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
/* $begin mmfree */
static void *coalesce(void *bp)
{
    //size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))) || PREV_BLKP(bp) == bp ; // prev_alloc will be true if previous        block is allocated or its size is zero
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));


    // Do not coalesce with previous block if the previous block is tagged with Reallocation tag
    if (GET_TAG(HDRP(PREV_BLKP(bp))))
        prev_alloc = 1;


    /*previous block size = m1, current block size = n, next block size = m2*/
    if (prev_alloc && next_alloc) {            /* Case 1 previous allocated bit = next allocated bit  = 1 */
        //free_list_add(bp,size);					   // adding free block in free_list
        return bp;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 next allocated bit = 0, so the next block is free*/
        free_list_delete(bp);
        free_list_delete(NEXT_BLKP(bp));       // next free block is deleted from free_list
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); /*current_block_size = current_block_size + next_block_size   || size = n+m2*/
        PUT(HDRP(bp), PACK(size, 0));          /*the current block header size = n+m2, the current block header allocated bit = 0 (free)*/
        PUT(FTRP(bp), PACK(size,0));           /*the current block footer size = n+m2, the current block footer allocated bit =  0 (free)*/
    }

    else if (!prev_alloc && next_alloc) {         /* Case 3 previuos  allocated bit = 0, so the previous block is free*/
        free_list_delete(bp);
        free_list_delete(PREV_BLKP(bp));          // previous free block is deleted from free_list
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));    /*size = n+m1*/
        PUT(FTRP(bp), PACK(size, 0));             /*the current block footer size = n+m1, the current block footer allocated bit  = 0 (free)*/
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));  /*the previous block header size = n+m1, the previous block header allocated bit = 0 (free)*/
        bp = PREV_BLKP(bp);                       /*Move pointer to the initial previous block address*/
    }

    else {                                         /* Case 4 previous allocated bit = next allocated bit =  0, both block are free*/
        free_list_delete(bp);
        free_list_delete(PREV_BLKP(bp));			// both free blocks are deleted from free_list
		free_list_delete(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); /*size = n+m1+m2*/
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));    /*the previous block header size = n+m1+m2, the previous block header allocated bit = 0 (free)*/
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));    /*the next block footer size = n+m1+m2, the next block footer allocated bit = 0 (free)*/

        bp = PREV_BLKP(bp);                          /*Move pointer to the initial previous block address*/

    }
    free_list_add(bp, size);								// add newly coalesced block to free_list
    return bp;
}
/* $end mmfree */
//
///* myMethods */
//// adds free block pointed by ptr to the free_list
//static void free_list_add(void* ptr){
//	NEXT_PTR(ptr)=freeListPtr;
//	PREV_PTR(freeListPtr)=ptr;
//	PREV_PTR(ptr)=NULL;
//	freeListPtr=ptr;
//}
//
//// deletes free block pointed by ptr to the free_list
//static void free_list_delete(void* ptr){
//	if(PREV_PTR(ptr)==NULL)						//if ptr points to root of free_list
//		freeListPtr=NEXT_PTR(ptr);
//	else										//if ptr points to any arbitary block in free_list
//		NEXT_PTR(PREV_PTR(ptr))=NEXT_PTR(ptr);
//	PREV_PTR(NEXT_PTR(ptr))=PREV_PTR(ptr);
//}

/*
 * insert_node - Insert a block pointer into a segregated list. Lists are
 *               segregated by byte size, with the n-th list spanning byte
 *               sizes 2^n to 2^(n+1)-1. Each individual list is sorted by
 *               pointer address in ascending order.
 */
static void free_list_add(void *ptr, size_t size) {
    int list = 0;
    void *search_ptr = ptr;
    void *insert_ptr = NULL;

    /* Select segregated list*/
    while ((list < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;
        list++;
    }

/* Select location on list to insert pointer while keeping list
     organized by byte size in ascending order. */
    search_ptr = segregated_free_lists[list];
    while ((search_ptr != NULL) && (size > GET_SIZE(HDRP(search_ptr)))) {
        insert_ptr = search_ptr;
        search_ptr = PRED(search_ptr);
    }

    // Set predecessor and successor
    if (search_ptr != NULL) {
        if (insert_ptr != NULL) {
            SET_PTR(PRED_PTR(ptr), search_ptr);
            SET_PTR(SUCC_PTR(search_ptr), ptr);
            SET_PTR(SUCC_PTR(ptr), insert_ptr);
            SET_PTR(PRED_PTR(insert_ptr), ptr);
        } else {
            SET_PTR(PRED_PTR(ptr), search_ptr);
            SET_PTR(SUCC_PTR(search_ptr), ptr);
            SET_PTR(SUCC_PTR(ptr), NULL);

            /* Add block to appropriate list */
            segregated_free_lists[list] = ptr;
        }
    } else {
        if (insert_ptr != NULL) {
            SET_PTR(PRED_PTR(ptr), NULL);
            SET_PTR(SUCC_PTR(ptr), insert_ptr);
            SET_PTR(PRED_PTR(insert_ptr), ptr);
        } else {
            SET_PTR(PRED_PTR(ptr), NULL);
            SET_PTR(SUCC_PTR(ptr), NULL);

            /* Add block to appropriate list */
            segregated_free_lists[list] = ptr;
        }
    }

    return;
}

/*
 * delete_node: Remove a free block pointer from a segregated list. If
 *              necessary, adjust pointers in predecessor and successor blocks
 *              or reset the list head.
 */

static void free_list_delete(void *ptr) {
    int list = 0;
    size_t size = GET_SIZE(HDRP(ptr));

    /* Select segregated list */
    while ((list < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;
        list++;
    }

    if (PRED(ptr) != NULL) {
        if (SUCC(ptr) != NULL) {
            SET_PTR(SUCC_PTR(PRED(ptr)), SUCC(ptr));
            SET_PTR(PRED_PTR(SUCC(ptr)), PRED(ptr));
        } else {
            SET_PTR(SUCC_PTR(PRED(ptr)), NULL);
            segregated_free_lists[list] = PRED(ptr);
        }
    } else {
        if (SUCC(ptr) != NULL) {
            SET_PTR(PRED_PTR(SUCC(ptr)), NULL);
        } else {
            segregated_free_lists[list] = NULL;
        }
    }

    return;
}


void *mm_realloc(void *ptr, size_t size)
{
    void *new_ptr = ptr;    /* Pointer to be returned */
    size_t new_size = size; /* Size of new block */
    int remainder;          /* Adequacy of block sizes */
    int extendsize;         /* Size of heap extension */
    int block_buffer;       /* Size of block buffer */

    /* Ignore invalid block size */
    if (size == 0)
        return NULL;

    /* Adjust block size to include boundary tag and alignment requirements */
    if (new_size <= DSIZE) {
        new_size = 2 * DSIZE;
    } else {
        new_size = ALIGN(size+DSIZE);
    }

    /* Add overhead requirements to block size */
    new_size += REALLOC_BUFFER;

    /* Calculate block buffer */
    block_buffer = GET_SIZE(HDRP(ptr)) - new_size;

    /* Allocate more space if overhead falls below the minimum */
    if (block_buffer < 0) {
        /* Check if next block is a free block or the epilogue block */
        if (!GET_ALLOC(HDRP(NEXT_BLKP(ptr))) || !GET_SIZE(HDRP(NEXT_BLKP(ptr)))) {
            remainder = GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(NEXT_BLKP(ptr))) - new_size;
            if (remainder < 0) {
                extendsize = MAX(-remainder, CHUNKSIZE);
                if (extend_heap(extendsize) == NULL)
                    return NULL;
                remainder += extendsize;
            }

             free_list_delete(NEXT_BLKP(ptr));

            // Do not split block
            PUT_NOTAG(HDRP(ptr), PACK(new_size + remainder, 1)); /* Block header */
            PUT_NOTAG(FTRP(ptr), PACK(new_size + remainder, 1)); /* Block footre */
        } else {
            new_ptr = mm_malloc(new_size - DSIZE);
            memcpy(new_ptr, ptr, MIN(size, new_size));
            mm_free(ptr);
        }
        block_buffer = GET_SIZE(HDRP(new_ptr)) - new_size;
    }

    /* Tag the next block if block overhead drops below twice the overhead */
    if (block_buffer < 2 * REALLOC_BUFFER)
        SET_RATAG(HDRP(NEXT_BLKP(new_ptr)));

    /* Return the reallocated block */
    return new_ptr;
}

/* $end mmfree */

//
///*
// *   Extend the heap with a free block and return that block's address.
// */
//static void * extend_heap(size_t words)
//{
//	void *bp;
//	size_t size;
//
//	/* Allocate an even number of words to maintain alignment. */
//	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
//
//	if ((bp = mem_sbrk(size)) == (void *)-1)
//		return (NULL);
//
//	/* Initialize free block header/footer and the epilogue header. */
//	PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
//	PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
//	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
//
//	/* Coalesce if the previous block was free. */
//	return (coalesce(bp));
//}

/*
 * extend_heap - Extend the heap with a system call. Insert the newly
 *               requested free block into the appropriate list.
 */
static void *extend_heap(size_t size)
{
    void *bp;   /* Pointer to newly allocated memory */
    size_t asize;  /*Adjusted size */

    /* Allocate an even number of words to maintain alignment. */
    asize = ALIGN(size); /* Maintain alignment*/

    /* Extend the heap */
    if ((bp = mem_sbrk(asize)) == (void *)-1)
        return NULL;

    /* Set headers and footer */
    /* Initialize free block header/footer and the epilogue header. */
    PUT_NOTAG(HDRP(bp), PACK(asize, 0)); /* Free block header */
    PUT_NOTAG(FTRP(bp), PACK(asize, 0)); /* Free block footer */
    PUT_NOTAG(HDRP(NEXT_BLKP(bp)), PACK(0, 1));  /* Epilogue header */

    /* Insert new block into appropriate list */
    free_list_add(bp, asize);

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}


/*
 * The remaining routines are heap consistency checker routines.
 */

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Perform a minimal check on the block "bp".
 */
static void checkblock(void *bp){

	if ((size_t)bp % DSIZE)
		printf("Error: %p is not doubleword aligned\n", bp);
	if (GET(HDRP(bp)) != GET(FTRP(bp)))
		printf("Error: header does not match footer\n");
}

/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Perform a minimal check of the heap for consistency.
 */
void checkheap(int verbose) {
	void*bp=freeListPtr;
        while (NEXT_PTR(bp)!=NULL) {
            //checks if blocks in free_list are actually free
            if (GET_ALLOC(HDRP(bp)) == 1 || GET_ALLOC(FTRP(bp)) == 1){
                    printf("Encountered an allocated block in free list\n");
                    return;
            }
            bp  = NEXT_PTR(bp);
        }

    if (verbose)
		printf("Heap (%p):\n", heap_listp);

	if (GET_SIZE(HDRP(heap_listp)) != DSIZE ||
	    !GET_ALLOC(HDRP(heap_listp)))
		printf("Bad prologue header\n");
	checkblock(heap_listp);

	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (verbose)
			printblock(bp);
		checkblock(bp);
	}

	if (verbose)
		printblock(bp);
	if (GET_SIZE(HDRP(bp)) != 0 || !GET_ALLOC(HDRP(bp)))
		printf("Bad epilogue header\n");

}

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Print the block "bp".
 */
static void printblock(void *bp) {
	size_t halloc, falloc;
	size_t hsize, fsize;

	checkheap(0);
	hsize = GET_SIZE(HDRP(bp));
	halloc = GET_ALLOC(HDRP(bp));
	fsize = GET_SIZE(FTRP(bp));
	falloc = GET_ALLOC(FTRP(bp));

	if (hsize == 0) {
		printf("%p: end of heap\n", bp);
		return;
	}

	printf("%p: header: [%zu:%c] footer: [%zu:%c]\n", bp,
	    hsize, (halloc ? 'a' : 'f'),
	    fsize, (falloc ? 'a' : 'f'));
}


