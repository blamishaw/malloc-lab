/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */

/* THE EIGHT CARDINAL RULES
 for (rule = 1; rule < 9; rule++)
    printf("%d", rules[rule]);
 
 rules = [
 1. Know your rights.
 2. Acknowledge your sources.
 3. Protect your work.
 4. Avoid suspicion.
 5. Do your own work.
 6. Never falsify a record or permit another person to do so.
 7. Never fabricate data, citations, or experimental results.
 8. Always tell the truth when discussing your work with your instructor.
 ]
 
 */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "Explicit Free List",
    /* First member's full name */
    "Brendan Lamishaw",
    /* First member's email address */
    "brendanlamishaw2021@u.northwestern.edu",
    /* Second member's full name (leave blank if none) */
    "Naveena Sharma",
    /* Second member's email address (leave blank if none) */
    "naveenasharma2021@u.northwestern.edu"
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
#define WSIZE 4                 /* Word and header/footer size in bytes */
#define DSIZE 8                 /* Double word size in bytes */
#define MIN_BLOCK_SIZE 16       /* Blocks must be at least 24 bytes as that is the min size for free blocks */
#define CHUNKSIZE (1 << 12)     /* Extend heap by this amount (bytes) */

#define MAX(x,y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)          (*(unsigned int *)(p))
#define PUT(p, val)     (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)     (GET(p) & ~0x7)
#define GET_ALLOC(p)    (GET(p) & 0x1)

/* Given block pointer bp, compute address of its header and footer */
#define HDRP(bp)        ((char *)(bp) - WSIZE)
#define FTRP(bp)        ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Macros for the explicit free-list implementation */
#define PREV_FREE(bp)   ((char *)(bp))
#define NEXT_FREE(bp)   ((char *)(bp) + WSIZE)

#define GET_PREV_FREE(bp) (*(char **)(PREV_FREE(bp)))
#define GET_NEXT_FREE(bp) (*(char **)(NEXT_FREE(bp)))

#define PACK_PREV(bp, val)  ((GET_PREV_FREE(bp)) = (val))
#define PACK_NEXT(bp, val)  ((GET_NEXT_FREE(bp)) = (val))



/* Static global pointer to prologue block of heap */
static char *heap_listp = 0;

/* Static global pointer to head of free-list */
static char *free_listp = 0;


/* Forward-declarations of helper functions */
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void *coalesce(void *bp);
static int mm_check(void);
static void removeBlock(void *bp);
static void insertBlock(void *bp);

/* Forward declarations for check functions */
static int checkBlockHFA(void *bp);
static int checkBlocksOverlap(void *bp);
static int checkBlockEscapedCoalesce(void *bp);


/*
    As of right now this implementation uses:
        1. Implicit Free List structure
        2. First-fit free block finding
        3. Immediate coalescing of free blocks
 
    Once working, next thing to try is:
        1. Next-fit free block finding
*/

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(2*MIN_BLOCK_SIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);                                                     /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(MIN_BLOCK_SIZE, 1));                   /* Prologue header */
    
    PUT(heap_listp + (2*WSIZE), 0);
    PUT(heap_listp + (3*WSIZE), 0);
    
    
    PUT(heap_listp + (4*WSIZE), PACK(MIN_BLOCK_SIZE, 1));              /* Prologue footer */
    PUT(heap_listp + MIN_BLOCK_SIZE + WSIZE, PACK(0, 1));                                /* Epilogue header */

    free_listp = heap_listp + DSIZE;
    
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    
    /* Assign head to initialized free block */
    
    
    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;        /* Adjusted block size */
    size_t extendsize;   /* Amount to extend heap if no fit */
    char *bp;
    
    // Ignore spurious requests
    if (size == 0)
        return NULL;
    
    /* Adjust block size to include overhead and alignment reqs */
    /* Make sure allocated block is 16 bytes -- add padding */
    if (size <= 2*DSIZE)
        asize = MIN_BLOCK_SIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL){
        place(bp, asize);
        return bp;
    }
    
    /* No fit found. Get more memory and place block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    if (heap_listp == 0)
        mm_init();
    
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    
    /* This immediately coalesces when a block is freed */
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

static void *extend_heap(size_t words) {
    char *bp;
    size_t size;
    
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if (size < MIN_BLOCK_SIZE)
        size = MIN_BLOCK_SIZE;
    
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));           /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));           /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));   /* New epilogue header */
    
    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    
    /* Previous and next blocks are allocated -> no coalescing necessary */
    if (next_alloc && prev_alloc){
        return bp;
    }
    
    /* Previous block unallocated, next block allocated -> coalesce with previous block */
    else if (!prev_alloc && next_alloc){
        // Update header of previous block and footer of bp
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));                  /* Why not FTRP? */
        removeBlock(PREV_BLKP(bp));                             /* Remove the previous block from free list */
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));                /* Update header of previous block */
        PUT(FTRP(bp), PACK(size, 0));                           /* Update footer of current block */
        bp = PREV_BLKP(bp);                                     /* Set bp to point to start of previous block */
        
        
    }
    
    /* Next block unallocated, prev block allocated -> coalesce with next block */
    else if (!next_alloc && prev_alloc){
        // Update header of current block and footer of next block
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        removeBlock(NEXT_BLKP(bp));                  /* Remove next block from free list */
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));                /* Different from book code -- why? */
        
    }
    
    /* Both the prev and next blocks are unallocated -> coalesce in both directions*/
    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        removeBlock(PREV_BLKP(bp));                             /* Remove the previous block from free list */
        removeBlock(NEXT_BLKP(bp));                             /* Remove next block from free list */
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));                /* Update header of previous block */
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));                /* Update footer of next block */
        bp = PREV_BLKP(bp);
        
    }
    
    insertBlock(bp);
    
    return bp;
}

/* Helper function to find a free block in the heap
   Uses the first-fit method
*/

//static void *find_fit(size_t asize){
//    void *bp;
//
//    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
//        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
//            return bp;
//        }
//    }
//    return NULL;
//}

/* Find first free block that fits in the explicit free list --> linked list traversal */
static void *find_fit(size_t asize) {
    void *curr = free_listp;
    while (curr != NULL){
        if (GET_SIZE(HDRP(curr)) >= asize){
            return curr;
        }
        curr = GET_NEXT_FREE(curr);
    }
    return NULL;
}

/* Helper function that deals with free block splitting protocol */
//void place(void *bp, size_t asize){
//
//    size_t csize = GET_SIZE(HDRP(bp));
//
//    if ((csize - asize) >= (2*ALIGNMENT)){
//        PUT(HDRP(bp), PACK(asize, 1));
//        PUT(FTRP(bp), PACK(asize, 1));
//        bp = NEXT_BLKP(bp);
//        PUT(HDRP(bp), PACK(csize - asize, 0));
//        PUT(FTRP(bp), PACK(csize - asize, 0));
//    }
//    else {
//        PUT(HDRP(bp), PACK(csize, 1));
//        PUT(FTRP(bp), PACK(csize, 1));
//    }
//}

void place(void *bp, size_t asize) {
    
    size_t csize = GET_SIZE(HDRP(bp));
    
    /* Remove free block from list */
    removeBlock(bp);
    
    /* If new free block will be greater than 24 bytes */
    if ((csize - asize) >= (MIN_BLOCK_SIZE)){
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        removeBlock(bp);
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        //insertBlock(bp);
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        removeBlock(bp);
    }
}

/* Add a block to the front of the free list */
static void insertBlock(void *bp){
    
    /* If explicit list is empty */
    if (!free_listp){
        PACK_PREV(bp, NULL);
        PACK_NEXT(bp, NULL);
        free_listp = bp;
    }
    
    /* If explicit list has 1 or more free blocks */
    else {
        PACK_PREV(bp, NULL);
        PACK_NEXT(bp, free_listp);
        
        PACK_PREV(free_listp, bp);
        free_listp = bp;
    }
    
}

/* Removes a block from the free list */
static void removeBlock(void *bp){
    
    /* If bp is the first and only block in the free list */
    if (!GET_PREV_FREE(bp) && !GET_NEXT_FREE(bp)){
        free_listp = 0;
    }
    
    /* If bp is the first but not only block in the free list*/
    else if (!GET_PREV_FREE(bp) && GET_NEXT_FREE(bp)) {
        /* Set prev of next free block to 0 and update free list head */
        PACK_NEXT(GET_PREV_FREE(bp), NULL);
        free_listp = GET_NEXT_FREE(bp);
    }
    
    /* If bp is at the end of the list */
    else if (GET_NEXT_FREE(bp) && !GET_NEXT_FREE(bp)) {
        /* Set next of prev block to 0 */
        PACK_PREV(GET_NEXT_FREE(bp), NULL);
    }
    
    /* If bp is somewhere in the middle of the list */
    else {
        /* Set next of prev block to next block */
        PACK_NEXT(GET_PREV_FREE(bp), GET_NEXT_FREE(bp));
        
        /* Set prev of next block to prev block*/
        PACK_PREV(GET_NEXT_FREE(bp), GET_PREV_FREE(bp));
    }
    
    
}
    

static int mm_check(void) {
    
    char *bp;
    int errno = 1;
    
    // For each block in the heap
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        //printf("%p: %d\n", bp, GET_SIZE(HDRP(bp)));
        errno = checkBlockHFA(bp);
        
        /* If block is allocated, check that it does not overlap with the next block */
        if (GET_ALLOC(HDRP(bp)))
            errno = checkBlocksOverlap(bp);
        
        /* If block is free, check if the next block is free -> if so then bp escaped coalescing */
        if (!GET_ALLOC(HDRP(bp)))
            errno = checkBlockEscapedCoalesce(bp);
        
    }
    return errno;
}

/* Function to check that a block's header and footer match and that it is aligned */
static int checkBlockHFA(void *bp) {
    int errno = 1;
    
    /* Check header and footer match */
    if (GET_SIZE(HDRP(bp)) != GET_SIZE(FTRP(bp))){
        printf("ERROR: Size of header and footer do not match\n");
        errno = 0;
    }
    
    if (GET_ALLOC(HDRP(bp)) != GET_ALLOC(FTRP(bp))){
        printf("ERROR: Allocation status of header and footer do not match\n");
        errno = 0;
    }
    
    /* Make sure payload is aligned */
    if (ALIGN(GET_SIZE(HDRP(bp))) != GET_SIZE(HDRP(bp))) {
        printf("ERROR: Payload is not aligned\n");
        errno = 0;
    }
    
    return errno;
}

/* Function to check if an allocated block overlaps with the block after it */
static int checkBlocksOverlap(void *bp){
    
    /* Check if the address of bp + the size of bp is greater than the address of the next block */
    if (bp + GET_SIZE(HDRP(bp)) - WSIZE >= NEXT_BLKP(bp)) {
        printf("ERROR: Block overlaps with next block\n");
        return 0;
    }
    
    return -1;
}

static int checkBlockEscapedCoalesce(void *bp){
    
    /* If bp is free, check if next block is also free */
    if (!GET_ALLOC(HDRP(NEXT_BLKP(bp))))
        printf("Block escaped coalescing\n");
        return 0;
    return -1;
}
        
        
    


