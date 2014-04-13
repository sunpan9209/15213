/*
 * mm.c
 * Name: Kuo Liu
 * Andrew ID: kuol
 *
 * Algorithm: I just use segregate list to store each block in seperate
 * list according to its size. When mallocing, I use the first fit strategy,
 * specifically, LIFO strategy. 
 */
 
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>
#include "contracts.h"

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */
/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

/* Basic constants and macros */
#define WSIZE           4               /* Word and header/footer size (bytes) */
#define DSIZE           8               /* Doubleword size (bytes) */
#define CHUNKSIZE       200     /* Extend heap by this amount (bytes) */

#define MAX(x, y)       ((x) > (y)? (x) : (y))
#define MIN(x, y)       ((x) < (y)? (x) : (y))

/* Pack a size and allocate bit into a word */
#define PACK(size, alloc)       ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)          (*(unsigned int *)(p))
#define PUT(p, val)     (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)                     (GET(p) & ~0x7)
#define GET_ALLOC(p)            (GET(p) & 0x1)  /* the 1st bit indicates the alloc state of current block */

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)        (void *)((char *)(bp) - WSIZE)
#define FTRP(bp)        (void *)((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)   (void *)((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)   (void *)((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Segregated Free Lists Definition */
#define LIST_NUM 19
#define MIN_BLOCK_SIZE  24
#define GET_PREVP(bp)           (*(void **)bp)
#define PUT_PREVP(bp, ptr)      (GET_PREVP(bp) = ptr)
#define GET_NEXTP(bp)           (*(void **)((char *)bp + DSIZE))
#define PUT_NEXTP(bp, ptr)      (GET_NEXTP(bp) = ptr)
#define GET_SEGI(lp, i) (*(void **)(lp + (i*DSIZE)))
#define PUT_SEGI(lp, i, ptr)    ((GET_SEGI(lp, i)) = ptr)


static char *heap_start;
static char *seg_list;

/* Basic functions */
static int get_seglist_no(size_t asize);
static void *find_fit(size_t asize);
static void place(void *bp, size_t size);
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *add_free_list(void *bp);
static void delete_free_list(void *bp);

/* Functions for mm_checkheap */
static void check_heap(int verbose);
static void check_free_list();
static int in_heap(const void *p);
static char *check_each_block(int verbose);
void print_block(void *p);


/*
 * Initialize: return -1 on error, 0 on success.
 * Allocates space for free list pointers.
 * Sets each to point to NULL which means the end of the list.
 */
int mm_init(void) {
    /* create the initial empty heap */ 
    if ((seg_list = mem_sbrk(LIST_NUM * DSIZE)) == (void *) - 1)
        return -1;
    for (int i = 0; i < LIST_NUM; i++)
        *(void **)(seg_list + (i * DSIZE)) = NULL;
    if ((heap_start = mem_sbrk(4 * WSIZE)) == (void *) - 1)
        return -1;
    *(uint32_t *)heap_start = 0; /* alignment padding */
    *((uint32_t *)heap_start + 1) = DSIZE|1; /* prologue header */
    *((uint32_t *)heap_start + 2) = DSIZE|1; /* prologue footer */ 
    *((uint32_t *)heap_start + 3) = 0|1; /* epilogue header */
    heap_start += DSIZE;
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

/*
 * extend_heap - Extend heap and return its block pointer
 */
static void *extend_heap(size_t words){
        char *bp;
        size_t size;
        
        /* Allocate an even number of words to maintain alignment */
        size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
        if((long)(bp = mem_sbrk(size)) == -1)
                return NULL;
        
        /* Initialize free block header/footer and the epilogue header */
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
        bp = add_free_list(bp);
        
        return bp;
}
 
/*
 * malloc - The malloc routine returns a pointer to an allocated block
 * payload of at least size bytes. 
 */
void *malloc (size_t size) {
        
        size_t asize;           /* Adjusted block size */
        size_t extendsize;      /* Amount to extend heap if no fit */
        char *bp;
        
        if(heap_start == 0)
                mm_init();
        
        /* Ignore spurious requests */
        if(size == 0)
                return NULL;
        
        /* Adjust block size to include overhead and alignment reqs */
        if(size <= DSIZE)
                asize = MIN_BLOCK_SIZE;
        else
                asize = ALIGN(size + DSIZE);
        
        /* Search the free list for a fit */
        if((bp = find_fit(asize)) != NULL){
                place(bp, asize);
                return bp;
        }
        
        extendsize = MAX(asize, CHUNKSIZE);
        if((bp = extend_heap(extendsize/WSIZE)) == NULL)
                return NULL;
        place(bp, asize);
        
        
        #ifdef MMCHECK
                mm_checkheap(0);
        #endif
        
        return bp;
}

/*
 * free - free a block pointed by ptr
 */
void free (void *ptr) {
        if(ptr == 0)
                return;
        
        size_t size = GET_SIZE(HDRP(ptr));
        if(heap_start == 0)
                mm_init();
        PUT(HDRP(ptr), PACK(size, 0));
        PUT(FTRP(ptr), PACK(size, 0));
        ptr = add_free_list(ptr);
        
        #ifdef MMCHECK
                mm_checkheap(0);
        #endif
}

/*
 * realloc - The realloc routine returns a pointer to an allocated
 * region of at least size bytes.
 */
void *realloc(void *oldptr, size_t size) {
    size_t copysize;
        void *newptr;
        
        /* if size == 0, then just use free and return NULL */
        if(size == 0){
                free(oldptr);
                return NULL;
        }
        
        /* if oldptr == NULL, then just use malloc */
        if(oldptr == NULL)
                return malloc(size);
        
        /* if oldptr != NULL, call malloc and do memory copying operation */
        newptr = malloc(size);
        
        if(!newptr)
                return NULL;
        copysize = GET_SIZE(HDRP(oldptr));
        copysize = MIN(copysize, size);
        memcpy(newptr, oldptr, copysize);
        free(oldptr);
        
        #ifdef MMCHECK
                mm_checkheap(0);
        #endif
        
        return newptr;
}

/*
 * calloc - Allocates memory for an array of nmemb elements of size
 * bytes each and returns pointer to allocated memory. The memory is
 * set to zero before returning.
 */
void *calloc(size_t nmemb, size_t size) {
        size_t memsize = nmemb * size;
        void *ptr = malloc(memsize);
        memset(ptr, 0, memsize);
        return  ptr;
}

/*
 * get_seglist_no - return the number of the segregated list
 * that best fit asize.
 *
 * 1~24                 0
 * 25~48                1
 * 49~72                2
 * 73~96                3
 * 97~120               4
 * 121~240              5
 * 241~480              6
 * 481~960              7
 * 961~1920             8
 * 1921~3840    9
 * 3841~7680    10
 * 7681~15360   11
 * 15361~30720  12
 * 30721~61440  13
 * >61440               14
 */
static int get_seglist_no(size_t asize){
        if(asize <= 24)
                return 0;
        else if(asize <= 32)
                return 1;
        else if(asize <= 40)
                return 2;
        else if(asize <= 56)
                return 4;
        else if(asize <= 72)
                return 5;
        else if(asize <= 88)
                return 6;
        else if(asize <= 104)
                return 7;
        else if(asize <= 120)
                return 8;
        else if(asize <= 240)
                return 9;
        else if(asize <= 480)
                return 10;
        else if(asize <= 960)
                return 11;
        else if(asize <= 1920)
                return 12;
        else if(asize <= 3840)
                return 13;
        else if(asize <= 7680)
                return 14;
        else if(asize <= 15360)
                return 15;
        else if(asize <= 30720)
                return 16;
        else if(asize <= 61440)
                return 17;
        else
                return 18;
}
 
/*
 * find_fit - Find a free block from the segregated lists
 * for the current request size.
 */
static void *find_fit(size_t asize){
        void *bp;
        int seglist_no = get_seglist_no(asize);
        
        for(int i = seglist_no; i < LIST_NUM; ++ i){
                for(bp = GET_SEGI(seg_list, i); (bp != NULL) && \
                                GET_SIZE(HDRP(bp)) > 0; bp = GET_NEXTP(bp)){
                        if(bp != NULL && (asize <= GET_SIZE(HDRP(bp))))
                                return bp;
                }
        }
        
        return NULL;
}

/*
 * place - Place the request block at the beginning of the free block,
 * splitting only if the size of the remainder would equal or exceed
 * the minimum block size
 */
static void place(void *bp, size_t asize){
        size_t csize = GET_SIZE(HDRP(bp));
        delete_free_list(bp);
        if((csize - asize) >= MIN_BLOCK_SIZE){
                PUT(HDRP(bp), PACK(asize, 1));
                PUT(FTRP(bp), PACK(asize, 1));
                bp = NEXT_BLKP(bp);
                PUT(HDRP(bp), PACK(csize - asize, 0));
                PUT(FTRP(bp), PACK(csize - asize, 0));
                bp = add_free_list(bp);
        }else{
                PUT(HDRP(bp), PACK(csize, 1));
                PUT(FTRP(bp), PACK(csize, 1));
        }
}

/*
 * add_free_list - Add the block to free list, just like stack
 */
static void *add_free_list(void *bp){
        
        bp = coalesce(bp);
        int seglist_no = get_seglist_no(GET_SIZE(HDRP(bp)));
        if(GET_SEGI(seg_list, seglist_no) == NULL){
                PUT_PREVP(bp, NULL);
                PUT_NEXTP(bp, NULL);
        }else if(GET_SEGI(seg_list,seglist_no) != NULL){
                PUT_PREVP(bp, NULL);
                PUT_NEXTP(bp, GET_SEGI(seg_list, seglist_no));
                PUT_PREVP(GET_SEGI(seg_list, seglist_no), bp);
        }
        
        PUT_SEGI(seg_list, seglist_no, bp);
        return bp;
}
 
/*
 * delete_free_list - Delete the block from free list
 */ 
static void delete_free_list(void *bp){

        int seglist_no = get_seglist_no(GET_SIZE(HDRP(bp)));
        void *next = GET_NEXTP(bp);
        void *prev = GET_PREVP(bp);
        
        if(bp == GET_SEGI(seg_list, seglist_no))
                PUT_SEGI(seg_list, seglist_no, next);
        if(prev != NULL)
                PUT_NEXTP(prev, next);
        if(next != NULL)
                PUT_PREVP(next, prev);
        PUT_PREVP(bp, NULL);
        PUT_NEXTP(bp, NULL);
}

/*
 * coalesce - Coalesce free blocks
 */
static void *coalesce(void *bp){
        
        size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
        size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
        size_t size = GET_SIZE(HDRP(bp));
        
        if(prev_alloc && next_alloc){
                return bp;
        }else if(prev_alloc && !next_alloc){
                size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
                delete_free_list(NEXT_BLKP(bp));
                PUT(HDRP(bp), PACK(size, 0));
                PUT(FTRP(bp), PACK(size, 0));
        }else if(!prev_alloc && next_alloc){
                bp = PREV_BLKP(bp);
                size += GET_SIZE(HDRP(bp));
                delete_free_list(bp);
                PUT(HDRP(bp), PACK(size, 0 ));
                PUT(FTRP(bp), PACK(size, 0 ));
        }else{
                size += (GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))));
                delete_free_list(PREV_BLKP(bp));
                delete_free_list(NEXT_BLKP(bp));
                PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
                PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
                bp = PREV_BLKP(bp);
        }
        return bp;
}
 
/*
 * mm_checkheap - heap checker
 * Checking the heap(segregated list)
 *   -Check epilogue and prologue blocks
 *   -Check each block's address alignment
 *   -Check heap boundaries
 *   -Check each block's header and footer: size(minimum size, alignment), 
 *    previous/next allocate/free bit, header and footer matching each other.
 *   -Check coalescing: no two consecutive free blocks in the heap
 * 
 * Checking the free list(segregated list)
 *   -All next/previous are constent
 *   -All free list pointers points between mem_heap_lo() and mem_heap_high()
 *   -Count free blocks by iterating through every block and traversing free
 *    list by pointers and see if they match
 *   -All blocks in each list bucket fall within bucket size range(segregated list)
 */
int mm_checkheap(int verbose) {
        check_heap(verbose);
        check_free_list();
        return 0;
}

/*
 * Checking the heap(segregated list)
 *   -Check epilogue and prologue blocks
 *   -Check each block's address alignment
 *   -Check heap boundaries
 *   -Check each block's header and footer: size(minimum size, alignment), 
 *    previous/next allocate/free bit, header and footer matching each other.
 *   -Check coalescing: no two consecutive free blocks in the heap
 */
static void check_heap(int verbose){
        /* Check prologue blocks */
        if((GET_SIZE(HDRP(heap_start)) != DSIZE) || !GET_ALLOC(HDRP(heap_start))){
                printf("Error in prologue header\n");
        }
        if((GET_SIZE(FTRP(heap_start)) != DSIZE) || !GET_ALLOC(FTRP(heap_start))){
                printf("Error in prologue footer\n");
        }
        
        /* Check each block in heap */
        char *bp = check_each_block(verbose);
        
        /* Check epilogue blocks */
        if(GET_SIZE(HDRP(bp)) != 0 || !GET_ALLOC(HDRP(bp))){
                printf("Error in epilogue\n");
        }
        if(verbose)
                print_block(bp);
}

/*
 * Checking the free list(segregated list)
 *   -All next/previous are consistent
 *   -All free list pointers points between mem_heap_lo() and mem_heap_high()
 *   -Count free blocks by iterating through every block and traversing free
 *    list by pointers and see if they match
 *   -All blocks in each list bucket fall within bucket size range(segregated list)
 */
static void check_free_list(){
        size_t size;
        void *next;
        void *bp;
        
        int count_free_list = 0;
        int count_free_block = 0;
        
        for(int i = 0; i < LIST_NUM; ++ i){
                for(bp = GET_SEGI(seg_list, i); 
                        bp != NULL && (GET_SIZE(HDRP(bp))) > 0; PUT_NEXTP(bp, GET_NEXTP(bp))){
                        size = GET_SIZE(HDRP(bp));
                        /* All next/previous are consistent */
                        next = GET_NEXTP(bp);
                        if(next != NULL && GET_PREVP(next) != bp){
                                printf("%p's next/previous are not consistent\n", bp);
                        }
                        
                        /* All free list pointers points between mem_heap_lo() and mem_heap_high() */
                        if(!in_heap(bp)){
                                printf("%p fall out of heap\n", bp);
                        }
                        
                        /* All blocks in each list bucket fall within bucket size range */
                        if(get_seglist_no(size) != i){
                                printf("%p fall in the wrong bucket\n", bp);
                        }
                        ++ count_free_list;
                }
        }
        
        for(bp = heap_start; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
                if(!GET_ALLOC(HDRP(bp)))
                        ++ count_free_block;
        }
        
        /* Count free blocks by iterating through every block and 
         * traversing free list by pointers and see if they match 
         */
        if(count_free_block != count_free_list){
                printf("Free block number does not match\n");
        }
}

/* 
 *print information in block bp 
 */
void print_block(void *bp){
        printf("%p: header[size:%d,alloc:%d], footer[size:%d,alloc:%d]\n",\
                bp, \
                GET_SIZE(HDRP(bp)), GET_ALLOC(HDRP(bp)),\
                GET_SIZE(FTRP(bp)), GET_ALLOC(FTRP(bp)));
}

/*
 * Check the following elements for each block in heap_start
 *   -Check each block's address alignment
 *   -Check heap boundaries
 *   -Check header and footer matching each other
 *   -Check coalescing
 */
static char *check_each_block(int verbose){

        char *bp = heap_start;
        for(bp = heap_start; bp && GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
                /* Check each block's address alignment */
                if((size_t)bp % 8){
                        printf("Alignment Error at %p\n", bp);
                }
                
                /* Check heap boundaries */
                if(!in_heap(bp)){
                        printf("Heap boundary violation at %p\n", bp);
                }
                
                /* Check header and footer matching each other */
                if(GET(HDRP(bp)) != GET(FTRP(bp))){
                        printf("Header does not match footer at %p\n", bp);
                        print_block(bp);
                }
                
                /* Check coalescing */
                if( !GET_ALLOC(HDRP(bp)) &&
                        in_heap(bp) &&
                        !GET_ALLOC(HDRP(NEXT_BLKP(bp)))){
                        printf("Coalesce error at %p\n", bp);
                }
                
                if(verbose){
                        print_block(bp);
                }
        }
        return bp;
}

/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void *p) {
        return p <= mem_heap_hi() && p >= mem_heap_lo();
}