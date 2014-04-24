/*
 * Name: Pan Sun
 * Andrew ID: pans
 *
 * Data Structure
 * 1.Type: Segregated free lists
 * 2.Algorithms: First fit
 * 3.Structure of the whole heap:
 * | free list root pointers | prologue | heap blocks | epilogue |
 * 4.Structure of allocated blocks:
 * | header | content | footer |
 * 5.Structure of free blocks:
 * | header | prev_freep | next_freep | --- | footer |
 * 6.Content of header and footer: ( size | 1 bit alloc )
 * 7.Content of prologue: / DSIZE | 0x1 / DSIZE | 0x1 /
 * 8.Content of epilogue: / 0 | 0x1 / 
 * The allocated prologue and epilogue blocks are overhead that
 * eliminate edge conditions during coalescing.
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

// Create aliases for driver tests
// DO NOT CHANGE THE FOLLOWING!
#ifdef DRIVER
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif

/*
 *  Logging Functions
 *  -----------------
 *  - dbg_printf acts like printf, but will not be run in a release build.
 *  - checkheap acts like mm_checkheap, but prints the line it failed on and
 *    exits if it fails.
 */

#ifndef NDEBUG
#define dbg_printf(...) printf(__VA_ARGS__)
#define checkheap(verbose) do {if (mm_checkheap(verbose)) {  \
                             printf("Checkheap failed on line %d\n", __LINE__);\
                             exit(-1);  \
                        }}while(0)
#else
#define dbg_printf(...)
#define checkheap(...)
#endif

/*
 * Define constants
 * ----------------
 */

#define MINI_SIZE 24 
#define WSIZE 4 // Word and header/footer size (bytes)
#define DSIZE 8 // Doubleword size (bytes)
#define NUM_FREE_LISTS 18
#define ALIGNMENT 8
#define CHUNKSIZE 400

/*
 *  Helper functions
 *  ----------------
 */

/* 
 * Align p to a multiple of w bytes
 */
static inline void* align(void* p, unsigned char w) {
    return (void*)(((uintptr_t)(p) + (w-1)) & ~(w-1));
}

/* 
 * Check if the given pointer is 8-byte aligned
 */
static inline int aligned(void* p) {
    return align(p, 8) == p;
}

/*
 * Return whether the pointer is in the heap.
 */
static int in_heap(void* p) {
     return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * This determines which free list a block is added to
 */
static int get_seglist_no(size_t asize){
    if (asize <= 24)
        return 0;
    else if (asize <= 48)
        return 1;
    else if (asize <= 72)
        return 2;
    else if (asize <= 96)
        return 3;
    else if (asize <= 120)
        return 4;
    else if (asize <= 144)
        return 5;
    else if (asize <= 168)
        return 6;
    else if (asize <= 192)
        return 7;
    else if (asize <= 216)
        return 8;
    else if (asize <= 240)
        return 9;
    else if (asize <= 480)
        return 10;
    else if (asize <= 960)
        return 11;
    else if (asize <= 1920)
        return 12;
    else if (asize <= 3840)
        return 13;
    else if (asize <= 7680)
        return 14;
    else if (asize <= 15360)
        return 15;
    else if (asize <= 30720)
        return 16;
    else
        return 17;
}

/*
 *  Block Functions
 *  ---------------
 *  TODO: Add your comment describing block functions here.
 *  The functions below act similar to the macros in the book, but calculate
 *  size in multiples of 4 bytes.
 */

/*
 * Return the size of the given block in multiples of the word size
 */
static inline unsigned int block_size(void* block) {
    REQUIRES(block != NULL);

    return ((*(uint32_t*)((void *)((char *)(block) - WSIZE))) & ~0x7);
}

/*
 * Return the allocation bit of the block
 */
static inline int block_alloc(void* block) {
    REQUIRES(block != NULL);

    return ((*(uint32_t *)((void *)((char*)(block) - WSIZE))) & 0x1);
}

/*
 * Return the size of the given block footer 
 * in multiples of the word size
 */
static inline unsigned int block_footer_size(void* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return ((*(uint32_t*)(((char *)(block) + \
            block_size(block) - DSIZE))) & ~0x7);
}

/*
 * Return the allocation bit of the block footer
 */
static inline int block_footer_alloc(void* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return ((*(uint32_t *)(((char*)(block) + \
            block_size(block) - DSIZE))) & 0x1);
}

/*
 * find the left neighbor block
 */
static inline void* prev_block(void* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return (void*)((char*)(block) - \
        ((*(uint32_t*)((char*)block - DSIZE)) & ~0x7));
}

/*
 * find the right neighbor block
 */
static inline void* next_block(void* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return (void*)((char*)(block) + \
        ((*(uint32_t*)((char*)block - WSIZE)) & ~0x7));
}

/*
 * Return the pointer to the previous block
 */
static inline void* block_prev(void* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return (*(void **)block);
}

/*
 * Return the pointer to the next block
 */
static inline void* block_next(void* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return (*(void **)((char *)block + DSIZE));
}

/*
 * set the previous one 
 */
static inline void set_prev_pointer(void* block, void* p){
    REQUIRES(block != NULL);

    *(void**)(block) = p;
}

/*
 * set the next one 
 */
static inline void set_next_pointer(void* block, void* p){
    REQUIRES(block != NULL);

    *(void **)((char *)block + DSIZE) = p;   
}

/*
 * set the size and the allocation status
 */
static inline void set_size(void* block, size_t size, size_t alloc){
    REQUIRES(block != NULL);

    (*(uint32_t*)((void*)((char*)(block) - WSIZE))) = (size|alloc);
    (*(uint32_t*)((void*)((char*)block + \
        block_size((void*)block) - DSIZE))) = (size|alloc);
}

static int get_free_list_index(size_t size);
static void* find_free_block(size_t size);
static void* extend_heap(size_t size);
static void remove_block(void* block);
static void* add_block_to_list(void* block);
static void* coalesce(void* block);
static void place(void* block, size_t size);

/*
 * other checking functions
 */
static void check_heap_head(int verbose, void* bp);
static void check_free_list(int verbose);
static void* check_block(int verbose);
static void print_block(void *bp);

/*
 * Define global variables
 * -----------------------
 */

static void** free_lists;
static void* heap_start;

/*
 *  Malloc Implementation
 *  ---------------------
 *  The following functions deal with the user-facing malloc implementation.
 */

/*
 * Initialize: return -1 on error, 0 on success.
 * Allocates space for free list pointers.
 * Sets each to point to NULL which means the end of the list.
 */
int mm_init(void) {
    void** current;
    /* create the initial empty heap */ 
    if ((free_lists = mem_sbrk(NUM_FREE_LISTS * DSIZE)) \
        == (void *) - 1)
        return -1;
    current = free_lists;
    for (int i = 0; i < NUM_FREE_LISTS; i++) {
        *current = NULL;
        current++;
    }
    if ((heap_start = mem_sbrk(4 * WSIZE)) == (void *) - 1)
        return -1;
    *(uint32_t *)heap_start = 0; // alignment padding 
    *((uint32_t *)heap_start + 1) = DSIZE|1; // prologue header
    *((uint32_t *)heap_start + 2) = DSIZE|1; // prologue footer 
    *((uint32_t *)heap_start + 3) = 0|1; // epilogue header 
    heap_start = (void*)((char*)heap_start + DSIZE);
    /* Extend the empty heap */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

/*
 * general purpose dynamic storage allocator
 */
void *malloc (size_t size) {
    size_t asize; 
    size_t extendsize;     
    void *bp;
    if (heap_start == 0) mm_init();
    if (size == 0) return NULL;
    /* Adjust block size */
        asize = ((size_t)(size + DSIZE) + (ALIGNMENT-1)) & ~0x7;
    /* Search the free list for a fit */
    if ((bp = find_free_block(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }
    /* No fit found. Get more memory and place the block */
    extendsize = (asize) > (CHUNKSIZE)? (asize) : (CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) return NULL;
    place(bp, asize);

    checkheap(1);
    return bp;
}

/*
 * free block at address bp
 */
void free (void *ptr) {
    if(ptr == 0) return;
    size_t size = block_size(ptr);
    if (heap_start == 0) mm_init();
    set_size(ptr, size, 0);
    ptr = coalesce(ptr);
    ptr = add_block_to_list(ptr);

    checkheap(1);    
}

/*
 * Change the size of the block by mallocing a new block,
 * copying its data, and freeing the old block.  
 */
void* realloc(void *oldptr, size_t size) {
    size_t copysize;
    void *newptr;
    /* if size == 0, then just use free and return NULL */
    if (size == 0) {
        free(oldptr);
        return NULL;
    }
    /* if oldptr == NULL, then just use malloc */
    if (oldptr == NULL) return malloc(size);
    /* if oldptr != NULL, call malloc and copy memory */
    newptr = malloc(size);
    if (!newptr) return NULL;
    copysize = block_size(oldptr);
    copysize = (copysize) < (size)? (copysize) : (size);
    memcpy(newptr, oldptr, copysize);
    free(oldptr);

    checkheap(1);
    return newptr;
}

/*
 * calloc - Allocate the block and set it to zero.
 */
void* calloc (size_t nmemb, size_t size) {
    size_t memsize = nmemb * size;
    void *ptr = malloc(memsize);
    memset(ptr, 0, memsize);

    checkheap(1);
    return ptr;
}

/*
 *  Other Helper functions
 *  ----------------
 */

/* 
 * Returns the index for a free list 
 * with a block to fit the size request
 */
static int get_free_list_index(size_t size){
    int index = 0;
    index = get_seglist_no(size);

    ENSURES(0 <= index && index < NUM_FREE_LISTS);
    return index;
}

/* 
 * Returns a pointer if block of sufficient size is available 
 * will allocate a new block if none are free
 */
static void* find_free_block(size_t size){
    void *bp;
    size_t asize;
    int index = get_free_list_index(size);
    /* first fit search */
    for (int i = index; i < NUM_FREE_LISTS; i++) {
        bp = free_lists[i];
        while (bp != NULL) {
            asize = block_size(bp);
            if (size <= asize) {
                return bp;
            }
            bp = block_next(bp);
        }
    }
    return NULL;
}

/*
 * place a block of 'size' at address bp
 */
static void place(void* bp, size_t size){
    size_t list_size = block_size(bp);
    remove_block(bp);
    /* splitted if larger than minimum size */
    if ((list_size - size) >= MINI_SIZE) {
        set_size(bp, size, 1);
        bp = next_block(bp);
        set_size(bp, (list_size - size), 0);
        bp = add_block_to_list(bp);
    } 
    /* less than minimum size */
    else {
        set_size(bp, list_size, 1);
    }
}

/*
 * Delete one free block from the free list
 */
static void remove_block(void* bp){
    int index = get_free_list_index(block_size(bp));
    void *next = block_next(bp);
    void *prev = block_prev(bp);
    if (bp == free_lists[index]) free_lists[index] = next;
    if(prev != NULL) set_next_pointer(prev, next);
    if(next != NULL) set_prev_pointer(next, prev);
    set_prev_pointer(bp, NULL);
    set_next_pointer(bp, NULL);
}

/*
 * add free block (LIFO)
 * add one free block to an appropriate free list
 */
static void* add_block_to_list(void* bp){
    REQUIRES(bp != NULL);

    int index = get_free_list_index(block_size(bp));
    /* empty list */
    if(free_lists[index] == NULL){
        set_prev_pointer(bp, NULL);
        set_next_pointer(bp, NULL);
    }
    /* set as the head */
    else {
        set_prev_pointer(bp, NULL);
        set_next_pointer(bp, free_lists[index]);
        set_prev_pointer(free_lists[index], bp);
    }
    /* set the root */    
    free_lists[index] = bp;
    return bp;
}

/*
 * extend_heap- Extend the heap with a new free block
 */
static void* extend_heap(size_t words){
    char *bp;
    size_t size;
    void* epilogue;  
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if((long)(bp = mem_sbrk(size)) == -1) return NULL;
    /* Initialize free block header/footer and the epilogue header */
    set_size(bp, size, 0);
    epilogue = next_block((void*)bp);
    (*(uint32_t *)((void *)((char *)(epilogue) - WSIZE))) = (0|1);
    bp = add_block_to_list(bp);
    return bp;
}

/*
 * coalesce - coalesce free blocks nearby and make them a 
 * larger free block
 */
static void* coalesce(void* bp){
    REQUIRES(bp != NULL);

    void* left_block;
    void* right_block;
    int prev_alloc;
    int next_alloc;
    size_t size;
    right_block = next_block(bp);
    left_block = prev_block(bp);
    prev_alloc = block_alloc(left_block);
    next_alloc = block_alloc(right_block);
    size = block_size(bp);   
    if (prev_alloc && next_alloc) {
        return bp;
    } 
    /* next block is free */
    else if (prev_alloc && !next_alloc) {
        size += block_size(right_block);
        remove_block(right_block);
        set_size(bp, size, 0);
    }
    /* prev block is free */
    else if (!prev_alloc && next_alloc) {
        bp = left_block;
        size += block_size(bp);
        remove_block(bp);
        set_size(bp, size, 0);
    }
    /*prev and next are free*/
    else {
        size += block_size(left_block);
        size += block_size(right_block);
        remove_block(left_block);
        remove_block(right_block);
        bp = left_block;
        set_size(bp, size, 0);
    }
    return bp;
}

/*
 *  Checking functions
 *  ----------------
 */

/* 
 * Returns 0 if no errors were found(nothing happens), 
 * otherwise print the error
 */
int mm_checkheap(int verbose) {
    void* bp;
    check_free_list(verbose);
    bp = check_block(verbose);
    check_heap_head(verbose, bp);
    return 0;
}

/*
 * Check Head
 * Check epilogue and prologue blocks
 * Check heap boundaries
 */
static void check_heap_head(int verbose, void* bp){
    /* Check prologue blocks */
    if ((block_size(heap_start) != DSIZE) || \
        !block_alloc(heap_start)) {
        printf("HEAD ERROR: prologue header\n");
    }
    if ((block_footer_size(heap_start) != DSIZE) || \
        !block_footer_alloc(heap_start)) {
        printf("HEAD ERROR: prologue footer\n");
    }
    /* Check epilogue blocks */
    if (block_size(bp) != 0 || !block_alloc(bp)) {
        printf("HEAD ERROR: epilogue\n");
        if(!verbose) print_block(bp);
    }
}

/*
 * Check the free list
 * next/previous are consistent
 * Check in_heap
 * Check alignment
 * Count free blocks and check if match
 * Check size range
 */
static void check_free_list(int verbose){
    void* bp;
    size_t size;
    void* next;
    int free_lists_count = 0;
    int free_blocks_count = 0;
    for (int i = 0; i < NUM_FREE_LISTS; i++) {
        bp = free_lists[i];
        while ((bp != NULL) && (block_size(bp)) > 0) {
            if (!in_heap(bp)) {
                printf("LIST ERROR: %p not in heap\n", bp);
                if (!verbose) print_block(bp);
            }
            if (block_alloc(bp)) {
                printf("LIST ERROR: %p not marked free\n", bp);
            }
            if (!aligned(bp)) {
                printf("LIST ERROR: %p not aligned\n", bp);
            }
            size = block_size(bp);
            next = block_next(bp);
            /* Check if next/previous are consistent */
            if (next != NULL && block_prev(next) != bp) {
                printf("LIST ERROR: %p not consistent\n", bp);
            }
            /* Check size range */
            if (get_free_list_index(size) != i){
                printf("LIST ERROR: %p in wrong list\n", bp);
            }
            free_lists_count++;
            bp = block_next(bp);
        }
    }
    for (bp = heap_start; block_size(bp) > 0; bp = next_block(bp)) {
        if (!block_alloc(bp)) free_blocks_count++;
    }
    if (free_blocks_count != free_lists_count) {
        printf("LIST ERROR: Free block number %d and %d not match\n", \
            free_blocks_count, free_lists_count);
    }
}

/*
 * Check each block in heap
 * Check alignment
 * Check boundaries
 * Check header and footer matching 
 * Check coalescing
 */
static void* check_block(int verbose){
    void *bp = heap_start;
    for (bp = heap_start; bp && block_size(bp) > 0; bp = next_block(bp)) {
        /* Check alignment */
        if (!aligned(bp)) {
            printf("BLOCK ERROR: block not aligned at %p\n", bp);
        }
        /* Check boundaries */
        if (!in_heap(bp)) {
            printf("BLOCK ERROR: boundary violation at %p\n", bp);
        }
        /* Check header and footer */
        if ((block_size(bp) != block_footer_size(bp)) || \
            (block_alloc(bp) != block_footer_alloc(bp))) {
            printf("BLOCK ERROR: not match at %p\n", bp);
            if (!verbose) print_block(bp);
        }
        /* Check coalescing */
        if (!block_alloc(bp) && in_heap(bp) && \
            !block_alloc(next_block(bp))) {
            printf("BLOCK ERROR: Coalesce error at %p\n", bp);
            if (!verbose) print_block(bp);
        }      
    }
    return bp;
}

/* 
 * print information in block 
 */
static void print_block(void *bp){
    printf("%p: header[size:%d,alloc:%d], footer[size:%d,alloc:%d]\n", \
        bp, block_size(bp), block_alloc(bp), block_footer_size(bp), \
        block_footer_alloc(bp));
}
