/*
 * File Name : mm.c
 * Author : Mayur Sharma
 * Andrew id : mayurs
 * 
 * Description :This is a malloc package based on first fit and segregated
 * explicit list.The headers and footers are stored as described in the 
 * book, ie, the last bit is used to store whether the block is allocated 
 * or not. The others bits bar the last 3 are used to store the size the 
 * size of the free blobk. The footers are the replicas of headers but are 
 * present at the end of any block. The next and previous free block in 
 * the list are stored in the first two words after the header respectively 
 * and are stored as the offset to heap_listp (which always remains constant)
 * which allows to  store these values in a word instead of a double word 
 * thereby making the minimum block size to 16. The bucket sizes are all 
 * initialized to zero and the lists for all of them are present as global 
 * pointers,
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

//* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Doubleword size (bytes) */
#define BSIZE      16       /* Minimum block size required (bytes) */
#define CHUNKSIZE  (1<<9) /* Extend heap by this amount (bytes) */  

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) //line:vm:mm:pack

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))           
#define PUT(p, val)  (*(unsigned int *)(p) = (val))   

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                  
#define GET_ALLOC(p) (GET(p) & 0x1)                   

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                     
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) 
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/*Given offset p, or absolute address ap, compute the other */
#define CONVERTTOOFFSET(ap) ((unsigned int)((((unsigned long)(ap))-((unsigned long)heap_listp))*(!(!((unsigned long)(ap))))))
#define CONVERTFROMOFFSET(p) ((unsigned long)((((unsigned long)(GET(p)))+((unsigned long)(heap_listp)))*(!(!((unsigned long)(GET(p)))))))

/* Read and Write offsets as next and previous pointers at given offset*/
#define GETA(p)       ((unsigned long )(CONVERTFROMOFFSET(p)))           
#define PUTA(p, val)  (*(unsigned int*)(CONVERTFROMOFFSET(p)) = (CONVERTTOOFFSET(val)))

/* Read and Write offsets as next and previous pointers at an absolute 
 * address*/
#define PUTAFREE(fl,val) ((*(unsigned int*)(fl))=(CONVERTTOOFFSET(val)))

/* Global variables */

/* Pointer to first block in the heap. Serves as reference */
static char *heap_listp = 0;

/* Pointers to free list of blocks less than or equal to specified no.  */
static char *free_listp_16 = 0;
static char *free_listp_32 = 0;
static char *free_listp_40 = 0;
static char *free_listp_72 = 0;
static char *free_listp_132 = 0;
static char *free_listp_520 = 0;
static char *free_listp_1032 = 0;
static char *free_listp_2056 = 0;
static char *free_listp_3080 = 0;
static char *free_listp_5128 = 0;
static char *free_listp_7168 = 0;
static char *free_listp_max = 0;

/* Function prototypes for internal helper routines */
inline static void *extend_heap(size_t words);
inline static void place(void *bp, size_t asize);
inline static void *find_fit(size_t asize);
inline static void *coalesce(void *bp);
inline static void printblock(void *bp);
inline static void checkblock(void *bp);
inline static void addtolist(void* bp);
inline static void removefromlist(unsigned long next, unsigned long prev,
		unsigned long size);
inline static void update(size_t asize, void* free_listp);
inline static char* nextlist(int index);
inline static char* getlist(size_t asize, int* index);

/*Variable that is used is coalesce function to indicate
 * that initialization is taking place*/
static int forinit = 1;
/* 
 * mm_init - Initialize the memory manager 
 */

int mm_init(void)
{
	forinit = 1;
	heap_listp = 0; /* Pointer to first block */

	/*Initialize the free lists to NULL */
	free_listp_16 = 0;
	free_listp_32 = 0;
	free_listp_40 = 0;
	free_listp_72 = 0;
	free_listp_132 = 0;
	free_listp_520 = 0;
	free_listp_1032 = 0;
	free_listp_2056 = 0;
	free_listp_3080 = 0;
	free_listp_5128 = 0;
	free_listp_7168 = 0;
	free_listp_max = 0;

	/* Create the initial empty heap */
	if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *) -1)
		return -1;
	PUT(heap_listp, 0); /* Alignment padding */
	PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
	PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
	PUT(heap_listp + (3*WSIZE), PACK(0, 1)); /* Epilogue header */
	heap_listp += (2 * WSIZE);

	/* Extend the empty heap with a free block of CHUNKSIZE bytes */
	if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
		return -1;

	/*Initial releveant free list points to the first & only free block*/
	free_listp_520 = heap_listp + DSIZE;
	return 0;
}

/* 
 * mm_malloc - Allocate a block with at least size bytes of payload 
 */

void *malloc(size_t size)
{
	size_t asize; /* Adjusted block size */
	size_t extendsize; /* Amount to extend heap if no fit */
	char *bp;

	if (heap_listp == 0)
	{
		mm_init();
	}

	/* Ignore spurious requests */
	if (size == 0)
		return NULL;

	/* Adjust block size to include overhead and alignment reqs. */

	/*If size less than or equal to 8 then make it 16 bytes 
	 * including header and footer */
	if (size <= DSIZE)
		asize = BSIZE;
	else
		/* Align it to 8 byte boundary */
		asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

	/* Search the free list for a fit */

	if ((bp = find_fit(asize)) != NULL)
	{
		place(bp, asize);

		return bp;
	}

	/* No fit found. Get more memory and place the block */
	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
		return NULL;

	place(bp, asize);

	return bp;
}

/* 
 * mm_free - Free a block 
 */

void free(void *bp)
{

	if (bp == 0)
		return;

	size_t size = GET_SIZE(HDRP(bp));

	if (heap_listp == 0)
	{
		mm_init();
	}

	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	coalesce(bp);

}

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */

static void *coalesce(void *bp)
{
	size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	unsigned long next = 0;
	unsigned long prev = 0;
	size_t tempsize;

	size_t size = GET_SIZE(HDRP(bp));

	if (forinit) /* For init function */
	{
		forinit = 0;
		free_listp_520 = bp;
		PUTAFREE(free_listp_520, 0);
		PUTAFREE(free_listp_520+WSIZE, 0);
		return bp;
	}

	if (prev_alloc && next_alloc) /* Case 1 */
	{

		addtolist(bp);

	}

	else if (prev_alloc && !next_alloc) /* Case 2 */
	{

		next = GETA(NEXT_BLKP(bp));
		prev = GETA(NEXT_BLKP(bp)+WSIZE);
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		tempsize = GET_SIZE(HDRP(NEXT_BLKP(bp)));
		removefromlist(next, prev, tempsize);
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size,0));
		addtolist(bp);

	}

	else if (!prev_alloc && next_alloc) /* Case 3 */
	{

		next = GETA(PREV_BLKP(bp));
		prev = GETA(PREV_BLKP(bp)+WSIZE);
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		tempsize = GET_SIZE(HDRP(PREV_BLKP(bp)));
		removefromlist(next, prev, tempsize);
		bp = PREV_BLKP(bp);
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
		addtolist(bp);

	}

	else /* Case 4 */
	{

		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
		prev = GETA(NEXT_BLKP(bp)+WSIZE);
		next = GETA(NEXT_BLKP(bp));
		tempsize = GET_SIZE(HDRP(NEXT_BLKP(bp)));
		removefromlist(next, prev, tempsize);
		prev = GETA(PREV_BLKP(bp)+WSIZE);
		next = GETA(PREV_BLKP(bp));
		tempsize = GET_SIZE(HDRP(PREV_BLKP(bp)));
		removefromlist(next, prev, tempsize);
		bp = PREV_BLKP(bp);
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
		addtolist(bp);

	}
	return bp;
}

/*
 * calloc - Allocate the block and set it to zero.
 */
void *calloc (size_t nmemb, size_t size)
{
  size_t bytes = nmemb * size;
  void *newptr;

  newptr = malloc(bytes);
  memset(newptr, 0, bytes);

  return newptr;
}


/*
 * mm_realloc - Naive implementation of realloc
 */
void *realloc(void *ptr, size_t size)
{

	size_t oldsize;
	void *newptr;

	/* If size == 0 then this is just free, and we return NULL. */
	if (size == 0)
	{
		free(ptr);
		return 0;
	}

	/* If oldptr is NULL, then this is just malloc. */
	if (ptr == NULL)
	{
		return malloc(size);
	}

	newptr = malloc(size);

	/* If realloc() fails the original block is left untouched  */
	if (!newptr)
	{
		return 0;
	}

	/* Copy the old data. */
	oldsize = GET_SIZE(HDRP(ptr));
	if (size < oldsize)
		oldsize = size;
	memcpy(newptr, ptr, oldsize);

	/* Free the old block. */
	mm_free(ptr);

	return newptr;
}

/* 
 * The remaining routines are internal helper routines 
 */

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */

static void *extend_heap(size_t words)
{
	char *bp;
	size_t size;

	/* Allocate an even number of words to maintain alignment */
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	if ((long) (bp = mem_sbrk(size)) == -1)
		return NULL;

	/* Initialize free block header/footer and the epilogue header */
	PUT(HDRP(bp), PACK(size, 0)); /* Free block header */
	PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
	/* Coalesce if the previous block was free */

	return coalesce(bp);

}

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */

static void place(void *bp, size_t asize)

{
	unsigned long next = 0;
	unsigned long prev = 0;
	size_t csize = GET_SIZE(HDRP(bp));

	next = GETA(bp); /*Get the address of next block in free list*/
	prev = GETA(bp+WSIZE); /* Get the address of prev block in free list */

	if ((csize - asize) >= (BSIZE)) /* If remaining size is >= 16 */
	{
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		next = GETA(bp);
		prev = GETA(bp+WSIZE);
		removefromlist(next, prev, csize); /*Remove whole block frm free list*/
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize-asize, 0));
		PUT(FTRP(bp), PACK(csize-asize, 0));
		addtolist(bp); /*Put the remaining block back in free list*/

	}
	else /* If remaining size is < 16 */
	{
		/*Remove whole block frm free list*/
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
		next = GETA(bp);
		prev = GETA(bp+WSIZE);
		removefromlist(next, prev, csize);

	}

}

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */

static void *find_fit(size_t asize)
{
	char* bp;
	int first = 1;
	char * free_listp;
	int index = 0;

	/*Get the relevant bucket for the size*/
	free_listp = getlist(asize, &index);

	do
	{
		if (!first)
		{
			free_listp = nextlist(index); /*Go to the next bucket*/
			index++;
		}
		for (bp = free_listp; bp != 0; bp = (char*) GETA(bp))
		{
			if (asize <= GET_SIZE(HDRP(bp)))
			{

				return bp;
			}
		}
		first = 0;

	} while (index <= 10);

	return NULL;

}

/* 
 * printblock - Prints the block information
 */

static void printblock(void *bp)
{
	size_t hsize, halloc, fsize, falloc;
	hsize = GET_SIZE(HDRP(bp));
	halloc = GET_ALLOC(HDRP(bp));
	fsize = GET_SIZE(FTRP(bp));
	falloc = GET_ALLOC(FTRP(bp));

	if (hsize == 0)
	{
		printf("%p: EOL\n", bp);
		return;
	}

	printf("%p: header: [%lu:%c] footer: [%lu:%c]\n", bp, hsize,
			(halloc ? 'a' : 'f'), fsize, (falloc ? 'a' : 'f'));

	printf("Next = %p\n", (char*) GETA(bp));
	printf("Prev = %p\n", (char*) GETA(bp+WSIZE));
}

/* 
 * checkheap - check of the heap for consistency 
 */
void mm_checkheap(int verbose)
{
	int i = 1;
	char *free_listp = free_listp_16;
	int index = 0;
	int first = 1;
	char*bp;

	if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
		printf("Bad prologue header\n");

	do
	{
		{
			if (!first)
			{
				free_listp = nextlist(index);
				index++;
			}
		}

		bp = free_listp;
		if (verbose)
			printf("Head of Free List (%p):\n", free_listp);

		i = 1;
		for (bp = free_listp; bp != 0; bp = (char*) GETA(bp))
		{
			if (verbose)
			{
				printf("Block %i\n", i++);
				printblock(bp);
			}
			checkblock(bp);
		}
		first = 0;

	} while (index <= 10);

}

/* 
 * checkblock - check of the block for consistency 
 */
static void checkblock(void *bp)
{
	if ((size_t) bp % 8)
		printf("Error: %p is not doubleword aligned\n", bp);
	if (GET(HDRP(bp)) != GET(FTRP(bp)))
	{
		printf("Error: header does not match footer\n");
		exit(1);
	}

	if (GETA(bp) != 0)
	{

		if (GETA(((char*)GETA(bp))+WSIZE) != (unsigned long) bp)
		{
			printf("Error: next pointer mismatch !! \n");
			exit(1);
		}
	}

	if (GETA(bp+WSIZE) != 0)
	{
		if (GETA((char*) (GETA (bp+WSIZE))) != (unsigned long) bp)
		{
			printf("Error: prev pointer mismatch !!  \n");
			exit(1);
		}
	}

}

/* 
 * addtolist - takes in a pointer & adds it to the head of relevant free list. 
 * It updates the next and previous pointers and keeps the list consistent.     
 */
static void addtolist(void* bp)
{
	int size = GET_SIZE(HDRP(bp));
	char* free_listp;
	int index;

	free_listp = getlist(size, &index);

	PUTAFREE(bp, (unsigned long )free_listp); /*Change next of current block*/

	/*Change prev of cuurent block to 0 as it will be the 1st block in list*/
	PUTAFREE(bp+WSIZE, 0);

	if (free_listp != 0)
	{
		/*Change prev of next block in free list */
		PUTAFREE(free_listp+WSIZE, (unsigned long )bp);
	}
	/*free list points to cuurent block*/
	free_listp = bp;

	/*update the relevent global free list*/
	update(size, free_listp);

}

/* 
 * removefromlist - takes in the next and previous pointers of a block
 * and update their pointers. It finds the correct list based on the size 
 * it is given as a parameter. It keeps the list consistent.     
 */
static void removefromlist(unsigned long next, unsigned long prev, size_t size)
{
	char* free_listp;
	int index;

	free_listp = getlist(size, &index);

	if (prev != 0)
	{ /*Update the next of the prev block*/
		PUTAFREE((char* )prev, (unsigned long )next);
	}
	else
	{
		free_listp = (char*) next;
	}
	if (next != 0)
	{
		/*Update the prev of the next block*/
		PUTAFREE((char*)next+WSIZE, (unsigned long )prev);
	}

	//Updating the global_free_list
	update(size, free_listp);

}

/* 
 * getlist - takes in the size and returns the correct free list for that size.
 * Also updates the index associated with each free list  
 */
static char* getlist(size_t asize, int* index)
{

	if (asize == 16)
	{
		*index = 0;
		return (free_listp_16);
	}

	else if (asize <= 32)
	{
		*index = 1;
		return (free_listp_32);
	}
	else if (asize <= 40)
	{
		*index = 2;
		return (free_listp_40);
	}
	else if (asize <= 72)
	{
		*index = 3;
		return (free_listp_72);
	}
	else if (asize <= 132)
	{
		*index = 4;
		return (free_listp_132);
	}
	else if (asize <= 520)
	{
		*index = 5;
		return (free_listp_520);
	}
	else if (asize <= 1032)
	{
		*index = 6;
		return (free_listp_1032);
	}
	else if (asize <= 2056)
	{
		*index = 7;
		return (free_listp_2056);
	}
	else if (asize <= 3080)
	{
		*index = 8;
		return (free_listp_3080);
	}
	else if (asize <= 5128)
	{
		*index = 9;
		return (free_listp_5128);
	}
	else if (asize <= 7168)
	{
		*index = 10;
		return (free_listp_7168);
	}

	else
	{
		*index = 11;
		return (free_listp_max);

	}
}

/* 
 * nextlist - takes in the index and returns the next bucket
 * in order of size
 */
static char* nextlist(int index)
{
	switch (index)
	{

	case 0:
	{
		return free_listp_32;
	}
	case 1:
	{
		return free_listp_40;
	}
	case 2:
	{
		return free_listp_72;
	}
	case 3:
	{
		return free_listp_132;
	}
	case 4:
	{
		return free_listp_520;
	}
	case 5:
	{
		return free_listp_1032;
	}
	case 6:
	{
		return free_listp_2056;
	}
	case 7:
	{
		return free_listp_3080;
	}
	case 8:
	{
		return free_listp_5128;
	}
	case 9:
	{
		return free_listp_7168;
	}
	case 10:
	{
		return free_listp_max;
	}
	default:
		return free_listp_max;

	}
}

/* 
 * update - updates the relevant global free_list
 */
static void update(size_t asize, void* free_listp)
{

	if (asize == 16)
	{
		free_listp_16 = free_listp;
	}
	else if (asize <= 32)
	{
		free_listp_32 = free_listp;
	}
	else if (asize <= 40)
	{
		free_listp_40 = free_listp;
	}
	else if (asize <= 72)
	{
		free_listp_72 = free_listp;
	}

	else if (asize <= 132)
	{
		free_listp_132 = free_listp;
	}
	else if (asize <= 520)
	{
		free_listp_520 = free_listp;
	}
	else if (asize <= 1032)
	{
		free_listp_1032 = free_listp;
	}
	else if (asize <= 2056)
	{
		free_listp_2056 = free_listp;
	}
	else if (asize <= 3080)
	{
		free_listp_3080 = free_listp;
	}
	else if (asize <= 5128)
	{
		free_listp_5128 = free_listp;
	}
	else if (asize <= 7168)
	{
		free_listp_7168 = free_listp;
	}
	else
	{
		free_listp_max = free_listp;

	}

}
