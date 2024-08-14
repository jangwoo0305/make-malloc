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
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4 //Word Size의 약자로 컴파일 시에 코드 내에서 WSIZE라는 이름을 만나면 ,그것을 4로 대체하라는 의미
#define DSIZE 8 //Double Word Size의 약자로 컴파일 시에 코드 내에서 DSIZE라는 이름을 만나면 ,그것을 8로 대체하라는 의미
#define CHUNKSIZE (1<<12) //초기 또는 확장할 때 할당할 기본 힙 크기 : 4GB

#define MAX(x,y) ((x)>(y) ? (x) : (y))
// 두 값을 비교하여 더 큰 값을 반환.
//메모리 블록 크기 결정시 / 힙 확장 시 크기 결정
#define PACK(size, alloc) ((size) | (alloc))
//둘 중 하나라고 1이면 1이되고, 둘다 0이면 0이된다.
//alloc이 1이되면 할당 되었음을 나타내고 size = 24: 00011000이고 alloc = 1:00000001이므로 이걸 연산하면 00011001(25)가 된다.
//비트 or연산자를 이용하면 두 정보를 하나의 값으로 결합할 수 있다.
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (int)(val))
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define HDRP(bp) ((char*)(bp) - WSIZE)
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(((char*)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE(((char*)(bp) - DSIZE)))
static char *heap_listp;
static char *start_nextfit = 0;
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
void *mm_malloc(size_t size);
static void *find_fit(size_t asize);
void place(void *bp, size_t asize);
void mm_free(void *bp);
void *mm_realloc(void *bp, size_t size);

/* 
 * mm_init - initialize the malloc package.
 */

static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); //현재 블록의 이전 블록이 메모리에서 할당되었는지 여부를 prev_alloc 변수에 저장
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if(prev_alloc && next_alloc){
        start_nextfit = bp;
        return bp;
    }

    else if (prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size,0));
        PUT(FTRP(bp), PACK(size,0));
    }

    else if (!prev_alloc && next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp);
    }

    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)),PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    start_nextfit = bp;
    return bp;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;
    //정렬을 유지하기 위해 짝수 개의 단어를 할당한다.
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; 
    if((long)(bp = mem_sbrk(size)) == -1){
        return NULL;
    }

    PUT(HDRP(bp), PACK(size, 0)); //Free block header 생성. / (prologue block이랑 헷갈리면 안됨.) regular block의 총합의 첫번째 부분. 현재 bp 위치의 한 칸 앞에 헤더를 생성.
    PUT(FTRP(bp), PACK(size, 0)); //Free block footer 생성. / regular block 총합의 마지막 부분.
    PUT(HDRP(NEXT_BLKP(bp)),PACK(0, 1));
    // 처음 세팅의 의미 = bp를 헤더에서 읽은 사이즈만큼 이동하고, 앞으로 한칸 간다. 그위치가 결국 늘린 블록 끝에서 한칸 간거라 거기가 epilogue header 위치.


    return coalesce(bp);
}

int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void*)-1)
        return -1;
    
    PUT(heap_listp,0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE,1));
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE,1));
    PUT(heap_listp + (3 * WSIZE), PACK(0,1));
    heap_listp += (2*WSIZE);
    start_nextfit = heap_listp;

    if(extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */

void *mm_malloc(size_t size)
{
/*
    int newsize = ALIGN(size + SIZE_T_SIZE);
    void *p = mem_sbrk(newsize);
    if (p == (void *)-1)
	return NULL;
    else {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    }
    */
    size_t asize; // 블록 사이즈 조정
    size_t extendsize; // heap에 맞는 fit이 없으면 확장하기 위한 사이즈
    char *bp; 

    if (size == 0) 
        return NULL;

    if (size <= DSIZE){
        asize = 2 * DSIZE;
    }
    else{
        asize = DSIZE *((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    }

    if ((bp = find_fit(asize)) != NULL){
        place(bp,asize);
        return bp;
   }

   extendsize = MAX(asize,CHUNKSIZE);
   if ((bp = extend_heap(extendsize/WSIZE)) == NULL){
    return NULL;
   }
   place(bp,asize);
   return bp;
}

static void *find_fit(size_t asize){
    void *bp;
    for (bp = start_nextfit; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            return bp;
        }
    }
    for (bp = heap_listp; bp != start_nextfit; bp = NEXT_BLKP(bp)){
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            return bp;
        }
    }
    return NULL;
}

void place(void *bp, size_t asize){
    size_t csize = GET_SIZE(HDRP(bp));
    if ((csize-asize) >= (2*DSIZE)){
        PUT(HDRP(bp), PACK(asize,1));
        PUT(FTRP(bp), PACK(asize,1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize,0));
        PUT(FTRP(bp), PACK(csize-asize,0));
    }
    else {
        PUT(HDRP(bp), PACK(csize,1));
        PUT(FTRP(bp), PACK(csize,1));
    }
}
/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
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