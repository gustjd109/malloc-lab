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
    "team 8",
    /* First member's full name */
    "Hyun Sung Hwang",
    /* First member's email address */
    "hyunsung109@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
// size보다 큰 가장 가까운 ALIGNMENT의 배수로 만들어준다 -> 정렬!
// size = 7 : (00000111 + 00000111) & 11111000 = 00001110 & 11111000 = 00001000 = 8
// size = 13 : (00001101 + 00000111) & 11111000 = 00010000 = 16
// 1 ~ 7 bytes : 8 bytes
// 8 ~ 16 bytes : 16 bytes
// 17 ~ 24 bytes : 24 bytes
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

/* 메모리 할당 시 기본적으로 header와 footer를 위해 필요한 더블워드만큼의 메모리 크기 */
// size_t : 해당 시스템에서 어떤 객체나 값이 포함할 수 있는 최대 크기의 데이터
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* 기본 상수 및 매크로 */
#define WSIZE 4 // 워드와 헤더 및 풋터 크기 정의
#define DSIZE 8 // 더블 워드 크기 정의
#define CHUNKSIZE (1<<12) // 초기 가용 블록과 확장시 추가되는 블록 크기 정의

#define MAX(x, y) ((x) > (y)? (x) : (y)) // 최대값 구하는 함수 정의

/* 헤더 및 풋터의 값(크기와 할당 여부) 반환 */
#define PACK(size, alloc) ((size) | (alloc)) // 크기와 할당 비트를 통합해서 헤더와 풋터에 저장할 수 있는 값 반환

/* 주소 p에서 워드를 읽거나 쓰는 함수 */
#define GET(p) (*(unsigned int *)(p)) // 포인터 p가 가리키는 블록의 데이터 반환
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // 포인터 p가 가리키는 블록의 값 저장

/* 헤더 또는 풋터에서 블록의 크기와 할당된 구역을 읽어옴 */
// & ~0x7 => 0x7:0000 0111 ~0x7:1111 1000이므로 ex. 1011 0111 & 1111 1000 = 1011 0000 : size 176bytes
#define GET_SIZE(p) (GET(p) & ~0x7) // 포인터 p가 가리키는 헤더 또는 풋터의 크기 반환
// & 0x1 => ex. 1011 0111 | 0000 0001 = 1 : Allocated
#define GET_ALLOC(p) (GET(p) & 0x1) // 포인터 p가 가리키는 헤더 또는 풋터의 할당 비트 반환

/* 각각 블록 헤더와 풋터가 가리키는 포인터 반환 */
// bp : 현재 블록 포인터
#define HDRP(bp) ((char *)(bp) - WSIZE) // 현재 블록 헤더의 위치 반환(bp - 1워드)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 현재 블록 풋터의 위치 반환(bp + 현재 블록 크기 - 더블 워드 크기)

/* 각각 이전 블록과 다음 블록을 가리키는 포인터 반환 */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) // 다음 블록의 블록 포인터 반환(bp + 현재 블록 크기 - 1워드)
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // 이전 블록의 블록 포인터 반환(bp - 현재 블록 크기 - 2워드)

#define FIRST_FIT // define하면 first_fit으로 탐색
// #define NEXT_FIT  // define하면 next_fit으로 탐색
// #define BEST_FIT  // define하면 best_fit으로 탐색

// 전역 힙 변수 및 함수 선언
static void *heap_listp;
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

#ifdef NEXT_FIT
    static void* last_freep;  // next_fit 사용 시 마지막으로 탐색한 가용 블록
#endif

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* 메모리에서 4워드 가져와서 빈 힙 생성 */
    // mem_sbrk: 힙 영역을 incr(0이 아닌 양수) 바이트 만큼 확장하고, 새로 할당된 힙 영역의 첫 번째 바이트를 가리키는 제네릭 포인터를 반환
    if((heap_listp = mem_sbrk(4 * WSIZE)) == (void *) -1) // heap_listp에 4워드 만큼의 메모리를 확장
        return -1; // 실패 시 -1 반환

    PUT(heap_listp, 0);                                 // 더블 워드 경계로 정렬된 미사용 패딩
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));      // 프롤로그 헤더를 1워드 할당하고 DSIZE로 값 삽입
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));      // 프롤로그 풋터를 1워드 할당하고 DSIZE로 값 삽입
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));          // 에필로그 헤더를 1워드 할당하고 0 사이즈 삽입
    heap_listp += (2 * WSIZE); // 정적 전역 변수는 늘 prologue block을 가리킴

    #ifdef NEXT_FIT
        last_freep = heap_listp;
    #endif

    /* CHUNKSIZE 만큼 힙을 확장해 초기 가용 블록을 생성 */
    if(extend_heap(CHUNKSIZE / WSIZE) == NULL) // 힙을 CHUNKSIZE 바이트로 확장하고 초기 가용 블록을 생성
        return -1; // 실패 시 -1 반환
    return 0;
}

// 두 가지 다른 경우에 호출
// 1) 힙이 초기화될 경우
// 2) mm_malloc이 적당한 맞춤 fit을 찾지 못했을 경우
// 위 경우일 때 정렬을 유지하기 위해서 extend_heap은 요청한 크기를 인접 2워드의 배수(8배수)로 반올림하고, 메모리 시스템으로부터 추가적인 힙 공간을 요청
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; // 워드가 홀수인 경우 정렬을 위해 인접 2워드의 배수(8바이트)로 반올림하며, 추가적인 힙 공간 요청
    if((long)(bp = mem_sbrk(size)) == -1) // mem_sbrk 함수에서 size가 할당 가능한 힙의 범위를 초과했다고 판단하면, -1을 반환하고 할당하지 않음
        return NULL;

    PUT(HDRP(bp), PACK(size, 0)); // 새로운 블록에 헤더 생성
    PUT(FTRP(bp), PACK(size, 0)); // 새로운 블록의 푸터 생성
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 새로운 블록 뒤에 붙는 에필로그 헤더 생성

    return coalesce(bp); // 이전 힙이 가용 블록으로 끝났다면, 두 개의 가용 블록을 통합하기 위해 coalesce 호출
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp)); // 해당 블록의 크기를 알아내 헤더와 풋터의 정보를 수정

    PUT(HDRP(bp), PACK(size, 0)); // 헤더를 0으로 할당
    PUT(FTRP(bp), PACK(size, 0)); // 풋터를 0으로 할당
    coalesce(bp); // coalesce를 호출하여 가용 메모리를 연결
}

static void *coalesce(void *bp)
{
    // 직전 블록의 풋터과 직후 블록의 헤더를 보고 가용 여부를 확인
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 직전 블록 가용 여부
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 직후 블록 가용 여부
    size_t size = GET_SIZE(HDRP(bp));

    if(prev_alloc && next_alloc) { // case 1 : 이전, 다음 블록이 모두 할당인 경우 -> 현재만 반환
        return bp;
    }

    else if(prev_alloc && !next_alloc) { // case 2 : 이전 블록 할당, 다음 블록 가용인 경우 -> 다음 블록과 병합
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if(!prev_alloc && next_alloc) { // case 3 : 이전 블록 가용, 다음 블록 할당인 경우 -> 이전 블록과 병합
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else { // case 4 : 이전, 다음 블록 모두 가용인 경우 -> 이전 블록과 다음 블록 병합
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    #ifdef NEXT_FIT
        last_freep = bp; // next-fit 사용 시, 추적 포인터를 연결이 끝난 블록의 블록 포인터로 변경
    #endif

    return bp;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize; /* 조정된 블록 크기 */
    size_t extendsize; /* 적합하지 않은 경우 힙을 확장할 크기 */
    char *bp;

    /* 가짜 요청 무시 */
    // 만약 할당 요청받은 용량이 0이면 그냥 반환
    if(size == 0)
        return NULL;

    // /* 오버헤드 및 정렬 요구 사항을 포함하도록 블록 크기를 조정 */
    // if(size <= DSIZE) // 사이즈가 2워드(8바이트) 이하라면 4워드로 할당 요청(앞의 1워드는 헤더에, 뒤의 1워드는 풋터)
    //     asize = 2 * DSIZE;
    // else // 할당 요청의 용량이 2워드 초과(8바이트의 배수에 맞지 않은 경우)라면 충분한 8바이트의 배수의 용량을 할당
    //     asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    // 요청 사이즈에 헤더와 풋터를 위한 더블 워드 공간(SIZE_T_SIZE)을 추가한 후 align 해줌
    asize = ALIGN(size + SIZE_T_SIZE);

    /* 적당한 크기의 가용 블록을 가용 리스트에서 검색 */
    if((bp = find_fit(asize)) != NULL) { // first_fit 함수로 적당한 크기의 가용 블록을 검색
        place(bp, asize); // place 함수로 초과 부분을 분할하고 새롭게 할당한 블록의 블록 포인터를 반환
        return bp;
    }

    /* 적당한 크기의 가용 블록을 찾지 못한다면 extend_heap 함수로 힙을 확장하여 추가 확장 블록을 배정 */
    extendsize = MAX(asize, CHUNKSIZE); // 둘 중 더 큰 값으로 사이즈 지정
    // extend_heap()은 워드 단위로 인자를 받으므로 WSIZE로 나눔
    if((bp = extend_heap(extendsize / WSIZE)) == NULL) // 힙 확장 실패 시 NULL을 반환(extendsize / WSIZE = 칸의 개수)
        return NULL;
    place(bp, asize); // 힙 확장 성공 시 블록을 배치하고 bp 반환
    return bp;
}

static void *find_fit(size_t asize)
{
    /* First-fit */
    #ifdef FIRST_FIT
        void *bp;

        // Free list에서 유일한 할당 블록은 리스트 맨 뒤의 프롤로그 블록이므로, 할당 블록을 만나면 모든 list 노드들을 다 확인한 것으로 탐색 종료
        for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) { // bp는 힙의 시작점을 가리키는 heap_listp에서 시작하여 에필로그 블록까지 탐색
            if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) { // 만약 해당 헤더의 블록이 할당되어있지 않고(GET_ALLOC 함수로 판단), 사이즈도 원하는 크기(asize)보다 크다면(GET_SIZE로 판단)
                return bp; // bp를 반환
            }
        }
        return NULL; // 못 칮으면 NULL 반환
    #endif

    /* Next-fit */
    #ifdef NEXT_FIT
        void* bp;
        void* old_last_freep = last_freep;

        // 이전 탐색이 종료된 시점에서부터 다시 탐색
        // first-fit과 동일하게 탐색하나, 탐색 시작점이 다름
        for(bp = last_freep; GET_SIZE(HDRP(bp)) > 0 ; bp = NEXT_BLKP(bp)) {
            if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
                return bp;
        }

        // 만약 끝까지 찾았는데도 안 나왔으면 처음부터 다시 탐색
        for(bp = heap_listp; bp < old_last_freep; bp = NEXT_BLKP(bp)) {
            if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
                return bp;
        }

        last_freep = bp; // 다시 탐색을 마침 시점으로 last_freep을 설정

        return NULL;
    #endif

    /* Best-fit */
    #ifdef BEST_FIT
        void *bp;
        void *best_fit = NULL;

        for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
            if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
                // 기존에 할당하려던 공간보다 더 최적의 공간이 나타났을 경우 리턴 블록 포인터 갱신
                if(!best_fit || GET_SIZE(HDRP(bp)) < GET_SIZE(HDRP(best_fit)))
                    best_fit = bp;

        return best_fit;
    #endif
}

static void place(void *bp, size_t asize) // place 함수는 데이터를 할당할 가용 블록의 bp와 배치 용량을 할당 받음
{
    size_t csize = GET_SIZE(HDRP(bp)); // 할당할 가용 블록의 전체 크기를 csize로 저장

    if((csize - asize) >= (2 * DSIZE)) { // 분할이 가능한 경우
        // 요청 용량만큼 블록을 배치하고 헤더와 풋터를 배치
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        // 남은 블록에 헤더와 풋터를 배치
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
    }
    else { // csize와 asize의 차이가 네 칸(16바이트)보다 작다면 해당 블록을 통째로 사용하고, 헤더와 풋터를 배치
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
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
