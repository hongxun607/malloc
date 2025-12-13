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
    "TJU",
    /* First member's full name */
    "Student",
    /* First member's email address */
    "student@tju.edu.cn",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8 // 定义8字节内存对齐

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7) // 将任意大小向上舍入到8的倍数

#define SIZE_T_SIZE (ALIGN(sizeof(size_t))) // 计算sizeof(size_t)的对齐后大小

#define WSIZE 4                                         // 定义字大小为4字节
#define DSIZE 8                                         // 定义双字大小为8字节
#define PTRSIZE (sizeof(void *))                        // 指针大小
#define CHUNKSIZE (1 << 12)                             // 定义初始堆大小为 4KB
#define MIN_BLOCK_SIZE (ALIGN(2 * WSIZE + 2 * PTRSIZE)) // 最小块大小
#define LIST_MAX 20                                     // 分离空闲链表的条数

// 将块大小 size 和分配标志 alloc 打包到一个字中
#define PACK(size, alloc) ((size) | (alloc))
// 从地址p处读出一个字(size_t)
#define GET(p) (*(size_t *)(p))
// 向地址p处写入一个字(size_t)
#define PUT(p, val) (*(size_t *)(p) = val)

// 从地址 p 处取出块大小(屏蔽低3位标志位)
#define GET_SIZE(p) (GET(p) & ~(size_t)0x7)
// 从地址 p 处取出分配标志(最低位)
#define GET_ALLOC(p) (GET(p) & 0x1)

//  由块指针 bp(指向payload) 得到该块头部指针
#define HDRP(bp) ((char *)(bp) - WSIZE)
// 由块指针 bp 得到该块脚部指针
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// 由当前块指针 bp 得到堆中下一块的块指针
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))
// 由当前块指针 bp 得到堆中上一块的块指针
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
// 返回空闲块 bp 中前驱指针字段的地址
#define PRED_PTR(bp) ((void **)(bp))
// 返回空闲块 bp 中后继指针字段的地址
#define SUCC_PTR(bp) ((void **)((char *)(bp) + PTRSIZE))

static char *heap_listp = NULL;     // 指向序言快 payload的指针
static void **seg_list_base = NULL; // 指向分离空闲链表头指针数组的起始地址

// 根据块大小 size 计算其对应的分离空闲链表下标
// 使用指数划分,块越大,下标越大,最大为LIST_MAX - 1
static int list_index(size_t size)
{
    int idx = 0;
    size_t s = size;

    while (idx < LIST_MAX - 1 && s > 1)
    {
        s >>= 1; // 不断除以2
        idx++;
    }

    return idx;
}

// 插入空闲块
static void insert_free_block(void *bp);
// 删除空闲块
static void remove_free_block(void *bp);
// 调整块大小
static size_t adjust_block_size(size_t size);

// 扩展堆空间
static void *extend_heap(size_t words);
// 合并空闲块
static void *coalesce(void *bp);
// 在分离空闲链表中寻找空闲块
static void *find_fit(size_t asize);
// 在空闲块中放置已分配块
static void place(void *bp, size_t asize);

/*
 * mm_init - initialize the malloc package.
 *
 * mm_init - 初始化内存分配器
 *
 * 步骤：
 *   在堆上为 LIST_MAX 个 void* 申请空间，作为“分离空闲链表头指针数组”；
 *   构造序言块和结尾块；
 *   调用 extend_heap 扩展一块初始空闲块。
 */
int mm_init(void)
{
    // 在堆上申请 LIST_MAX 个 void* 的空间,存放各链表的头指针
    size_t bytes = LIST_MAX * PTRSIZE;
    bytes = ALIGN(bytes); // 保证数组本身按8字节对齐

    void *p = mem_sbrk(bytes);

    if (p == (void *)-1)
    {
        return -1; // 申请失败
    }

    seg_list_base = (void **)p;

    // 初始化所有链表头为 NULL
    for (int i = 0; i < LIST_MAX; i++)
    {
        seg_list_base[i] = NULL;
    }

    // 再申请 4 个 word，用于：对齐填充字 + 序言头 + 序言脚 + 结尾头
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
    {
        return -1;
    }

    // 内存布局：[填充字][序言头][序言脚][结尾头]
    PUT(heap_listp + 0, 0);                      // 对齐填充字
    PUT(heap_listp + 1 * WSIZE, PACK(DSIZE, 1)); // 序言头：大小为 DSIZE，已分配
    PUT(heap_listp + 2 * WSIZE, PACK(DSIZE, 1)); // 序言脚：同上
    PUT(heap_listp + 3 * WSIZE, PACK(0, 1));     // 结尾块头：大小为 0，已分配

    // heap_listp 指向序言块 payload
    heap_listp += 2 * WSIZE;

    // 3. 扩展一块初始空闲块，大小为 CHUNKSIZE 字节
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
    {
        return -1;
    }

    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 * Always allocate a block whose size is a multiple of the alignment.
 *
 * mm_malloc - 分配 size 字节的内存块
 *
 * 返回：
 *   成功：指向新块 payload 的指针
 *   失败：NULL
 */
void *mm_malloc(size_t size)
{
    if (size == 0)
    {
        // 忽略 size 为0的无效请求
        return NULL;
    }

    // 计算包含头、脚并对其后的实际块大小
    size_t asize = adjust_block_size(size);

    // 在分离空闲链表中寻找合适的空闲块
    void *bp = find_fit(asize);
    if (bp != NULL)
    {
        place(bp, asize);
        return bp;
    }

    // 若找不到合适的空闲块,则需要扩展堆
    size_t extend_size = (asize > CHUNKSIZE) ? asize : CHUNKSIZE;
    bp = extend_heap(extend_size / WSIZE);
    if (bp == NULL)
    {
        return NULL; // 扩展失败
    }

    // 在新扩展的空闲块中放置 asize 大小的已分配块
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 * 释放之前通过 mm_malloc / mm_realloc 分配的块
 */
void mm_free(void *ptr)
{
    if (ptr == NULL)
    {
        // 释放空指针则什么都不做
        return;
    }

    size_t size = GET_SIZE(HDRP(ptr));

    // 将块头和块脚的 alloc 标志清零,标记为空闲
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));

    // 立即尝试与前后空闲块合并
    coalesce(ptr);
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
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

// 将空闲块 bp 插入对应 size class 的空闲链表表头
static void insert_free_block(void *bp)
{
    // 根据块大小确定所属链表下标
    size_t size = GET_SIZE(HDRP(bp));
    int idx = list_index(size);

    // 当前链表的表头
    void *head = seg_list_base[idx];

    // 头插法,bp成为新的表头
    *PRED_PTR(bp) = NULL; // 新头结点前驱为空
    *SUCC_PTR(bp) = head; // 新头结点后继为原来的头结点
    if (head != NULL)
    {
        *PRED_PTR(head) = bp; // 原表头若存在,其前驱更新为bp
    }

    seg_list_base[idx] = bp;
}

// 将空闲块 bp 从分离空闲链表中摘除
static void remove_free_block(void *bp)
{
    // 根据块大小确定所属链表下标
    size_t size = GET_SIZE(HDRP(bp));
    int idx = list_index(size);

    void *pred = *PRED_PTR(bp); // 前驱结点
    void *succ = *SUCC_PTR(bp); // 后继结点

    if (pred != NULL)
    {
        // bp 不是头结点,则前驱的后继指向 bp 的后继
        *SUCC_PTR(pred) = succ;
    }
    else
    {
        // bp 是头结点,更新链表的头指针
        seg_list_base[idx] = succ;
    }

    if (succ != NULL)
    {
        // 若存在后继,则更新后继的前驱为pred
        *PRED_PTR(succ) = pred;
    }
}

/*
 *根据用户请求的 size (payload大小)计算实际块大小asize
 *块大小包含:头部 + 脚部 + 有效载荷
 *至少为MIN_BLOCK_SIZE
 *使用 ALIGN 宏保证8字节对齐
 */
static size_t adjust_block_size(size_t size)
{
    size_t asize;
    if (size == 0)
    {
        return 0; // 无效请求,后续直接返回 NULL
    }

    if (size <= DSIZE)
    {
        // 对于很小的请求,直接返回最小块大小
        asize = MIN_BLOCK_SIZE;
    }
    else
    {
        // size + 头 + 脚,再用 ALIGN 对齐
        asize = ALIGN(size + 2 * WSIZE);
        if (asize < MIN_BLOCK_SIZE)
        {
            asize = MIN_BLOCK_SIZE;
        }
    }

    return asize;
}

/*
 * extend_heap - 通过 mem_sbrk 向内存系统中申请额外的堆空间
 *
 * 参数:
 *    words - 希望扩展的字数(一个word = 4 字节)
 *
 * 返回:
 *    成功: 指向新空闲块 payload 的指针
 *    失败: NULL
 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    // 为保证双字对齐,扩展的字数必须为偶数
    if (words % 2 == 0)
    {
        size = words * WSIZE;
    }
    else
    {
        size = (words + 1) * WSIZE;
    }

    bp = mem_sbrk(size);
    if (bp == (void *)-1)
    {
        return NULL; // 扩展失败
    }

    // 将获得的空间初始化为: 一个空闲块 + 一个新的结尾块
    PUT(HDRP(bp), PACK(size, 0)); // 新空闲块头部
    PUT(FTRP(bp), PACK(size, 0)); // 新空闲块脚部

    void *new_epilogue = NEXT_BLKP(bp);  // 新结尾块位置
    PUT(HDRP(new_epilogue), PACK(0, 1)); // 结尾块头,大小为0,已分配

    // 尝试与前块合并,并把合并结果插入空闲链表
    return coalesce(bp);
}

/*
 * coalesce - 合并与当前空闲块 bp 相邻的空闲块
 *
 * 返回:
 *    合并后的空闲块指针
 */
static void *coalesce(void *bp)
{
    void *prev = PREV_BLKP(bp); // bp 前一块
    void *next = NEXT_BLKP(bp); // bp 后一块

    int prev_alloc = GET_ALLOC(FTRP(prev)); // 前块是否已分配
    int next_alloc = GET_ALLOC(HDRP(next)); // 后块是否已分配
    size_t size = GET_SIZE(HDRP(bp));       // 当前块大小

    if (prev_alloc && next_alloc)
    {
        // 前后都已分配,不发生合并
        insert_free_block(bp);
    }
    else if (prev_alloc && !next_alloc)
    {
        // 前分配,后空闲,与后块合并
        remove_free_block(next);      // 将后块从空闲链表中摘除
        size += GET_SIZE(HDRP(next)); // 合并后大小
        PUT(HDRP(bp), PACK(size, 0)); // 更新当前块头
        PUT(FTRP(bp), PACK(size, 0)); // 更新当前块脚
        insert_free_block(bp);        // 插回空闲链表
    }
    else if (!prev_alloc && next_alloc)
    {
        // 前空闲,后分配,与前块合并
        remove_free_block(prev);        // 将前块从空闲链表中摘除
        size += GET_SIZE(HDRP(prev));   // 合并后大小
        PUT(HDRP(prev), PACK(size, 0)); // 更新当前块头
        PUT(FTRP(bp), PACK(size, 0));   // 更新当前块脚
        bp = prev;                      // 合并后的块起点为prev
        insert_free_block(bp);          // 插回空闲链表
    }
    else
    {
        // 前后都空闲,三块一起合并
        remove_free_block(prev);
        remove_free_block(next);

        size += GET_SIZE(HDRP(prev)) + GET_SIZE(HDRP(next));
        PUT(HDRP(prev), PACK(size, 0)); // 新头在 prev
        PUT(FTRP(next), PACK(size, 0)); // 新脚在next的脚部位置
        bp = prev;
        insert_free_block(bp);
    }

    return bp;
}

/*
 * find_fit - 在分离空闲链表中寻找一个大小不小于 asize 的空闲块
 *
 *策略:
 *   从 asize 对应的 size class 开始,依次向更大 size class 搜索
 *   在每条链表中使用 first-fit,找到第一个满足大小要求的块就返回
 */
static void *find_fit(size_t asize)
{
    int idx = list_index(asize);

    // 从对应 size class 开始,向更大的 class 逐个尝试
    for (int i = idx; i < LIST_MAX; i++)
    {
        void *bp = seg_list_base[i];
        for (; bp != NULL; bp = *SUCC_PTR(bp))
        {
            if (GET_SIZE(HDRP(bp)) >= asize)
            {
                return bp; // 找到适配块
            }
        }
    }

    // 所有链表都没有合适空闲块
    return NULL;
}

/*
 * place - 在空闲块 bp 中放置一个大小为asize的已分配块
 *
 * 逻辑：
 *   先把 bp 从空闲链表中摘除
 *   若 csize - asize 足够大(>= MIN_BLOCK_SIZE),则进行分割:
 *       - 前半部分为已分配块(大小为 asize);
 *       - 后半部分为新的空闲块插入分离链表
 *   否则:
 *       - 整块都标记为已分配
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); // 获得当前空闲块的总大小

    // 将该空闲块从空闲链表中删除
    remove_free_block(bp);

    if (csize - asize >= MIN_BLOCK_SIZE)
    {
        // 可以分割
        // 前半部分: 已分配块
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        // 后把部分: 新的空闲块
        void *next = (char *)bp + asize;
        PUT(HDRP(next), PACK(csize - asize, 0));
        PUT(FTRP(next), PACK(csize - asize, 0));

        insert_free_block(next); // 将剩余空闲块挂到分离链表
    }
    else
    {
        // 剩余空间不足以形成一个最小块,整块直接分配
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}