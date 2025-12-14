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
#define LIST_MAX 32                                     // 分离空闲链表的条数
#define FIRST_FIT_MAX_IDX 22                            // 采用首次适配策略的链表最大下标
#define BEST_FIT_SCAN_LIMIT 1024                        // 最佳适配策略的扫描块数上限
#define PREV_ALLOC 0x2                                  // 前块分配标志位

// 改写某个块头的 prev_alloc 位
#define SET_PREV_ALLOC_HDR(hdrp) PUT((hdrp), GET(hdrp) | PREV_ALLOC)
#define CLR_PREV_ALLOC_HDR(hdrp) PUT((hdrp), GET(hdrp) & ~PREV_ALLOC)

// 更新后继块的 prev_alloc位
#define SET_NEXT_PREV_ALLOC(bp) SET_PREV_ALLOC_HDR(HDRP(NEXT_BLKP(bp)))
#define CLR_NEXT_PREV_ALLOC(bp) CLR_PREV_ALLOC_HDR(HDRP(NEXT_BLKP(bp)))

// 从地址p处读出一个字(size_t)
#define GET(p) (*(size_t *)(p))
// 向地址p处写入一个字(size_t)
#define PUT(p, val) (*(size_t *)(p) = val)
// 从地址 p 处取出块大小(屏蔽低3位标志位)
#define GET_SIZE(p) (GET(p) & ~(size_t)0x7)
// 从地址 p 处取出分配标志(最低位)
#define GET_ALLOC(p) (GET(p) & 0x1)
// 获取前块分配标志位
#define GET_PREV_ALLOC(p) (GET(p) & PREV_ALLOC)

//  由块指针 bp(指向payload) 得到该块头部指针
#define HDRP(bp) ((char *)(bp) - WSIZE)
// 由当前块指针 bp 得到堆中下一块的块指针
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))

// 仅 free 块可用
#define FTRP_FREE(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
// 打包块头信息
#define PACK_HDR(size, alloc, prev_alloc) ((size) | (alloc) | ((prev_alloc) ? PREV_ALLOC : 0))
// 打包块脚信息
#define PACK_FTR(size) (size)

// 仅当前块 header 显示 prev 是 free 时可用
#define PREV_BLKP_FREE(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
// 返回空闲块 bp 中前驱指针字段的地址
#define PRED_PTR(bp) ((void **)(bp))
// 返回空闲块 bp 中后继指针字段的地址
#define SUCC_PTR(bp) ((void **)((char *)(bp) + PTRSIZE))

static char *heap_listp = NULL;     // 指向序言快 payload的指针
static void **seg_list_base = NULL; // 指向分离空闲链表头指针数组的起始地址

// 计算块大小对应的分离链表下标
static inline int list_index(size_t size);
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
    size_t bytes = ALIGN(LIST_MAX * PTRSIZE);
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
    PUT(heap_listp + 0, 0);                             // 对齐填充字
    PUT(heap_listp + 1 * WSIZE, PACK_HDR(DSIZE, 1, 1)); // 序言头：大小为 DSIZE，已分配
    PUT(heap_listp + 2 * WSIZE, PACK_FTR(DSIZE));       // 序言脚：同上
    PUT(heap_listp + 3 * WSIZE, PACK_HDR(0, 1, 1));     // 结尾块头：大小为 0，已分配

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
    int prev_alloc = GET_PREV_ALLOC(HDRP(ptr));

    // 当前块变空闲块,更新头脚部信息
    PUT(HDRP(ptr), PACK_HDR(size, 0, prev_alloc));
    PUT(FTRP_FREE(ptr), PACK_FTR(size));

    // 后继块看到前块是空闲块
    CLR_NEXT_PREV_ALLOC(ptr);

    // 立即尝试与前后空闲块合并
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 *
 * 缩小: 原地缩小,若剩余空间足够,拆分出新的空闲块并合并
 * 扩容: 优先尝试与后继空闲块合并实现原地扩容
 * 堆尾扩容:若后继为结尾块,先extend_heap,再尝试原地扩容
 * 最后再尝试 malloc + memcpy + free
 */
void *mm_realloc(void *ptr, size_t size)
{
    // ptr 为NULL,相当于malloc
    if (ptr == NULL)
    {
        return mm_malloc(size);
    }

    // size 为0,相当于free
    if (size == 0)
    {
        mm_free(ptr);
        return NULL;
    }

    // 旧块总大小(包含header/footer)
    size_t old_size = GET_SIZE(HDRP(ptr));

    // 新需求块总大小(对齐 + 头脚 + 最小块约束)
    size_t asize = adjust_block_size(size);

    // allocated 无footer,payload = old_size - header
    size_t old_payload = (old_size >= WSIZE) ? (old_size - WSIZE) : 0;

    // 原地缩小
    if (asize <= old_size)
    {
        size_t remain = old_size - asize;

        // 剩余空间够形成合法空闲块则拆分,否则不拆
        if (remain >= MIN_BLOCK_SIZE)
        {
            // 获取前块分配状态
            int prev_alloc = GET_PREV_ALLOC(HDRP(ptr));

            // 当前块缩成asize
            PUT(HDRP(ptr), PACK_HDR(asize, 1, prev_alloc));

            // 构造紧随其后的空闲块
            void *new_free = NEXT_BLKP(ptr);
            PUT(HDRP(new_free), PACK_HDR(remain, 0, 1));
            PUT(FTRP_FREE(new_free), PACK_FTR(remain));

            // 新空闲块可能与后继空闲块相邻,交给 coalesce 合并
            coalesce(new_free);
        }

        return ptr;
    }

    // 原地扩容,优先尝试与后继空闲块合并
    void *next = NEXT_BLKP(ptr);
    size_t next_size = GET_SIZE(HDRP(next));
    int next_alloc = GET_ALLOC(HDRP(next));

    if (!next_alloc)
    {
        size_t combined = old_size + next_size;

        if (combined >= asize)
        {
            // 将后继空闲块从分离链表中摘除
            remove_free_block(next);

            int prev_alloc = GET_PREV_ALLOC(HDRP(ptr));
            size_t remain = combined - asize;

            if (remain >= MIN_BLOCK_SIZE)
            {
                // 合并后可拆分出新的空闲块
                PUT(HDRP(ptr), PACK_HDR(asize, 1, prev_alloc));

                void *split = NEXT_BLKP(ptr);
                PUT(HDRP(split), PACK_HDR(remain, 0, 1));
                PUT(FTRP_FREE(split), PACK_FTR(remain));

                // 将其与可能的后继空闲块合并
                coalesce(split);
            }
            else
            {
                // 剩余空间太小,整块并入当前块
                PUT(HDRP(ptr), PACK_HDR(combined, 1, prev_alloc));
                SET_NEXT_PREV_ALLOC(ptr);
            }
            return ptr;
        }

        // next 空闲但不够,且next后面即为结尾块
        void *next_next = NEXT_BLKP(next);
        if (GET_SIZE(HDRP(next_next)) == 0 && GET_ALLOC(HDRP(next_next)) == 1)
        {
            size_t need_more = asize - combined;

            // 先摘掉 next
            remove_free_block(next);

            // 申请更多堆空间
            size_t words = (need_more + (WSIZE - 1)) / WSIZE;
            if (words < (MIN_BLOCK_SIZE / WSIZE))
            {
                words = MIN_BLOCK_SIZE / WSIZE;
            }

            if (extend_heap(words) != NULL)
            {
                // 扩展后,next后继为新空闲块
                void *new_next = NEXT_BLKP(ptr);
                size_t new_next_size = GET_SIZE(HDRP(new_next));

                // 将new_next从空闲链表摘除
                remove_free_block(new_next);

                size_t total = old_size + new_next_size;
                size_t remain = total - asize;
                int prev_alloc = GET_PREV_ALLOC(HDRP(ptr));

                if (remain >= MIN_BLOCK_SIZE)
                {
                    // 合并后可拆分出新的空闲块
                    PUT(HDRP(ptr), PACK_HDR(asize, 1, prev_alloc));

                    void *split = NEXT_BLKP(ptr);
                    PUT(HDRP(split), PACK_HDR(remain, 0, 1));
                    PUT(FTRP_FREE(split), PACK_FTR(remain));

                    coalesce(split);
                }
                else
                {
                    // 剩余空间太小,整块并入当前块
                    PUT(HDRP(ptr), PACK_HDR(total, 1, prev_alloc));
                    SET_NEXT_PREV_ALLOC(ptr);
                }
                return ptr;
            }
            else
            {
                // 扩展堆失败,恢复 next 状态
                insert_free_block(next);
            }
        }
    }

    // next 是 结尾块，扩堆后原地扩容
    if (next_size == 0 && next_alloc == 1)
    {
        size_t need_more = asize - old_size;
        size_t words = (need_more + (WSIZE - 1)) / WSIZE;
        if (words < (MIN_BLOCK_SIZE / WSIZE))
        {
            words = (MIN_BLOCK_SIZE / WSIZE);
        }

        if (extend_heap(words) != NULL)
        {
            void *new_next = NEXT_BLKP(ptr);

            if (!GET_ALLOC(HDRP(new_next)))
            {
                size_t new_next_size = GET_SIZE(HDRP(new_next));
                remove_free_block(new_next);

                size_t total = old_size + new_next_size;
                size_t remain = total - asize;
                int prev_alloc = GET_PREV_ALLOC(HDRP(ptr));

                if (remain >= MIN_BLOCK_SIZE)
                {
                    PUT(HDRP(ptr), PACK_HDR(asize, 1, prev_alloc));

                    void *split = NEXT_BLKP(ptr);
                    PUT(HDRP(split), PACK_HDR(remain, 0, 1));
                    PUT(FTRP_FREE(split), PACK_FTR(remain));

                    coalesce(split);
                }
                else
                {
                    PUT(HDRP(ptr), PACK_HDR(total, 1, prev_alloc));
                    SET_NEXT_PREV_ALLOC(ptr);
                }
                return ptr;
            }
        }
    }

    // prev 空闲，尝试向前扩容
    int curr_prev_alloc = GET_PREV_ALLOC(HDRP(ptr));
    if (!curr_prev_alloc)
    {
        void *prev = PREV_BLKP_FREE(ptr);
        size_t prev_size = GET_SIZE(HDRP(prev));

        // 先合并prev
        if (prev_size + old_size >= asize)
        {
            int prev_prev_alloc = GET_PREV_ALLOC(HDRP(prev));
            remove_free_block(prev);

            // 把ptr数据搬到prev
            size_t copy_bytes = old_payload;
            memmove(prev, ptr, copy_bytes);

            size_t total = prev_size + old_size;
            size_t remain = total - asize;

            if (remain >= MIN_BLOCK_SIZE)
            {
                PUT(HDRP(prev), PACK_HDR(asize, 1, prev_prev_alloc));

                void *split = NEXT_BLKP(prev);
                PUT(HDRP(split), PACK_HDR(remain, 0, 1));
                PUT(FTRP_FREE(split), PACK_FTR(remain));
                coalesce(split);
            }
            else
            {
                PUT(HDRP(prev), PACK_HDR(total, 1, prev_prev_alloc));
                SET_NEXT_PREV_ALLOC(prev);
            }
            return prev;
        }

        // 在尝试合并 prev + next
        if (!GET_ALLOC(HDRP(next)))
        {
            size_t total = prev_size + old_size + GET_SIZE(HDRP(next));

            if (total >= asize)
            {
                int prev_prev_alloc = GET_PREV_ALLOC(HDRP(prev));
                remove_free_block(prev);
                remove_free_block(next);

                // 把ptr数据搬到prev
                size_t copy_bytes = old_payload;
                memmove(prev, ptr, copy_bytes);

                size_t remain = total - asize;

                if (remain >= MIN_BLOCK_SIZE)
                {
                    PUT(HDRP(prev), PACK_HDR(asize, 1, prev_prev_alloc));

                    void *split = NEXT_BLKP(prev);
                    PUT(HDRP(split), PACK_HDR(remain, 0, 1));
                    PUT(FTRP_FREE(split), PACK_FTR(remain));
                    coalesce(split);
                }
                else
                {
                    PUT(HDRP(prev), PACK_HDR(total, 1, prev_prev_alloc));
                    SET_NEXT_PREV_ALLOC(prev);
                }
                return prev;
            }
        }
    }

    // 最后再尝试 malloc + memcpy + free
    void *new_ptr = mm_malloc(size);
    if (new_ptr == NULL)
    {
        return NULL;
    }

    size_t copy_size = (size < old_payload) ? size : old_payload;
    memcpy(new_ptr, ptr, copy_size);
    mm_free(ptr);

    return new_ptr;
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
    if (size == 0)
    {
        return 0; // 无效请求,后续直接返回 NULL
    }

    size_t asize = ALIGN(size + WSIZE); // 先加头部大小再对齐
    if (asize < MIN_BLOCK_SIZE)
    {
        // 对于很小的请求,直接返回最小块大小
        asize = MIN_BLOCK_SIZE;
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

    if (size < MIN_BLOCK_SIZE)
    {
        size = MIN_BLOCK_SIZE;
    }

    bp = mem_sbrk(size);
    if (bp == (void *)-1)
    {
        return NULL; // 扩展失败
    }

    // 获取前块的分配状态
    int prev_alloc = GET_PREV_ALLOC(HDRP(bp));

    // 初始化新空闲块的头部和脚部
    PUT(HDRP(bp), PACK_HDR(size, 0, prev_alloc)); // 新空闲块头部
    PUT(FTRP_FREE(bp), PACK_FTR(size));           // 新空闲块脚部

    // 初始化新的结尾块
    PUT(HDRP(NEXT_BLKP(bp)), PACK_HDR(0, 1, 0)); // 结尾块头,大小为0,已分配

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
    size_t size = GET_SIZE(HDRP(bp));

    int prev_alloc = GET_PREV_ALLOC(HDRP(bp));
    void *next = NEXT_BLKP(bp);
    int next_alloc = GET_ALLOC(HDRP(next));

    void *prev = NULL;
    int prev_prev_alloc = 1; // 前前块分配标志,默认为1

    // 只有当 prev_alloc 为0时,才有必要获取前块指针
    if (!prev_alloc)
    {
        prev = PREV_BLKP_FREE(bp);
        prev_prev_alloc = GET_PREV_ALLOC(HDRP(prev));
    }

    if (prev_alloc && next_alloc)
    {
        // 前后都已分配,不发生合并
    }
    else if (prev_alloc && !next_alloc)
    {
        // 前分配,后空闲,与后块合并
        remove_free_block(next);             // 将后块从空闲链表中摘除
        size += GET_SIZE(HDRP(next));        // 合并后大小
        PUT(HDRP(bp), PACK_HDR(size, 0, 1)); // 更新当前块头
        PUT(FTRP_FREE(bp), PACK_FTR(size));  // 更新当前块脚
    }
    else if (!prev_alloc && next_alloc)
    {
        // 前空闲,后分配,与前块合并
        remove_free_block(prev);      // 将前块从空闲链表中摘除
        size += GET_SIZE(HDRP(prev)); // 合并后大小

        bp = prev;                                         // 合并后的块起点为prev
        PUT(HDRP(bp), PACK_HDR(size, 0, prev_prev_alloc)); // 更新当前块头
        PUT(FTRP_FREE(bp), PACK_FTR(size));                // 更新当前块脚
    }
    else
    {
        // 前后都空闲,三块一起合并
        remove_free_block(prev);
        remove_free_block(next);
        size += GET_SIZE(HDRP(prev)) + GET_SIZE(HDRP(next));

        bp = prev;
        PUT(HDRP(bp), PACK_HDR(size, 0, prev_prev_alloc)); // 新头在 prev
        PUT(FTRP_FREE(bp), PACK_FTR(size));                // 新脚在next的脚部位置
    }

    // 合并后的块是空闲的,后继块 prev_alloc 位清0
    CLR_NEXT_PREV_ALLOC(bp);

    // 将合并后的空闲块插入分离链表
    insert_free_block(bp);
    return bp;
}

/*
 * find_fit - 在分离空闲链表中寻找一个大小不小于 asize 的空闲块
 *
 *策略:
 *   从 asize 对应的 size class 开始,依次向更大 size class 搜索
 *  使用 best-fit 策略
 */
static void *find_fit(size_t asize)
{
    int idx = list_index(asize);

    // 从当前 size class 开始往后找
    for (int i = idx; i < LIST_MAX; i++)
    {
        void *bp = seg_list_base[i];
        void *best_bp = NULL;
        size_t min_diff = (size_t)-1; // 初始化为最大值
        int count = 0;                // 记录扫描块数

        // Best-Fit 策略
        while (bp != NULL)
        {
            size_t curr_size = GET_SIZE(HDRP(bp));

            if (curr_size >= asize)
            {
                size_t diff = curr_size - asize;

                if (diff == 0)
                {
                    return bp; // 完美匹配,直接返回
                }

                if (diff < min_diff)
                {
                    // 找到更优的块
                    min_diff = diff;
                    best_bp = bp;
                }

                // 限制扫描块数,避免过度搜索
                count++;
                if (count >= BEST_FIT_SCAN_LIMIT)
                {
                    break;
                }
            }
            bp = *SUCC_PTR(bp); // 继续扫描下一个空闲块
        }
        if (best_bp != NULL)
        {
            return best_bp; // 返回找到的最佳块
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
 *       - 后半部分为新的空闲块,调用coalesce合并后插入空闲链表
 *   否则:
 *       - 整块都标记为已分配
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); // 获得当前空闲块的总大小
    size_t remain = csize - asize;     // 剩下的空间

    // 将该空闲块从空闲链表中删除
    remove_free_block(bp);

    int prev_alloc = GET_PREV_ALLOC(HDRP(bp)); // 获取前块分配状态

    if (remain >= MIN_BLOCK_SIZE)
    {
        // 可以分割
        // 前半部分: 已分配块
        PUT(HDRP(bp), PACK_HDR(asize, 1, prev_alloc));

        // 找到剩余部分的指针
        void *next = NEXT_BLKP(bp);

        // 后半部分: 新空闲块
        PUT(HDRP(next), PACK_HDR(remain, 0, 1));
        PUT(FTRP_FREE(next), PACK_FTR(remain));

        coalesce(next); // 与可能的后继空闲块合并
    }
    else
    {
        // 剩余空间不足以形成一个最小块,整块直接分配
        PUT(HDRP(bp), PACK_HDR(csize, 1, prev_alloc));

        // 后继块看到前块是已分配块
        SET_NEXT_PREV_ALLOC(bp);
    }
}

/*
 * list_index - 混合分桶策略
 *
 * 分桶规则 (LIST_MAX = 32):
 * [16, 128]    步长 8B   -> idx 0 ~ 14
 * (128, 256]   步长 16B  -> idx 15 ~ 22
 * > 256        阈值表    -> idx 23 ~ 31
 */
static inline int list_index(size_t size)
{
    if (size <= 16)
    {
        return 0;
    }

    // 16 ~ 128, 步长 8B
    if (size <= 128)
    {
        return (int)((size >> 3) - 2);
    }

    // 128 ~ 256, 步长 16B
    if (size <= 256)
    {
        return (int)(((size + 15) >> 4) + 6);
    }

    // > 256, 用阈值表映射到idx 23~31
    if (size > 256)
    {
        static const size_t limits[9] = {512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, (size_t)-1};

        for (int i = 0; i < 9; i++)
        {
            if (size <= limits[i])
            {
                return 23 + i;
            }
        }
    }

    return LIST_MAX - 1; // 超过最大限制,放到最后一个链表
}
