/**********************************************************************

  gc.c -

  $Author$
  created at: Tue Oct  5 09:44:46 JST 1993

  Copyright (C) 1993-2007 Yukihiro Matsumoto
  Copyright (C) 2000  Network Applied Communication Laboratory, Inc.
  Copyright (C) 2000  Information-technology Promotion Agency, Japan

**********************************************************************/

#define rb_data_object_alloc rb_data_object_alloc
#define rb_data_typed_object_alloc rb_data_typed_object_alloc

#include "ruby/internal/config.h"
#ifdef _WIN32
# include "ruby/ruby.h"
#endif

#include <signal.h>

#define sighandler_t ruby_sighandler_t

#ifndef _WIN32
#include <unistd.h>
#include <sys/mman.h>
#endif

#if defined(__wasm__) && !defined(__EMSCRIPTEN__)
# include "wasm/setjmp.h"
# include "wasm/machine.h"
#else
# include <setjmp.h>
#endif
#include <stdarg.h>
#include <stdio.h>

/* MALLOC_HEADERS_BEGIN */
#ifndef HAVE_MALLOC_USABLE_SIZE
# ifdef _WIN32
#  define HAVE_MALLOC_USABLE_SIZE
#  define malloc_usable_size(a) _msize(a)
# elif defined HAVE_MALLOC_SIZE
#  define HAVE_MALLOC_USABLE_SIZE
#  define malloc_usable_size(a) malloc_size(a)
# endif
#endif

#ifdef HAVE_MALLOC_USABLE_SIZE
# ifdef RUBY_ALTERNATIVE_MALLOC_HEADER
/* Alternative malloc header is included in ruby/missing.h */
# elif defined(HAVE_MALLOC_H)
#  include <malloc.h>
# elif defined(HAVE_MALLOC_NP_H)
#  include <malloc_np.h>
# elif defined(HAVE_MALLOC_MALLOC_H)
#  include <malloc/malloc.h>
# endif
#endif

#ifdef HAVE_MALLOC_TRIM
# include <malloc.h>

# ifdef __EMSCRIPTEN__
/* malloc_trim is defined in emscripten/emmalloc.h on emscripten. */
#  include <emscripten/emmalloc.h>
# endif
#endif

#if !defined(PAGE_SIZE) && defined(HAVE_SYS_USER_H)
/* LIST_HEAD conflicts with sys/queue.h on macOS */
# include <sys/user.h>
#endif
/* MALLOC_HEADERS_END */

#ifdef HAVE_SYS_TIME_H
# include <sys/time.h>
#endif

#ifdef HAVE_SYS_RESOURCE_H
# include <sys/resource.h>
#endif

#if defined _WIN32 || defined __CYGWIN__
# include <windows.h>
#elif defined(HAVE_POSIX_MEMALIGN)
#elif defined(HAVE_MEMALIGN)
# include <malloc.h>
#endif

#include <sys/types.h>

#ifdef __EMSCRIPTEN__
#include <emscripten.h>
#endif

#ifdef HAVE_MACH_TASK_EXCEPTION_PORTS
# include <mach/task.h>
# include <mach/mach_init.h>
# include <mach/mach_port.h>
#endif
#undef LIST_HEAD /* ccan/list conflicts with BSD-origin sys/queue.h. */

#include "constant.h"
#include "darray.h"
#include "debug_counter.h"
#include "eval_intern.h"
#include "id_table.h"
#include "internal.h"
#include "internal/class.h"
#include "internal/compile.h"
#include "internal/complex.h"
#include "internal/cont.h"
#include "internal/error.h"
#include "internal/eval.h"
#include "internal/gc.h"
#include "internal/hash.h"
#include "internal/imemo.h"
#include "internal/io.h"
#include "internal/numeric.h"
#include "internal/object.h"
#include "internal/proc.h"
#include "internal/rational.h"
#include "internal/sanitizers.h"
#include "internal/struct.h"
#include "internal/symbol.h"
#include "internal/thread.h"
#include "internal/variable.h"
#include "internal/warnings.h"
#include "rjit.h"
#include "probes.h"
#include "regint.h"
#include "ruby/debug.h"
#include "ruby/io.h"
#include "ruby/re.h"
#include "ruby/st.h"
#include "ruby/thread.h"
#include "ruby/util.h"
#include "ruby_assert.h"
#include "ruby_atomic.h"
#include "symbol.h"
#include "vm_core.h"
#include "vm_sync.h"
#include "vm_callinfo.h"
#include "ractor_core.h"

#include "builtin.h"
#include "shape.h"

#define rb_setjmp(env) RUBY_SETJMP(env)
#define rb_jmp_buf rb_jmpbuf_t
#undef rb_data_object_wrap

#if !defined(MAP_ANONYMOUS) && defined(MAP_ANON)
#define MAP_ANONYMOUS MAP_ANON
#endif


void *
print_for_debug(const char * msg)
{
    if (getenv("NULL_GC")) {
        fprintf(stderr, "NO-OP: %s\n", msg);
    }
    return 0;
}

static size_t malloc_offset = 0;
static size_t
gc_compute_malloc_offset(void)
{
    print_for_debug("gc_compute_malloc_offset");
    return 0;
}


size_t
rb_malloc_grow_capa(size_t current, size_t type_size)
{
    // required, segv otherwise
    size_t current_capacity = current;
    if (current_capacity < 4) {
        current_capacity = 4;
    }
    current_capacity *= type_size;

    // We double the current capacity.
    size_t new_capacity = (current_capacity * 2);

    // And round up to the next power of 2 if it's not already one.
    if (rb_popcount64(new_capacity) != 1) {
        new_capacity = (size_t)(1 << (64 - nlz_int64(new_capacity)));
    }

    new_capacity -= malloc_offset;
    new_capacity /= type_size;
    if (current > new_capacity) {
        rb_bug("rb_malloc_grow_capa: current_capacity=%zu, new_capacity=%zu, malloc_offset=%zu", current, new_capacity, malloc_offset);
    }
    RUBY_ASSERT(new_capacity > current);
    return new_capacity;
}

static inline struct rbimpl_size_mul_overflow_tag
size_add_overflow(size_t x, size_t y)
{
    size_t z;
    bool p;
#if 0

#elif __has_builtin(__builtin_add_overflow)
    p = __builtin_add_overflow(x, y, &z);

#elif defined(DSIZE_T)
    RB_GNUC_EXTENSION DSIZE_T dx = x;
    RB_GNUC_EXTENSION DSIZE_T dy = y;
    RB_GNUC_EXTENSION DSIZE_T dz = dx + dy;
    p = dz > SIZE_MAX;
    z = (size_t)dz;

#else
    z = x + y;
    p = z < y;

#endif
    return (struct rbimpl_size_mul_overflow_tag) { p, z, };
}

static inline struct rbimpl_size_mul_overflow_tag
size_mul_add_overflow(size_t x, size_t y, size_t z) /* x * y + z */
{
    struct rbimpl_size_mul_overflow_tag t = rbimpl_size_mul_overflow(x, y);
    struct rbimpl_size_mul_overflow_tag u = size_add_overflow(t.right, z);
    return (struct rbimpl_size_mul_overflow_tag) { t.left || u.left, u.right };
}

static inline struct rbimpl_size_mul_overflow_tag
size_mul_add_mul_overflow(size_t x, size_t y, size_t z, size_t w) /* x * y + z * w */
{
    struct rbimpl_size_mul_overflow_tag t = rbimpl_size_mul_overflow(x, y);
    struct rbimpl_size_mul_overflow_tag u = rbimpl_size_mul_overflow(z, w);
    struct rbimpl_size_mul_overflow_tag v = size_add_overflow(t.right, u.right);
    return (struct rbimpl_size_mul_overflow_tag) { t.left || u.left || v.left, v.right };
}

PRINTF_ARGS(NORETURN(static void gc_raise(VALUE, const char*, ...)), 2, 3);

static inline size_t
size_mul_or_raise(size_t x, size_t y, VALUE exc)
{
    struct rbimpl_size_mul_overflow_tag t = rbimpl_size_mul_overflow(x, y);
    if (LIKELY(!t.left)) {
        return t.right;
    }
    else if (rb_during_gc()) {
        rb_memerror();          /* or...? */
    }
    else {
        gc_raise(
            exc,
            "integer overflow: %"PRIuSIZE
            " * %"PRIuSIZE
            " > %"PRIuSIZE,
            x, y, (size_t)SIZE_MAX);
    }
}

size_t
rb_size_mul_or_raise(size_t x, size_t y, VALUE exc)
{
    return size_mul_or_raise(x, y, exc);
}

static inline size_t
size_mul_add_or_raise(size_t x, size_t y, size_t z, VALUE exc)
{
    struct rbimpl_size_mul_overflow_tag t = size_mul_add_overflow(x, y, z);
    if (LIKELY(!t.left)) {
        return t.right;
    }
    else if (rb_during_gc()) {
        rb_memerror();          /* or...? */
    }
    else {
        gc_raise(
            exc,
            "integer overflow: %"PRIuSIZE
            " * %"PRIuSIZE
            " + %"PRIuSIZE
            " > %"PRIuSIZE,
            x, y, z, (size_t)SIZE_MAX);
    }
}

size_t
rb_size_mul_add_or_raise(size_t x, size_t y, size_t z, VALUE exc)
{
    return size_mul_add_or_raise(x, y, z, exc);
}

static inline size_t
size_mul_add_mul_or_raise(size_t x, size_t y, size_t z, size_t w, VALUE exc)
{
    struct rbimpl_size_mul_overflow_tag t = size_mul_add_mul_overflow(x, y, z, w);
    if (LIKELY(!t.left)) {
        return t.right;
    }
    else if (rb_during_gc()) {
        rb_memerror();          /* or...? */
    }
    else {
        gc_raise(
            exc,
            "integer overflow: %"PRIdSIZE
            " * %"PRIdSIZE
            " + %"PRIdSIZE
            " * %"PRIdSIZE
            " > %"PRIdSIZE,
            x, y, z, w, (size_t)SIZE_MAX);
    }
}

#if defined(HAVE_RB_GC_GUARDED_PTR_VAL) && HAVE_RB_GC_GUARDED_PTR_VAL
/* trick the compiler into thinking a external signal handler uses this */
volatile VALUE rb_gc_guarded_val;
volatile VALUE *
rb_gc_guarded_ptr_val(volatile VALUE *ptr, VALUE val)
{
    print_for_debug(__func__);
    return 0;
}
#endif

#ifndef GC_HEAP_INIT_SLOTS
#define GC_HEAP_INIT_SLOTS 10000
#endif
#ifndef GC_HEAP_FREE_SLOTS
#define GC_HEAP_FREE_SLOTS  4096
#endif
#ifndef GC_HEAP_GROWTH_FACTOR
#define GC_HEAP_GROWTH_FACTOR 1.8
#endif
#ifndef GC_HEAP_GROWTH_MAX_SLOTS
#define GC_HEAP_GROWTH_MAX_SLOTS 0 /* 0 is disable */
#endif
#ifndef GC_HEAP_REMEMBERED_WB_UNPROTECTED_OBJECTS_LIMIT_RATIO
# define GC_HEAP_REMEMBERED_WB_UNPROTECTED_OBJECTS_LIMIT_RATIO 0.01
#endif
#ifndef GC_HEAP_OLDOBJECT_LIMIT_FACTOR
#define GC_HEAP_OLDOBJECT_LIMIT_FACTOR 2.0
#endif

#ifndef GC_HEAP_FREE_SLOTS_MIN_RATIO
#define GC_HEAP_FREE_SLOTS_MIN_RATIO  0.20
#endif
#ifndef GC_HEAP_FREE_SLOTS_GOAL_RATIO
#define GC_HEAP_FREE_SLOTS_GOAL_RATIO 0.40
#endif
#ifndef GC_HEAP_FREE_SLOTS_MAX_RATIO
#define GC_HEAP_FREE_SLOTS_MAX_RATIO  0.65
#endif

#ifndef GC_MALLOC_LIMIT_MIN
#define GC_MALLOC_LIMIT_MIN (16 * 1024 * 1024 /* 16MB */)
#endif
#ifndef GC_MALLOC_LIMIT_MAX
#define GC_MALLOC_LIMIT_MAX (32 * 1024 * 1024 /* 32MB */)
#endif
#ifndef GC_MALLOC_LIMIT_GROWTH_FACTOR
#define GC_MALLOC_LIMIT_GROWTH_FACTOR 1.4
#endif

#ifndef GC_OLDMALLOC_LIMIT_MIN
#define GC_OLDMALLOC_LIMIT_MIN (16 * 1024 * 1024 /* 16MB */)
#endif
#ifndef GC_OLDMALLOC_LIMIT_GROWTH_FACTOR
#define GC_OLDMALLOC_LIMIT_GROWTH_FACTOR 1.2
#endif
#ifndef GC_OLDMALLOC_LIMIT_MAX
#define GC_OLDMALLOC_LIMIT_MAX (128 * 1024 * 1024 /* 128MB */)
#endif

#ifndef GC_CAN_COMPILE_COMPACTION
#if defined(__wasi__) /* WebAssembly doesn't support signals */
# define GC_CAN_COMPILE_COMPACTION 0
#else
# define GC_CAN_COMPILE_COMPACTION 1
#endif
#endif

#ifndef PRINT_MEASURE_LINE
#define PRINT_MEASURE_LINE 0
#endif
#ifndef PRINT_ENTER_EXIT_TICK
#define PRINT_ENTER_EXIT_TICK 0
#endif
#ifndef PRINT_ROOT_TICKS
#define PRINT_ROOT_TICKS 0
#endif

#define USE_TICK_T                 (PRINT_ENTER_EXIT_TICK || PRINT_MEASURE_LINE || PRINT_ROOT_TICKS)
#define TICK_TYPE 1

typedef struct {
    size_t size_pool_init_slots[SIZE_POOL_COUNT];
    size_t heap_free_slots;
    double growth_factor;
    size_t growth_max_slots;

    double heap_free_slots_min_ratio;
    double heap_free_slots_goal_ratio;
    double heap_free_slots_max_ratio;
    double uncollectible_wb_unprotected_objects_limit_ratio;
    double oldobject_limit_factor;

    size_t malloc_limit_min;
    size_t malloc_limit_max;
    double malloc_limit_growth_factor;

    size_t oldmalloc_limit_min;
    size_t oldmalloc_limit_max;
    double oldmalloc_limit_growth_factor;

    VALUE gc_stress;
} ruby_gc_params_t;

static ruby_gc_params_t gc_params = {
    { 0 },
    GC_HEAP_FREE_SLOTS,
    GC_HEAP_GROWTH_FACTOR,
    GC_HEAP_GROWTH_MAX_SLOTS,

    GC_HEAP_FREE_SLOTS_MIN_RATIO,
    GC_HEAP_FREE_SLOTS_GOAL_RATIO,
    GC_HEAP_FREE_SLOTS_MAX_RATIO,
    GC_HEAP_REMEMBERED_WB_UNPROTECTED_OBJECTS_LIMIT_RATIO,
    GC_HEAP_OLDOBJECT_LIMIT_FACTOR,

    GC_MALLOC_LIMIT_MIN,
    GC_MALLOC_LIMIT_MAX,
    GC_MALLOC_LIMIT_GROWTH_FACTOR,

    GC_OLDMALLOC_LIMIT_MIN,
    GC_OLDMALLOC_LIMIT_MAX,
    GC_OLDMALLOC_LIMIT_GROWTH_FACTOR,

    FALSE,
};

/* GC_DEBUG:
 *  enable to embed GC debugging information.
 */
#ifndef GC_DEBUG
#define GC_DEBUG 0
#endif

/* RGENGC_DEBUG:
 * 1: basic information
 * 2: remember set operation
 * 3: mark
 * 4:
 * 5: sweep
 */
#ifndef RGENGC_DEBUG
#ifdef RUBY_DEVEL
#define RGENGC_DEBUG       -1
#else
#define RGENGC_DEBUG       0
#endif
#endif
#if RGENGC_DEBUG < 0 && !defined(_MSC_VER)
# define RGENGC_DEBUG_ENABLED(level) (-(RGENGC_DEBUG) >= (level) && ruby_rgengc_debug >= (level))
#elif defined(HAVE_VA_ARGS_MACRO)
# define RGENGC_DEBUG_ENABLED(level) ((RGENGC_DEBUG) >= (level))
#else
# define RGENGC_DEBUG_ENABLED(level) 0
#endif
int ruby_rgengc_debug;

/* RGENGC_CHECK_MODE
 * 0: disable all assertions
 * 1: enable assertions (to debug RGenGC)
 * 2: enable internal consistency check at each GC (for debugging)
 * 3: enable internal consistency check at each GC steps (for debugging)
 * 4: enable liveness check
 * 5: show all references
 */
#ifndef RGENGC_CHECK_MODE
#define RGENGC_CHECK_MODE  0
#endif

// Note: using RUBY_ASSERT_WHEN() extend a macro in expr (info by nobu).
#define GC_ASSERT(expr) RUBY_ASSERT_MESG_WHEN(RGENGC_CHECK_MODE > 0, expr, #expr)

/* RGENGC_PROFILE
 * 0: disable RGenGC profiling
 * 1: enable profiling for basic information
 * 2: enable profiling for each types
 */
#ifndef RGENGC_PROFILE
#define RGENGC_PROFILE     0
#endif

/* RGENGC_ESTIMATE_OLDMALLOC
 * Enable/disable to estimate increase size of malloc'ed size by old objects.
 * If estimation exceeds threshold, then will invoke full GC.
 * 0: disable estimation.
 * 1: enable estimation.
 */
#ifndef RGENGC_ESTIMATE_OLDMALLOC
#define RGENGC_ESTIMATE_OLDMALLOC 1
#endif

/* RGENGC_FORCE_MAJOR_GC
 * Force major/full GC if this macro is not 0.
 */
#ifndef RGENGC_FORCE_MAJOR_GC
#define RGENGC_FORCE_MAJOR_GC 0
#endif

#ifndef GC_PROFILE_MORE_DETAIL
#define GC_PROFILE_MORE_DETAIL 0
#endif
#ifndef GC_PROFILE_DETAIL_MEMORY
#define GC_PROFILE_DETAIL_MEMORY 0
#endif
#ifndef GC_ENABLE_LAZY_SWEEP
#define GC_ENABLE_LAZY_SWEEP   1
#endif
#ifndef CALC_EXACT_MALLOC_SIZE
#define CALC_EXACT_MALLOC_SIZE USE_GC_MALLOC_OBJ_INFO_DETAILS
#endif
#if defined(HAVE_MALLOC_USABLE_SIZE) || CALC_EXACT_MALLOC_SIZE > 0
#ifndef MALLOC_ALLOCATED_SIZE
#define MALLOC_ALLOCATED_SIZE 0
#endif
#else
#define MALLOC_ALLOCATED_SIZE 0
#endif
#ifndef MALLOC_ALLOCATED_SIZE_CHECK
#define MALLOC_ALLOCATED_SIZE_CHECK 0
#endif

#ifndef GC_DEBUG_STRESS_TO_CLASS
#define GC_DEBUG_STRESS_TO_CLASS RUBY_DEBUG
#endif

#ifndef RGENGC_OBJ_INFO
#define RGENGC_OBJ_INFO (RGENGC_DEBUG | RGENGC_CHECK_MODE)
#endif

typedef enum {
    GPR_FLAG_NONE               = 0x000,
    /* major reason */
    GPR_FLAG_MAJOR_BY_NOFREE    = 0x001,
    GPR_FLAG_MAJOR_BY_OLDGEN    = 0x002,
    GPR_FLAG_MAJOR_BY_SHADY     = 0x004,
    GPR_FLAG_MAJOR_BY_FORCE     = 0x008,
#if RGENGC_ESTIMATE_OLDMALLOC
    GPR_FLAG_MAJOR_BY_OLDMALLOC = 0x020,
#endif
    GPR_FLAG_MAJOR_MASK         = 0x0ff,

    /* gc reason */
    GPR_FLAG_NEWOBJ             = 0x100,
    GPR_FLAG_MALLOC             = 0x200,
    GPR_FLAG_METHOD             = 0x400,
    GPR_FLAG_CAPI               = 0x800,
    GPR_FLAG_STRESS            = 0x1000,

    /* others */
    GPR_FLAG_IMMEDIATE_SWEEP   = 0x2000,
    GPR_FLAG_HAVE_FINALIZE     = 0x4000,
    GPR_FLAG_IMMEDIATE_MARK    = 0x8000,
    GPR_FLAG_FULL_MARK        = 0x10000,
    GPR_FLAG_COMPACT          = 0x20000,

    GPR_DEFAULT_REASON =
        (GPR_FLAG_FULL_MARK | GPR_FLAG_IMMEDIATE_MARK |
         GPR_FLAG_IMMEDIATE_SWEEP | GPR_FLAG_CAPI),
} gc_profile_record_flag;

typedef struct gc_profile_record {
    unsigned int flags;

    double gc_time;
    double gc_invoke_time;

    size_t heap_total_objects;
    size_t heap_use_size;
    size_t heap_total_size;
    size_t moved_objects;

#if GC_PROFILE_MORE_DETAIL
    double gc_mark_time;
    double gc_sweep_time;

    size_t heap_use_pages;
    size_t heap_live_objects;
    size_t heap_free_objects;

    size_t allocate_increase;
    size_t allocate_limit;

    double prepare_time;
    size_t removing_objects;
    size_t empty_objects;
#if GC_PROFILE_DETAIL_MEMORY
    long maxrss;
    long minflt;
    long majflt;
#endif
#endif
#if MALLOC_ALLOCATED_SIZE
    size_t allocated_size;
#endif

#if RGENGC_PROFILE > 0
    size_t old_objects;
    size_t remembered_normal_objects;
    size_t remembered_shady_objects;
#endif
} gc_profile_record;

struct RMoved {
    VALUE flags;
    VALUE dummy;
    VALUE destination;
    shape_id_t original_shape_id;
};

#define RMOVED(obj) ((struct RMoved *)(obj))

typedef struct RVALUE {
    union {
        struct {
            VALUE flags;		/* always 0 for freed obj */
            struct RVALUE *next;
        } free;
        struct RMoved  moved;
        struct RBasic  basic;
        struct RObject object;
        struct RClass  klass;
        struct RFloat  flonum;
        struct RString string;
        struct RArray  array;
        struct RRegexp regexp;
        struct RHash   hash;
        struct RData   data;
        struct RTypedData   typeddata;
        struct RStruct rstruct;
        struct RBignum bignum;
        struct RFile   file;
        struct RMatch  match;
        struct RRational rational;
        struct RComplex complex;
        struct RSymbol symbol;
        union {
            rb_cref_t cref;
            struct vm_svar svar;
            struct vm_throw_data throw_data;
            struct vm_ifunc ifunc;
            struct MEMO memo;
            struct rb_method_entry_struct ment;
            const rb_iseq_t iseq;
            rb_env_t env;
            struct rb_imemo_tmpbuf_struct alloc;
            rb_ast_t ast;
        } imemo;
        struct {
            struct RBasic basic;
            VALUE v1;
            VALUE v2;
            VALUE v3;
        } values;
    } as;

    /* Start of RVALUE_OVERHEAD.
     * Do not directly read these members from the RVALUE as they're located
     * at the end of the slot (which may differ in size depending on the size
     * pool). */
#if RACTOR_CHECK_MODE
    uint32_t _ractor_belonging_id;
#endif
#if GC_DEBUG
    const char *file;
    int line;
#endif
} RVALUE;

#if RACTOR_CHECK_MODE
# define RVALUE_OVERHEAD (sizeof(RVALUE) - offsetof(RVALUE, _ractor_belonging_id))
#elif GC_DEBUG
# define RVALUE_OVERHEAD (sizeof(RVALUE) - offsetof(RVALUE, file))
#else
# define RVALUE_OVERHEAD 0
#endif

STATIC_ASSERT(sizeof_rvalue, sizeof(RVALUE) == (SIZEOF_VALUE * 5) + RVALUE_OVERHEAD);
STATIC_ASSERT(alignof_rvalue, RUBY_ALIGNOF(RVALUE) == SIZEOF_VALUE);

typedef uintptr_t bits_t;
enum {
    BITS_SIZE = sizeof(bits_t),
    BITS_BITLENGTH = ( BITS_SIZE * CHAR_BIT )
};
#define popcount_bits rb_popcount_intptr

struct heap_page_header {
    struct heap_page *page;
};

struct heap_page_body {
    struct heap_page_header header;
    /* char gap[];      */
    /* RVALUE values[]; */
};

#define STACK_CHUNK_SIZE 500

typedef struct stack_chunk {
    VALUE data[STACK_CHUNK_SIZE];
    struct stack_chunk *next;
} stack_chunk_t;

typedef struct mark_stack {
    stack_chunk_t *chunk;
    stack_chunk_t *cache;
    int index;
    int limit;
    size_t cache_size;
    size_t unused_cache_size;
} mark_stack_t;

#define SIZE_POOL_EDEN_HEAP(size_pool) (&(size_pool)->eden_heap)
#define SIZE_POOL_TOMB_HEAP(size_pool) (&(size_pool)->tomb_heap)

typedef int (*gc_compact_compare_func)(const void *l, const void *r, void *d);

typedef struct rb_heap_struct {
    struct heap_page *free_pages;
    struct ccan_list_head pages;
    struct heap_page *sweeping_page; /* iterator for .pages */
    struct heap_page *compact_cursor;
    uintptr_t compact_cursor_index;
    struct heap_page *pooled_pages;
    size_t total_pages;      /* total page count in a heap */
    size_t total_slots;      /* total slot count (about total_pages * HEAP_PAGE_OBJ_LIMIT) */
} rb_heap_t;

typedef struct rb_size_pool_struct {
    short slot_size;

    size_t allocatable_pages;

    /* Basic statistics */
    size_t total_allocated_pages;
    size_t total_freed_pages;
    size_t force_major_gc_count;
    size_t force_incremental_marking_finish_count;
    size_t total_allocated_objects;
    size_t total_freed_objects;

    /* Sweeping statistics */
    size_t freed_slots;
    size_t empty_slots;

    rb_heap_t eden_heap;
    rb_heap_t tomb_heap;
} rb_size_pool_t;

enum gc_mode {
    gc_mode_none,
    gc_mode_marking,
    gc_mode_sweeping,
    gc_mode_compacting,
};

typedef struct rb_objspace {
    struct {
        size_t limit;
        size_t increase;
#if MALLOC_ALLOCATED_SIZE
        size_t allocated_size;
        size_t allocations;
#endif

    } malloc_params;

    struct {
        unsigned int mode : 2;
        unsigned int immediate_sweep : 1;
        unsigned int dont_gc : 1;
        unsigned int dont_incremental : 1;
        unsigned int during_gc : 1;
        unsigned int during_compacting : 1;
        unsigned int during_reference_updating : 1;
        unsigned int gc_stressful: 1;
        unsigned int has_newobj_hook: 1;
        unsigned int during_minor_gc : 1;
        unsigned int during_incremental_marking : 1;
        unsigned int measure_gc : 1;
    } flags;

    rb_event_flag_t hook_events;
    VALUE next_object_id;

    rb_size_pool_t size_pools[SIZE_POOL_COUNT];

    struct {
        rb_atomic_t finalizing;
    } atomic_flags;

    mark_stack_t mark_stack;
    size_t marked_slots;

    struct {
        struct heap_page **sorted;
        size_t allocated_pages;
        size_t allocatable_pages;
        size_t sorted_length;
        uintptr_t range[2];
        size_t freeable_pages;

        /* final */
        size_t final_slots;
        VALUE deferred_final;
    } heap_pages;

    st_table *finalizer_table;

    struct {
        int run;
        unsigned int latest_gc_info;
        gc_profile_record *records;
        gc_profile_record *current_record;
        size_t next_index;
        size_t size;

#if GC_PROFILE_MORE_DETAIL
        double prepare_time;
#endif
        double invoke_time;

        size_t minor_gc_count;
        size_t major_gc_count;
        size_t compact_count;
        size_t read_barrier_faults;
#if RGENGC_PROFILE > 0
        size_t total_generated_normal_object_count;
        size_t total_generated_shady_object_count;
        size_t total_shade_operation_count;
        size_t total_promoted_count;
        size_t total_remembered_normal_object_count;
        size_t total_remembered_shady_object_count;

#if RGENGC_PROFILE >= 2
        size_t generated_normal_object_count_types[RUBY_T_MASK];
        size_t generated_shady_object_count_types[RUBY_T_MASK];
        size_t shade_operation_count_types[RUBY_T_MASK];
        size_t promoted_types[RUBY_T_MASK];
        size_t remembered_normal_object_count_types[RUBY_T_MASK];
        size_t remembered_shady_object_count_types[RUBY_T_MASK];
#endif
#endif /* RGENGC_PROFILE */

        /* temporary profiling space */
        double gc_sweep_start_time;
        size_t total_allocated_objects_at_gc_start;
        size_t heap_used_at_gc_start;

        /* basic statistics */
        size_t count;
        uint64_t marking_time_ns;
        struct timespec marking_start_time;
        uint64_t sweeping_time_ns;
        struct timespec sweeping_start_time;

        /* Weak references */
        size_t weak_references_count;
        size_t retained_weak_references_count;
    } profile;

    VALUE gc_stress_mode;

    struct {
        VALUE parent_object;
        int need_major_gc;
        size_t last_major_gc;
        size_t uncollectible_wb_unprotected_objects;
        size_t uncollectible_wb_unprotected_objects_limit;
        size_t old_objects;
        size_t old_objects_limit;

#if RGENGC_ESTIMATE_OLDMALLOC
        size_t oldmalloc_increase;
        size_t oldmalloc_increase_limit;
#endif

#if RGENGC_CHECK_MODE >= 2
        struct st_table *allrefs_table;
        size_t error_count;
#endif
    } rgengc;

    struct {
        size_t considered_count_table[T_MASK];
        size_t moved_count_table[T_MASK];
        size_t moved_up_count_table[T_MASK];
        size_t moved_down_count_table[T_MASK];
        size_t total_moved;

        /* This function will be used, if set, to sort the heap prior to compaction */
        gc_compact_compare_func compare_func;
    } rcompactor;

    struct {
        size_t pooled_slots;
        size_t step_slots;
    } rincgc;

    st_table *id_to_obj_tbl;
    st_table *obj_to_id_tbl;

#if GC_DEBUG_STRESS_TO_CLASS
    VALUE stress_to_class;
#endif

    rb_darray(VALUE *) weak_references;
    rb_postponed_job_handle_t finalize_deferred_pjob;

#ifdef RUBY_ASAN_ENABLED
    rb_execution_context_t *marking_machine_context_ec;
#endif

} rb_objspace_t;


#ifndef HEAP_PAGE_ALIGN_LOG
/* default tiny heap size: 64KiB */
#define HEAP_PAGE_ALIGN_LOG 16
#endif

#define BASE_SLOT_SIZE sizeof(RVALUE)

#define CEILDIV(i, mod) roomof(i, mod)
enum {
    HEAP_PAGE_ALIGN = (1UL << HEAP_PAGE_ALIGN_LOG),
    HEAP_PAGE_ALIGN_MASK = (~(~0UL << HEAP_PAGE_ALIGN_LOG)),
    HEAP_PAGE_SIZE = HEAP_PAGE_ALIGN,
    HEAP_PAGE_OBJ_LIMIT = (unsigned int)((HEAP_PAGE_SIZE - sizeof(struct heap_page_header)) / BASE_SLOT_SIZE),
    HEAP_PAGE_BITMAP_LIMIT = CEILDIV(CEILDIV(HEAP_PAGE_SIZE, BASE_SLOT_SIZE), BITS_BITLENGTH),
    HEAP_PAGE_BITMAP_SIZE = (BITS_SIZE * HEAP_PAGE_BITMAP_LIMIT),
};
#define HEAP_PAGE_ALIGN (1 << HEAP_PAGE_ALIGN_LOG)
#define HEAP_PAGE_SIZE HEAP_PAGE_ALIGN

#if !defined(INCREMENTAL_MARK_STEP_ALLOCATIONS)
# define INCREMENTAL_MARK_STEP_ALLOCATIONS 500
#endif

#undef INIT_HEAP_PAGE_ALLOC_USE_MMAP
/* Must define either HEAP_PAGE_ALLOC_USE_MMAP or
 * INIT_HEAP_PAGE_ALLOC_USE_MMAP. */

#ifndef HAVE_MMAP
/* We can't use mmap of course, if it is not available. */
static const bool HEAP_PAGE_ALLOC_USE_MMAP = false;

#elif defined(__wasm__)
/* wasmtime does not have proper support for mmap.
 * See https://github.com/bytecodealliance/wasmtime/blob/main/docs/WASI-rationale.md#why-no-mmap-and-friends
 */
static const bool HEAP_PAGE_ALLOC_USE_MMAP = false;

#elif HAVE_CONST_PAGE_SIZE
/* If we have the PAGE_SIZE and it is a constant, then we can directly use it. */
static const bool HEAP_PAGE_ALLOC_USE_MMAP = (PAGE_SIZE <= HEAP_PAGE_SIZE);

#elif defined(PAGE_MAX_SIZE) && (PAGE_MAX_SIZE <= HEAP_PAGE_SIZE)
/* If we can use the maximum page size. */
static const bool HEAP_PAGE_ALLOC_USE_MMAP = true;

#elif defined(PAGE_SIZE)
/* If the PAGE_SIZE macro can be used dynamically. */
# define INIT_HEAP_PAGE_ALLOC_USE_MMAP (PAGE_SIZE <= HEAP_PAGE_SIZE)

#elif defined(HAVE_SYSCONF) && defined(_SC_PAGE_SIZE)
/* If we can use sysconf to determine the page size. */
# define INIT_HEAP_PAGE_ALLOC_USE_MMAP (sysconf(_SC_PAGE_SIZE) <= HEAP_PAGE_SIZE)

#else
/* Otherwise we can't determine the system page size, so don't use mmap. */
static const bool HEAP_PAGE_ALLOC_USE_MMAP = false;
#endif

#ifdef INIT_HEAP_PAGE_ALLOC_USE_MMAP
/* We can determine the system page size at runtime. */
# define HEAP_PAGE_ALLOC_USE_MMAP (heap_page_alloc_use_mmap != false)

static bool heap_page_alloc_use_mmap;
#endif

#define RVALUE_AGE_BIT_COUNT 2
#define RVALUE_AGE_BIT_MASK (((bits_t)1 << RVALUE_AGE_BIT_COUNT) - 1)

struct heap_page {
    short slot_size;
    short total_slots;
    short free_slots;
    short final_slots;
    short pinned_slots;
    struct {
        unsigned int before_sweep : 1;
        unsigned int has_remembered_objects : 1;
        unsigned int has_uncollectible_wb_unprotected_objects : 1;
        unsigned int in_tomb : 1;
    } flags;

    rb_size_pool_t *size_pool;

    struct heap_page *free_next;
    uintptr_t start;
    RVALUE *freelist;
    struct ccan_list_node page_node;

    bits_t wb_unprotected_bits[HEAP_PAGE_BITMAP_LIMIT];
    /* the following three bitmaps are cleared at the beginning of full GC */
    bits_t mark_bits[HEAP_PAGE_BITMAP_LIMIT];
    bits_t uncollectible_bits[HEAP_PAGE_BITMAP_LIMIT];
    bits_t marking_bits[HEAP_PAGE_BITMAP_LIMIT];

    bits_t remembered_bits[HEAP_PAGE_BITMAP_LIMIT];

    /* If set, the object is not movable */
    bits_t pinned_bits[HEAP_PAGE_BITMAP_LIMIT];
    bits_t age_bits[HEAP_PAGE_BITMAP_LIMIT * RVALUE_AGE_BIT_COUNT];
};

/*
 * When asan is enabled, this will prohibit writing to the freelist until it is unlocked
 */
static void
asan_lock_freelist(struct heap_page *page)
{
    print_for_debug("asan_lock_freelist");
}

/*
 * When asan is enabled, this will enable the ability to write to the freelist
 */
static void
asan_unlock_freelist(struct heap_page *page)
{
    print_for_debug("asan_unlock_freelist");
}

#define GET_PAGE_BODY(x)   ((struct heap_page_body *)((bits_t)(x) & ~(HEAP_PAGE_ALIGN_MASK)))
#define GET_PAGE_HEADER(x) (&GET_PAGE_BODY(x)->header)
#define GET_HEAP_PAGE(x)   (GET_PAGE_HEADER(x)->page)

#define NUM_IN_PAGE(p)   (((bits_t)(p) & HEAP_PAGE_ALIGN_MASK) / BASE_SLOT_SIZE)
#define BITMAP_INDEX(p)  (NUM_IN_PAGE(p) / BITS_BITLENGTH )
#define BITMAP_OFFSET(p) (NUM_IN_PAGE(p) & (BITS_BITLENGTH-1))
#define BITMAP_BIT(p)    ((bits_t)1 << BITMAP_OFFSET(p))

/* Bitmap Operations */
#define MARKED_IN_BITMAP(bits, p)    ((bits)[BITMAP_INDEX(p)] & BITMAP_BIT(p))
#define MARK_IN_BITMAP(bits, p)      ((bits)[BITMAP_INDEX(p)] = (bits)[BITMAP_INDEX(p)] | BITMAP_BIT(p))
#define CLEAR_IN_BITMAP(bits, p)     ((bits)[BITMAP_INDEX(p)] = (bits)[BITMAP_INDEX(p)] & ~BITMAP_BIT(p))

/* getting bitmap */
#define GET_HEAP_MARK_BITS(x)           (&GET_HEAP_PAGE(x)->mark_bits[0])
#define GET_HEAP_PINNED_BITS(x)         (&GET_HEAP_PAGE(x)->pinned_bits[0])
#define GET_HEAP_UNCOLLECTIBLE_BITS(x)  (&GET_HEAP_PAGE(x)->uncollectible_bits[0])
#define GET_HEAP_WB_UNPROTECTED_BITS(x) (&GET_HEAP_PAGE(x)->wb_unprotected_bits[0])
#define GET_HEAP_MARKING_BITS(x)        (&GET_HEAP_PAGE(x)->marking_bits[0])

#define GC_SWEEP_PAGES_FREEABLE_PER_STEP 3

#define RVALUE_AGE_BITMAP_INDEX(n)  (NUM_IN_PAGE(n) / (BITS_BITLENGTH / RVALUE_AGE_BIT_COUNT))
#define RVALUE_AGE_BITMAP_OFFSET(n) ((NUM_IN_PAGE(n) % (BITS_BITLENGTH / RVALUE_AGE_BIT_COUNT)) * RVALUE_AGE_BIT_COUNT)

#define RVALUE_OLD_AGE   3

static int
RVALUE_AGE_GET(VALUE obj)
{
    print_for_debug("RVALUE_AGE_GET");
    return 0;
}

static void
RVALUE_AGE_SET(VALUE obj, int age)
{
    print_for_debug("RVALUE_AGE_SET");
}

/* Aliases */
#define rb_objspace (*rb_objspace_of(GET_VM()))
#define rb_objspace_of(vm) ((vm)->objspace)
#define unless_objspace(objspace) \
    rb_objspace_t *objspace; \
    rb_vm_t *unless_objspace_vm = GET_VM(); \
    if (unless_objspace_vm) objspace = unless_objspace_vm->objspace; \
    else /* return; or objspace will be warned uninitialized */

#define ruby_initial_gc_stress	gc_params.gc_stress

VALUE *ruby_initial_gc_stress_ptr = &ruby_initial_gc_stress;

#define malloc_limit		objspace->malloc_params.limit
#define malloc_increase 	objspace->malloc_params.increase
#define malloc_allocated_size 	objspace->malloc_params.allocated_size
#define heap_pages_sorted       objspace->heap_pages.sorted
#define heap_allocated_pages    objspace->heap_pages.allocated_pages
#define heap_pages_sorted_length objspace->heap_pages.sorted_length
#define heap_pages_lomem	objspace->heap_pages.range[0]
#define heap_pages_himem	objspace->heap_pages.range[1]
#define heap_pages_freeable_pages	objspace->heap_pages.freeable_pages
#define heap_pages_final_slots		objspace->heap_pages.final_slots
#define heap_pages_deferred_final	objspace->heap_pages.deferred_final
#define size_pools              objspace->size_pools
#define during_gc		objspace->flags.during_gc
#define finalizing		objspace->atomic_flags.finalizing
#define finalizer_table 	objspace->finalizer_table
#define ruby_gc_stressful	objspace->flags.gc_stressful
#define ruby_gc_stress_mode     objspace->gc_stress_mode
#if GC_DEBUG_STRESS_TO_CLASS
#define stress_to_class         objspace->stress_to_class
#define set_stress_to_class(c)  (stress_to_class = (c))
#else
#define stress_to_class         (objspace, 0)
#define set_stress_to_class(c)  (objspace, (c))
#endif

#if 0
#define dont_gc_on()          (fprintf(stderr, "dont_gc_on@%s:%d\n",      __FILE__, __LINE__), objspace->flags.dont_gc = 1)
#define dont_gc_off()         (fprintf(stderr, "dont_gc_off@%s:%d\n",     __FILE__, __LINE__), objspace->flags.dont_gc = 0)
#define dont_gc_set(b)        (fprintf(stderr, "dont_gc_set(%d)@%s:%d\n", __FILE__, __LINE__), (int)b), objspace->flags.dont_gc = (b))
#define dont_gc_val()         (objspace->flags.dont_gc)
#else
#define dont_gc_on()          (objspace->flags.dont_gc = 1)
#define dont_gc_off()         (objspace->flags.dont_gc = 0)
#define dont_gc_set(b)        (((int)b), objspace->flags.dont_gc = (b))
#define dont_gc_val()         (objspace->flags.dont_gc)
#endif

static inline enum gc_mode
gc_mode_verify(enum gc_mode mode)
{
    print_for_debug("gc_mode_verify");
    return mode;
}

static inline bool
has_sweeping_pages(rb_objspace_t *objspace)
{
    // required segv otherwise
    for (int i = 0; i < SIZE_POOL_COUNT; i++) {
        if (SIZE_POOL_EDEN_HEAP(&size_pools[i])->sweeping_page) {
            return TRUE;
        }
    }
    return FALSE;
}

static inline size_t
heap_eden_total_pages(rb_objspace_t *objspace)
{
    // required, segv otherwise
    size_t count = 0;
    for (int i = 0; i < SIZE_POOL_COUNT; i++) {
        count += SIZE_POOL_EDEN_HEAP(&size_pools[i])->total_pages;
    }
    return count;
}

static inline size_t
heap_eden_total_slots(rb_objspace_t *objspace)
{
    // required, segv otherwise
    size_t count = 0;
    for (int i = 0; i < SIZE_POOL_COUNT; i++) {
        count += SIZE_POOL_EDEN_HEAP(&size_pools[i])->total_slots;
    }
    return count;
}

static inline size_t
heap_tomb_total_pages(rb_objspace_t *objspace)
{
    print_for_debug("heap_tomb_total_pages");
    return 0;
}

static inline size_t
heap_allocatable_pages(rb_objspace_t *objspace)
{
    // required, segv otherwise
    size_t count = 0;
    for (int i = 0; i < SIZE_POOL_COUNT; i++) {
        count += size_pools[i].allocatable_pages;
    }
    return count;
}

static inline size_t
heap_allocatable_slots(rb_objspace_t *objspace)
{
    print_for_debug("heap_allocatable_slots");
    return 0;
}


static inline size_t
total_allocated_objects(rb_objspace_t *objspace)
{
    print_for_debug("total_allocated_objects");
    return 0;
}

static inline size_t
total_freed_objects(rb_objspace_t *objspace)
{
    print_for_debug("total_freed_objects");
    return 0;
}

#define gc_mode(objspace)                gc_mode_verify((enum gc_mode)(objspace)->flags.mode)
#define gc_mode_set(objspace, m)         ((objspace)->flags.mode = (unsigned int)gc_mode_verify(m))

#define is_marking(objspace)             (gc_mode(objspace) == gc_mode_marking)
#define is_sweeping(objspace)            (gc_mode(objspace) == gc_mode_sweeping)
#define is_full_marking(objspace)        ((objspace)->flags.during_minor_gc == FALSE)
#define is_incremental_marking(objspace) ((objspace)->flags.during_incremental_marking != FALSE)
#define will_be_incremental_marking(objspace) ((objspace)->rgengc.need_major_gc != GPR_FLAG_NONE)
#define GC_INCREMENTAL_SWEEP_SLOT_COUNT 2048
#define GC_INCREMENTAL_SWEEP_POOL_SLOT_COUNT 1024
#define is_lazy_sweeping(objspace)           (GC_ENABLE_LAZY_SWEEP && has_sweeping_pages(objspace))

#if SIZEOF_LONG == SIZEOF_VOIDP
# define obj_id_to_ref(objid) ((objid) ^ FIXNUM_FLAG) /* unset FIXNUM_FLAG */
#elif SIZEOF_LONG_LONG == SIZEOF_VOIDP
# define obj_id_to_ref(objid) (FIXNUM_P(objid) ? \
   ((objid) ^ FIXNUM_FLAG) : (NUM2PTR(objid) << 1))
#else
# error not supported
#endif

#define RANY(o) ((RVALUE*)(o))

struct RZombie {
    struct RBasic basic;
    VALUE next;
    void (*dfree)(void *);
    void *data;
};

#define RZOMBIE(o) ((struct RZombie *)(o))

#define nomem_error GET_VM()->special_exceptions[ruby_error_nomemory]

#if RUBY_MARK_FREE_DEBUG
int ruby_gc_debug_indent = 0;
#endif
VALUE rb_mGC;
int ruby_disable_gc = 0;
int ruby_enable_autocompact = 0;
#if RGENGC_CHECK_MODE
gc_compact_compare_func ruby_autocompact_compare_func;
#endif

void rb_vm_update_references(void *ptr);

void rb_gcdebug_print_obj_condition(VALUE obj);

NORETURN(static void gc_raise(VALUE exc, const char *fmt, ...));

static void init_mark_stack(mark_stack_t *stack);
static int garbage_collect(rb_objspace_t *, unsigned int reason);

static int  gc_start(rb_objspace_t *objspace, unsigned int reason);
static void gc_rest(rb_objspace_t *objspace);

enum gc_enter_event {
    gc_enter_event_start,
    gc_enter_event_continue,
    gc_enter_event_rest,
    gc_enter_event_finalizer,
    gc_enter_event_rb_memerror,
};

static inline void gc_enter(rb_objspace_t *objspace, enum gc_enter_event event, unsigned int *lock_lev);
static inline void gc_exit(rb_objspace_t *objspace, enum gc_enter_event event, unsigned int *lock_lev);
static void gc_marking_enter(rb_objspace_t *objspace);
static void gc_marking_exit(rb_objspace_t *objspace);
static void gc_sweeping_enter(rb_objspace_t *objspace);
static void gc_sweeping_exit(rb_objspace_t *objspace);

static void gc_sweep(rb_objspace_t *objspace);
static void gc_sweep_finish_size_pool(rb_objspace_t *objspace, rb_size_pool_t *size_pool);

static inline void gc_mark(rb_objspace_t *objspace, VALUE ptr);
static inline void gc_pin(rb_objspace_t *objspace, VALUE ptr);
static inline void gc_mark_and_pin(rb_objspace_t *objspace, VALUE ptr);
NO_SANITIZE("memory", static void gc_mark_maybe(rb_objspace_t *objspace, VALUE ptr));

static int gc_mark_stacked_objects_incremental(rb_objspace_t *, size_t count);
NO_SANITIZE("memory", static inline int is_pointer_to_heap(rb_objspace_t *objspace, const void *ptr));

static size_t obj_memsize_of(VALUE obj, int use_all_types);
static void gc_verify_internal_consistency(rb_objspace_t *objspace);

static double getrusage_time(void);
static inline void gc_prof_setup_new_record(rb_objspace_t *objspace, unsigned int reason);
static inline void gc_prof_timer_start(rb_objspace_t *);
static inline void gc_prof_timer_stop(rb_objspace_t *);
static inline void gc_prof_mark_timer_start(rb_objspace_t *);
static inline void gc_prof_mark_timer_stop(rb_objspace_t *);
static inline void gc_prof_sweep_timer_start(rb_objspace_t *);
static inline void gc_prof_sweep_timer_stop(rb_objspace_t *);
static inline void gc_prof_set_malloc_info(rb_objspace_t *);
static inline void gc_prof_set_heap_info(rb_objspace_t *);

#define TYPED_UPDATE_IF_MOVED(_objspace, _type, _thing) do { \
    if (gc_object_moved_p((_objspace), (VALUE)(_thing))) {    \
        *(_type *)&(_thing) = (_type)RMOVED(_thing)->destination; \
    } \
} while (0)

#define UPDATE_IF_MOVED(_objspace, _thing) TYPED_UPDATE_IF_MOVED(_objspace, VALUE, _thing)

#define gc_prof_record(objspace) (objspace)->profile.current_record
#define gc_prof_enabled(objspace) ((objspace)->profile.run && (objspace)->profile.current_record)

#ifdef HAVE_VA_ARGS_MACRO
# define gc_report(level, objspace, ...) \
    if (!RGENGC_DEBUG_ENABLED(level)) {} else gc_report_body(level, objspace, __VA_ARGS__)
#else
# define gc_report if (!RGENGC_DEBUG_ENABLED(0)) {} else gc_report_body
#endif
PRINTF_ARGS(static void gc_report_body(int level, rb_objspace_t *objspace, const char *fmt, ...), 3, 4);
static const char *obj_info(VALUE obj);
static const char *obj_info_basic(VALUE obj);

static void gc_finalize_deferred(void *dmy);

/*
 * 1 - TSC (H/W Time Stamp Counter)
 * 2 - getrusage
 */
#ifndef TICK_TYPE
#define TICK_TYPE 1
#endif

#if USE_TICK_T

#if TICK_TYPE == 1
/* the following code is only for internal tuning. */

/* Source code to use RDTSC is quoted and modified from
 * https://www.mcs.anl.gov/~kazutomo/rdtsc.html
 * written by Kazutomo Yoshii <kazutomo@mcs.anl.gov>
 */

#if defined(__GNUC__) && defined(__i386__)
typedef unsigned long long tick_t;
#define PRItick "llu"
static inline tick_t
tick(void)
{
    unsigned long long int x;
    __asm__ __volatile__ ("rdtsc" : "=A" (x));
    return x;
}

#elif defined(__GNUC__) && defined(__x86_64__)
typedef unsigned long long tick_t;
#define PRItick "llu"

static __inline__ tick_t
tick(void)
{
    unsigned long hi, lo;
    __asm__ __volatile__ ("rdtsc" : "=a"(lo), "=d"(hi));
    return ((unsigned long long)lo)|( ((unsigned long long)hi)<<32);
}

#elif defined(__powerpc64__) && (GCC_VERSION_SINCE(4,8,0) || defined(__clang__))
typedef unsigned long long tick_t;
#define PRItick "llu"

static __inline__ tick_t
tick(void)
{
    unsigned long long val = __builtin_ppc_get_timebase();
    return val;
}

/* Implementation for macOS PPC by @nobu
 * See: https://github.com/ruby/ruby/pull/5975#discussion_r890045558
 */
#elif defined(__POWERPC__) && defined(__APPLE__)
typedef unsigned long long tick_t;
#define PRItick "llu"

static __inline__ tick_t
tick(void)
{
    unsigned long int upper, lower, tmp;
    # define mftbu(r) __asm__ volatile("mftbu   %0" : "=r"(r))
    # define mftb(r)  __asm__ volatile("mftb    %0" : "=r"(r))
        do {
            mftbu(upper);
            mftb(lower);
            mftbu(tmp);
        } while (tmp != upper);
    return ((tick_t)upper << 32) | lower;
}

#elif defined(__aarch64__) &&  defined(__GNUC__)
typedef unsigned long tick_t;
#define PRItick "lu"

static __inline__ tick_t
tick(void)
{
    unsigned long val;
    __asm__ __volatile__ ("mrs %0, cntvct_el0" : "=r" (val));
    return val;
}


#elif defined(_WIN32) && defined(_MSC_VER)
#include <intrin.h>
typedef unsigned __int64 tick_t;
#define PRItick "llu"

static inline tick_t
tick(void)
{
    return __rdtsc();
}

#else /* use clock */
typedef clock_t tick_t;
#define PRItick "llu"

static inline tick_t
tick(void)
{
    return clock();
}
#endif /* TSC */

#elif TICK_TYPE == 2
typedef double tick_t;
#define PRItick "4.9f"

static inline tick_t
tick(void)
{
    return getrusage_time();
}
#else /* TICK_TYPE */
#error "choose tick type"
#endif /* TICK_TYPE */

#define MEASURE_LINE(expr) do { \
    volatile tick_t start_time = tick(); \
    volatile tick_t end_time; \
    expr; \
    end_time = tick(); \
    fprintf(stderr, "0\t%"PRItick"\t%s\n", end_time - start_time, #expr); \
} while (0)

#else /* USE_TICK_T */
#define MEASURE_LINE(expr) expr
#endif /* USE_TICK_T */

#define asan_unpoisoning_object(obj) \
    for (void *poisoned = asan_unpoison_object_temporary(obj), \
              *unpoisoning = &poisoned; /* flag to loop just once */ \
         unpoisoning; \
         unpoisoning = asan_poison_object_restore(obj, poisoned))

#define FL_CHECK2(name, x, pred) \
    ((RGENGC_CHECK_MODE && SPECIAL_CONST_P(x)) ? \
     (rb_bug(name": SPECIAL_CONST (%p)", (void *)(x)), 0) : (pred))
#define FL_TEST2(x,f)  FL_CHECK2("FL_TEST2",  x, FL_TEST_RAW((x),(f)) != 0)
#define FL_SET2(x,f)   FL_CHECK2("FL_SET2",   x, RBASIC(x)->flags |= (f))
#define FL_UNSET2(x,f) FL_CHECK2("FL_UNSET2", x, RBASIC(x)->flags &= ~(f))

#define RVALUE_MARK_BITMAP(obj)           MARKED_IN_BITMAP(GET_HEAP_MARK_BITS(obj), (obj))
#define RVALUE_PIN_BITMAP(obj)            MARKED_IN_BITMAP(GET_HEAP_PINNED_BITS(obj), (obj))
#define RVALUE_PAGE_MARKED(page, obj)     MARKED_IN_BITMAP((page)->mark_bits, (obj))

#define RVALUE_WB_UNPROTECTED_BITMAP(obj) MARKED_IN_BITMAP(GET_HEAP_WB_UNPROTECTED_BITS(obj), (obj))
#define RVALUE_UNCOLLECTIBLE_BITMAP(obj)  MARKED_IN_BITMAP(GET_HEAP_UNCOLLECTIBLE_BITS(obj), (obj))
#define RVALUE_MARKING_BITMAP(obj)        MARKED_IN_BITMAP(GET_HEAP_MARKING_BITS(obj), (obj))

#define RVALUE_PAGE_WB_UNPROTECTED(page, obj) MARKED_IN_BITMAP((page)->wb_unprotected_bits, (obj))
#define RVALUE_PAGE_UNCOLLECTIBLE(page, obj)  MARKED_IN_BITMAP((page)->uncollectible_bits, (obj))
#define RVALUE_PAGE_MARKING(page, obj)        MARKED_IN_BITMAP((page)->marking_bits, (obj))

static int rgengc_remember(rb_objspace_t *objspace, VALUE obj);
static void rgengc_mark_and_rememberset_clear(rb_objspace_t *objspace, rb_heap_t *heap);
static void rgengc_rememberset_mark(rb_objspace_t *objspace, rb_heap_t *heap);

static int
check_rvalue_consistency_force(const VALUE obj, int terminate)
{
    print_for_debug("check_rvalue_consistency_force");
    return 0;
}

static inline VALUE
check_rvalue_consistency(const VALUE obj)
{
    print_for_debug("check_rvalue_consistency");
    return 0;
}

static inline int
gc_object_moved_p(rb_objspace_t * objspace, VALUE obj)
{
    print_for_debug("gc_object_moved_p");
    return 0;
}

// rvalues seem kind of important, compilation can hang if
// these are gutted (at least the first one, i skipped the rest.
static inline int
RVALUE_MARKED(VALUE obj)
{
    check_rvalue_consistency(obj);
    return RVALUE_MARK_BITMAP(obj) != 0;
}

static inline int
RVALUE_WB_UNPROTECTED(VALUE obj)
{
    check_rvalue_consistency(obj);
    return RVALUE_WB_UNPROTECTED_BITMAP(obj) != 0;
}

static inline int
RVALUE_MARKING(VALUE obj)
{
    check_rvalue_consistency(obj);
    return RVALUE_MARKING_BITMAP(obj) != 0;
}

static inline int
RVALUE_REMEMBERED(VALUE obj)
{
    check_rvalue_consistency(obj);
    return MARKED_IN_BITMAP(GET_HEAP_PAGE(obj)->remembered_bits, obj) != 0;
}

static inline int
RVALUE_UNCOLLECTIBLE(VALUE obj)
{
    check_rvalue_consistency(obj);
    return RVALUE_UNCOLLECTIBLE_BITMAP(obj) != 0;
}

static inline int
RVALUE_OLD_P(VALUE obj)
{
    GC_ASSERT(!RB_SPECIAL_CONST_P(obj));
    check_rvalue_consistency(obj);
    // Because this will only ever be called on GC controlled objects,
    // we can use the faster _RAW function here
    return RB_OBJ_PROMOTED_RAW(obj);
}

static inline void
RVALUE_PAGE_OLD_UNCOLLECTIBLE_SET(rb_objspace_t *objspace, struct heap_page *page, VALUE obj)
{
    MARK_IN_BITMAP(&page->uncollectible_bits[0], obj);
    objspace->rgengc.old_objects++;

#if RGENGC_PROFILE >= 2
    objspace->profile.total_promoted_count++;
    objspace->profile.promoted_types[BUILTIN_TYPE(obj)]++;
#endif
}

static inline void
RVALUE_OLD_UNCOLLECTIBLE_SET(rb_objspace_t *objspace, VALUE obj)
{
    RB_DEBUG_COUNTER_INC(obj_promote);
    RVALUE_PAGE_OLD_UNCOLLECTIBLE_SET(objspace, GET_HEAP_PAGE(obj), obj);
}

/* set age to age+1 */
static inline void
RVALUE_AGE_INC(rb_objspace_t *objspace, VALUE obj)
{
    int age = RVALUE_AGE_GET((VALUE)obj);

    if (RGENGC_CHECK_MODE && age == RVALUE_OLD_AGE) {
        rb_bug("RVALUE_AGE_INC: can not increment age of OLD object %s.", obj_info(obj));
    }

    age++;
    RVALUE_AGE_SET(obj, age);

    if (age == RVALUE_OLD_AGE) {
        RVALUE_OLD_UNCOLLECTIBLE_SET(objspace, obj);
    }

    check_rvalue_consistency(obj);
}

static inline void
RVALUE_AGE_SET_CANDIDATE(rb_objspace_t *objspace, VALUE obj)
{
    check_rvalue_consistency(obj);
    GC_ASSERT(!RVALUE_OLD_P(obj));
    RVALUE_AGE_SET(obj, RVALUE_OLD_AGE - 1);
    check_rvalue_consistency(obj);
}

static inline void
RVALUE_AGE_RESET(VALUE obj)
{
    RVALUE_AGE_SET(obj, 0);
}

static inline void
RVALUE_DEMOTE(rb_objspace_t *objspace, VALUE obj)
{
    check_rvalue_consistency(obj);
    GC_ASSERT(RVALUE_OLD_P(obj));

    if (!is_incremental_marking(objspace) && RVALUE_REMEMBERED(obj)) {
        CLEAR_IN_BITMAP(GET_HEAP_PAGE(obj)->remembered_bits, obj);
    }

    CLEAR_IN_BITMAP(GET_HEAP_UNCOLLECTIBLE_BITS(obj), obj);
    RVALUE_AGE_RESET(obj);

    if (RVALUE_MARKED(obj)) {
        objspace->rgengc.old_objects--;
    }

    check_rvalue_consistency(obj);
}

static inline int
RVALUE_BLACK_P(VALUE obj)
{
    return RVALUE_MARKED(obj) && !RVALUE_MARKING(obj);
}

#if 0
static inline int
RVALUE_GREY_P(VALUE obj)
{
    return RVALUE_MARKED(obj) && RVALUE_MARKING(obj);
}
#endif

static inline int
RVALUE_WHITE_P(VALUE obj)
{
    return RVALUE_MARKED(obj) == FALSE;
}

/*
  --------------------------- ObjectSpace -----------------------------
*/

static inline void *
calloc1(size_t n)
{
    // required, segv otherwise
    return calloc(1, n);
}

rb_objspace_t *
rb_objspace_alloc(void)
{
    // required, segv otherwise
    rb_objspace_t *objspace = calloc1(sizeof(rb_objspace_t));
    objspace->flags.measure_gc = 1;
    malloc_limit = gc_params.malloc_limit_min;
    objspace->finalize_deferred_pjob = rb_postponed_job_preregister(0, gc_finalize_deferred, objspace);
    if (objspace->finalize_deferred_pjob == POSTPONED_JOB_HANDLE_INVALID) {
        rb_bug("Could not preregister postponed job for GC");
    }

    for (int i = 0; i < SIZE_POOL_COUNT; i++) {
        rb_size_pool_t *size_pool = &size_pools[i];

        size_pool->slot_size = (1 << i) * BASE_SLOT_SIZE;

        ccan_list_head_init(&SIZE_POOL_EDEN_HEAP(size_pool)->pages);
        ccan_list_head_init(&SIZE_POOL_TOMB_HEAP(size_pool)->pages);
    }

    rb_darray_make_without_gc(&objspace->weak_references, 0);

    dont_gc_on();

    return objspace;
}

void
rb_objspace_free(rb_objspace_t *objspace)
{
    print_for_debug("rb_objspace_free");
}

static void
heap_pages_expand_sorted_to(rb_objspace_t *objspace, size_t next_length)
{
    // required, assertion fails
    struct heap_page **sorted;
    size_t size = size_mul_or_raise(next_length, sizeof(struct heap_page *), rb_eRuntimeError);

    gc_report(3, objspace, "heap_pages_expand_sorted: next_length: %"PRIdSIZE", size: %"PRIdSIZE"\n",
              next_length, size);

    if (heap_pages_sorted_length > 0) {
        sorted = (struct heap_page **)realloc(heap_pages_sorted, size);
        if (sorted) heap_pages_sorted = sorted;
    }
    else {
        sorted = heap_pages_sorted = (struct heap_page **)malloc(size);
    }

    if (sorted == 0) {
        rb_memerror();
    }

    heap_pages_sorted_length = next_length;
}

static void
heap_pages_expand_sorted(rb_objspace_t *objspace)
{
    //required, assertion fails
    /* usually heap_allocatable_pages + heap_eden->total_pages == heap_pages_sorted_length
     * because heap_allocatable_pages contains heap_tomb->total_pages (recycle heap_tomb pages).
     * however, if there are pages which do not have empty slots, then try to create new pages
     * so that the additional allocatable_pages counts (heap_tomb->total_pages) are added.
     */
    size_t next_length = heap_allocatable_pages(objspace);
    for (int i = 0; i < SIZE_POOL_COUNT; i++) {
        rb_size_pool_t *size_pool = &size_pools[i];
        next_length += SIZE_POOL_EDEN_HEAP(size_pool)->total_pages;
        next_length += SIZE_POOL_TOMB_HEAP(size_pool)->total_pages;
    }

    if (next_length > heap_pages_sorted_length) {
        heap_pages_expand_sorted_to(objspace, next_length);
    }

    GC_ASSERT(heap_allocatable_pages(objspace) + heap_eden_total_pages(objspace) <= heap_pages_sorted_length);
    GC_ASSERT(heap_allocated_pages <= heap_pages_sorted_length);
}

static void
size_pool_allocatable_pages_set(rb_objspace_t *objspace, rb_size_pool_t *size_pool, size_t s)
{
    // required, segv otherwise
    size_pool->allocatable_pages = s;
    heap_pages_expand_sorted(objspace);
}

static inline void
heap_page_add_freeobj(rb_objspace_t *objspace, struct heap_page *page, VALUE obj)
{
    // required
    ASSERT_vm_locking();

    RVALUE *p = (RVALUE *)obj;

    asan_unpoison_object(obj, false);

    asan_unlock_freelist(page);

    p->as.free.flags = 0;
    p->as.free.next = page->freelist;
    page->freelist = p;
    asan_lock_freelist(page);

    RVALUE_AGE_RESET(obj);

    if (RGENGC_CHECK_MODE &&
        /* obj should belong to page */
        !(page->start <= (uintptr_t)obj &&
          (uintptr_t)obj   <  ((uintptr_t)page->start + (page->total_slots * page->slot_size)) &&
          obj % BASE_SLOT_SIZE == 0)) {
        rb_bug("heap_page_add_freeobj: %p is not rvalue.", (void *)p);
    }

    asan_poison_object(obj);
    gc_report(3, objspace, "heap_page_add_freeobj: add %p to freelist\n", (void *)obj);
}

static inline void
heap_add_freepage(rb_heap_t *heap, struct heap_page *page)
{
    // required
    asan_unlock_freelist(page);
    GC_ASSERT(page->free_slots != 0);
    GC_ASSERT(page->freelist != NULL);

    page->free_next = heap->free_pages;
    heap->free_pages = page;

    RUBY_DEBUG_LOG("page:%p freelist:%p", (void *)page, (void *)page->freelist);

    asan_lock_freelist(page);
}

static inline void
heap_add_poolpage(rb_objspace_t *objspace, rb_heap_t *heap, struct heap_page *page)
{
    // required
    asan_unlock_freelist(page);
    GC_ASSERT(page->free_slots != 0);
    GC_ASSERT(page->freelist != NULL);

    page->free_next = heap->pooled_pages;
    heap->pooled_pages = page;
    objspace->rincgc.pooled_slots += page->free_slots;

    asan_lock_freelist(page);
}

static void
heap_unlink_page(rb_objspace_t *objspace, rb_heap_t *heap, struct heap_page *page)
{
    print_for_debug("heap_unlink_page");
}

static void rb_aligned_free(void *ptr, size_t size);

static void
heap_page_body_free(struct heap_page_body *page_body)
{
    // required
    GC_ASSERT((uintptr_t)page_body % HEAP_PAGE_ALIGN == 0);

    if (HEAP_PAGE_ALLOC_USE_MMAP) {
#ifdef HAVE_MMAP
        GC_ASSERT(HEAP_PAGE_SIZE % sysconf(_SC_PAGE_SIZE) == 0);
        if (munmap(page_body, HEAP_PAGE_SIZE)) {
            rb_bug("heap_page_body_free: munmap failed");
        }
#endif
    }
    else {
        rb_aligned_free(page_body, HEAP_PAGE_SIZE);
    }
}

static void *
rb_aligned_malloc(size_t alignment, size_t size)
{
    print_for_debug("rb_aligned_malloc");
    return 0;
}

static void
heap_pages_free_unused_pages(rb_objspace_t *objspace)
{
    print_for_debug("heap_pages_free_unused_pages");
}

static struct heap_page_body *
heap_page_body_allocate(void)
{
    // required, fails to allocate memory otherwise
    struct heap_page_body *page_body;

    if (HEAP_PAGE_ALLOC_USE_MMAP) {
#ifdef HAVE_MMAP
        GC_ASSERT(HEAP_PAGE_ALIGN % sysconf(_SC_PAGE_SIZE) == 0);

        char *ptr = mmap(NULL, HEAP_PAGE_ALIGN + HEAP_PAGE_SIZE,
                         PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
        if (ptr == MAP_FAILED) {
            return NULL;
        }

        char *aligned = ptr + HEAP_PAGE_ALIGN;
        aligned -= ((VALUE)aligned & (HEAP_PAGE_ALIGN - 1));
        GC_ASSERT(aligned > ptr);
        GC_ASSERT(aligned <= ptr + HEAP_PAGE_ALIGN);

        size_t start_out_of_range_size = aligned - ptr;
        GC_ASSERT(start_out_of_range_size % sysconf(_SC_PAGE_SIZE) == 0);
        if (start_out_of_range_size > 0) {
            if (munmap(ptr, start_out_of_range_size)) {
                rb_bug("heap_page_body_allocate: munmap failed for start");
            }
        }

        size_t end_out_of_range_size = HEAP_PAGE_ALIGN - start_out_of_range_size;
        GC_ASSERT(end_out_of_range_size % sysconf(_SC_PAGE_SIZE) == 0);
        if (end_out_of_range_size > 0) {
            if (munmap(aligned + HEAP_PAGE_SIZE, end_out_of_range_size)) {
                rb_bug("heap_page_body_allocate: munmap failed for end");
            }
        }

        page_body = (struct heap_page_body *)aligned;
#endif
    }
    else {
        page_body = rb_aligned_malloc(HEAP_PAGE_ALIGN, HEAP_PAGE_SIZE);
    }

    GC_ASSERT((uintptr_t)page_body % HEAP_PAGE_ALIGN == 0);

    return page_body;
}

static struct heap_page *
heap_page_allocate(rb_objspace_t *objspace, rb_size_pool_t *size_pool)
{
    // required, segv otherwise
    uintptr_t start, end, p;
    struct heap_page *page;
    uintptr_t hi, lo, mid;
    size_t stride = size_pool->slot_size;
    unsigned int limit = (unsigned int)((HEAP_PAGE_SIZE - sizeof(struct heap_page_header)))/(int)stride;

    /* assign heap_page body (contains heap_page_header and RVALUEs) */
    struct heap_page_body *page_body = heap_page_body_allocate();
    if (page_body == 0) {
        rb_memerror();
    }

    /* assign heap_page entry */
    page = calloc1(sizeof(struct heap_page));
    if (page == 0) {
        heap_page_body_free(page_body);
        rb_memerror();
    }

    /* adjust obj_limit (object number available in this page) */
    start = (uintptr_t)((VALUE)page_body + sizeof(struct heap_page_header));

    if (start % BASE_SLOT_SIZE != 0) {
        int delta = BASE_SLOT_SIZE - (start % BASE_SLOT_SIZE);
        start = start + delta;
        GC_ASSERT(NUM_IN_PAGE(start) == 0 || NUM_IN_PAGE(start) == 1);

        /* Find a num in page that is evenly divisible by `stride`.
         * This is to ensure that objects are aligned with bit planes.
         * In other words, ensure there are an even number of objects
         * per bit plane. */
        if (NUM_IN_PAGE(start) == 1) {
            start += stride - BASE_SLOT_SIZE;
        }

        GC_ASSERT(NUM_IN_PAGE(start) * BASE_SLOT_SIZE % stride == 0);

        limit = (HEAP_PAGE_SIZE - (int)(start - (uintptr_t)page_body))/(int)stride;
    }
    end = start + (limit * (int)stride);

    /* setup heap_pages_sorted */
    lo = 0;
    hi = (uintptr_t)heap_allocated_pages;
    while (lo < hi) {
        struct heap_page *mid_page;

        mid = (lo + hi) / 2;
        mid_page = heap_pages_sorted[mid];
        if ((uintptr_t)mid_page->start < start) {
            lo = mid + 1;
        }
        else if ((uintptr_t)mid_page->start > start) {
            hi = mid;
        }
        else {
            rb_bug("same heap page is allocated: %p at %"PRIuVALUE, (void *)page_body, (VALUE)mid);
        }
    }

    if (hi < (uintptr_t)heap_allocated_pages) {
        MEMMOVE(&heap_pages_sorted[hi+1], &heap_pages_sorted[hi], struct heap_page_header*, heap_allocated_pages - hi);
    }

    heap_pages_sorted[hi] = page;

    heap_allocated_pages++;

    GC_ASSERT(heap_eden_total_pages(objspace) + heap_allocatable_pages(objspace) <= heap_pages_sorted_length);
    GC_ASSERT(heap_eden_total_pages(objspace) + heap_tomb_total_pages(objspace) == heap_allocated_pages - 1);
    GC_ASSERT(heap_allocated_pages <= heap_pages_sorted_length);

    size_pool->total_allocated_pages++;

    if (heap_allocated_pages > heap_pages_sorted_length) {
        rb_bug("heap_page_allocate: allocated(%"PRIdSIZE") > sorted(%"PRIdSIZE")",
               heap_allocated_pages, heap_pages_sorted_length);
    }

    if (heap_pages_lomem == 0 || heap_pages_lomem > start) heap_pages_lomem = start;
    if (heap_pages_himem < end) heap_pages_himem = end;

    page->start = start;
    page->total_slots = limit;
    page->slot_size = size_pool->slot_size;
    page->size_pool = size_pool;
    page_body->header.page = page;

    for (p = start; p != end; p += stride) {
        gc_report(3, objspace, "assign_heap_page: %p is added to freelist\n", (void *)p);
        heap_page_add_freeobj(objspace, page, (VALUE)p);
    }
    page->free_slots = limit;

    asan_lock_freelist(page);
    return page;
}

static struct heap_page *
heap_page_resurrect(rb_objspace_t *objspace, rb_size_pool_t *size_pool)
{
    print_for_debug("heap_page_resurrect");
    return 0;
}

static struct heap_page *
heap_page_create(rb_objspace_t *objspace, rb_size_pool_t *size_pool)
{
    // required, segv otherwise
    struct heap_page *page;
    const char *method = "recycle";

    size_pool->allocatable_pages--;

    page = heap_page_resurrect(objspace, size_pool);

    if (page == NULL) {
        page = heap_page_allocate(objspace, size_pool);
        method = "allocate";
    }
    if (0) fprintf(stderr, "heap_page_create: %s - %p, "
                   "heap_allocated_pages: %"PRIdSIZE", "
                   "heap_allocated_pages: %"PRIdSIZE", "
                   "tomb->total_pages: %"PRIdSIZE"\n",
                   method, (void *)page, heap_pages_sorted_length, heap_allocated_pages, SIZE_POOL_TOMB_HEAP(size_pool)->total_pages);
    return page;
}

static void
heap_add_page(rb_objspace_t *objspace, rb_size_pool_t *size_pool, rb_heap_t *heap, struct heap_page *page)
{
    // required, segv otherwise
    /* Adding to eden heap during incremental sweeping is forbidden */
    GC_ASSERT(!(heap == SIZE_POOL_EDEN_HEAP(size_pool) && heap->sweeping_page));
    page->flags.in_tomb = (heap == SIZE_POOL_TOMB_HEAP(size_pool));
    ccan_list_add_tail(&heap->pages, &page->page_node);
    heap->total_pages++;
    heap->total_slots += page->total_slots;
}

static void
heap_assign_page(rb_objspace_t *objspace, rb_size_pool_t *size_pool, rb_heap_t *heap)
{
    // required, segv
    struct heap_page *page = heap_page_create(objspace, size_pool);
    heap_add_page(objspace, size_pool, heap, page);
    heap_add_freepage(heap, page);
}

static size_t
slots_to_pages_for_size_pool(rb_objspace_t *objspace, rb_size_pool_t *size_pool, size_t slots)
{
    // required, fails to allocate mem otherwise
    size_t multiple = size_pool->slot_size / BASE_SLOT_SIZE;
    /* Due to alignment, heap pages may have one less slot. We should
     * ensure there is enough pages to guarantee that we will have at
     * least the required number of slots after allocating all the pages. */
    size_t slots_per_page = (HEAP_PAGE_OBJ_LIMIT / multiple) - 1;
    return CEILDIV(slots, slots_per_page);
}

static size_t
minimum_pages_for_size_pool(rb_objspace_t *objspace, rb_size_pool_t *size_pool)
{
    // failed to allocate memory
    size_t size_pool_idx = size_pool - size_pools;
    size_t init_slots = gc_params.size_pool_init_slots[size_pool_idx];
    return slots_to_pages_for_size_pool(objspace, size_pool, init_slots);
}

static size_t
heap_extend_pages(rb_objspace_t *objspace, rb_size_pool_t *size_pool, size_t free_slots, size_t total_slots, size_t used)
{
    print_for_debug(__func__);
    return 0;
}

static int
heap_increment(rb_objspace_t *objspace, rb_size_pool_t *size_pool, rb_heap_t *heap)
{
    // failed to allocate memory
    if (size_pool->allocatable_pages > 0) {
        gc_report(1, objspace, "heap_increment: heap_pages_sorted_length: %"PRIdSIZE", "
                  "heap_pages_inc: %"PRIdSIZE", heap->total_pages: %"PRIdSIZE"\n",
                  heap_pages_sorted_length, size_pool->allocatable_pages, heap->total_pages);

        GC_ASSERT(heap_allocatable_pages(objspace) + heap_eden_total_pages(objspace) <= heap_pages_sorted_length);
        GC_ASSERT(heap_allocated_pages <= heap_pages_sorted_length);

        heap_assign_page(objspace, size_pool, heap);
        return TRUE;
    }
    return FALSE;
}

static void
gc_continue(rb_objspace_t *objspace, rb_size_pool_t *size_pool, rb_heap_t *heap)
{
    print_for_debug(__func__);
}

static void
heap_prepare(rb_objspace_t *objspace, rb_size_pool_t *size_pool, rb_heap_t *heap)
{
    // required, segv
    GC_ASSERT(heap->free_pages == NULL);

    /* Continue incremental marking or lazy sweeping, if in any of those steps. */
    gc_continue(objspace, size_pool, heap);

    /* If we still don't have a free page and not allowed to create a new page,
     * we should start a new GC cycle. */
    if (heap->free_pages == NULL &&
            (will_be_incremental_marking(objspace) ||
                (heap_increment(objspace, size_pool, heap) == FALSE))) {
        if (gc_start(objspace, GPR_FLAG_NEWOBJ) == FALSE) {
            rb_memerror();
        }
        else {
            /* Do steps of incremental marking or lazy sweeping if the GC run permits. */
            gc_continue(objspace, size_pool, heap);

            /* If we're not incremental marking (e.g. a minor GC) or finished
             * sweeping and still don't have a free page, then
             * gc_sweep_finish_size_pool should allow us to create a new page. */
            if (heap->free_pages == NULL && !heap_increment(objspace, size_pool, heap)) {
                if (objspace->rgengc.need_major_gc == GPR_FLAG_NONE) {
                    rb_bug("cannot create a new page after GC");
                }
                else { // Major GC is required, which will allow us to create new page
                    if (gc_start(objspace, GPR_FLAG_NEWOBJ) == FALSE) {
                        rb_memerror();
                    }
                    else {
                        /* Do steps of incremental marking or lazy sweeping. */
                        gc_continue(objspace, size_pool, heap);

                        if (heap->free_pages == NULL &&
                                !heap_increment(objspace, size_pool, heap)) {
                            rb_bug("cannot create a new page after major GC");
                        }
                    }
                }
            }
        }
    }

    GC_ASSERT(heap->free_pages != NULL);
}

void
rb_objspace_set_event_hook(const rb_event_flag_t event)
{
    print_for_debug("rb_objspace_set_event_hook");
}

static void
gc_event_hook_body(rb_execution_context_t *ec, rb_objspace_t *objspace, const rb_event_flag_t event, VALUE data)
{
    print_for_debug("gc_event_hook_body");
}

#define gc_event_newobj_hook_needed_p(objspace) ((objspace)->flags.has_newobj_hook)
#define gc_event_hook_needed_p(objspace, event) ((objspace)->hook_events & (event))

#define gc_event_hook_prep(objspace, event, data, prep) do { \
    if (UNLIKELY(gc_event_hook_needed_p(objspace, event))) { \
        prep; \
        gc_event_hook_body(GET_EC(), (objspace), (event), (data)); \
    } \
} while (0)

#define gc_event_hook(objspace, event, data) gc_event_hook_prep(objspace, event, data, (void)0)

static inline VALUE
newobj_init(VALUE klass, VALUE flags, int wb_protected, rb_objspace_t *objspace, VALUE obj)
{
    // required, segv
#if !__has_feature(memory_sanitizer)
    GC_ASSERT(BUILTIN_TYPE(obj) == T_NONE);
    GC_ASSERT((flags & FL_WB_PROTECTED) == 0);
#endif
    RVALUE *p = RANY(obj);
    p->as.basic.flags = flags;
    *((VALUE *)&p->as.basic.klass) = klass;

    int t = flags & RUBY_T_MASK;
    if (t == T_CLASS || t == T_MODULE || t == T_ICLASS) {
        RVALUE_AGE_SET_CANDIDATE(objspace, obj);
    }

#if RACTOR_CHECK_MODE
    rb_ractor_setup_belonging(obj);
#endif

#if RGENGC_CHECK_MODE
    p->as.values.v1 = p->as.values.v2 = p->as.values.v3 = 0;

    RB_VM_LOCK_ENTER_NO_BARRIER();
    {
        check_rvalue_consistency(obj);

        GC_ASSERT(RVALUE_MARKED(obj) == FALSE);
        GC_ASSERT(RVALUE_MARKING(obj) == FALSE);
        GC_ASSERT(RVALUE_OLD_P(obj) == FALSE);
        GC_ASSERT(RVALUE_WB_UNPROTECTED(obj) == FALSE);

        if (RVALUE_REMEMBERED((VALUE)obj)) rb_bug("newobj: %s is remembered.", obj_info(obj));
    }
    RB_VM_LOCK_LEAVE_NO_BARRIER();
#endif

    if (UNLIKELY(wb_protected == FALSE)) {
        ASSERT_vm_locking();
        MARK_IN_BITMAP(GET_HEAP_WB_UNPROTECTED_BITS(obj), obj);
    }

#if RGENGC_PROFILE
    if (wb_protected) {
        objspace->profile.total_generated_normal_object_count++;
#if RGENGC_PROFILE >= 2
        objspace->profile.generated_normal_object_count_types[BUILTIN_TYPE(obj)]++;
#endif
    }
    else {
        objspace->profile.total_generated_shady_object_count++;
#if RGENGC_PROFILE >= 2
        objspace->profile.generated_shady_object_count_types[BUILTIN_TYPE(obj)]++;
#endif
    }
#endif

#if GC_DEBUG
    RANY(obj)->file = rb_source_location_cstr(&RANY(obj)->line);
    GC_ASSERT(!SPECIAL_CONST_P(obj)); /* check alignment */
#endif

    gc_report(5, objspace, "newobj: %s\n", obj_info_basic(obj));

    // RUBY_DEBUG_LOG("obj:%p (%s)", (void *)obj, obj_type_name(obj));
    return obj;
}

size_t
rb_gc_obj_slot_size(VALUE obj)
{
    // required, segv
    return GET_HEAP_PAGE(obj)->slot_size - RVALUE_OVERHEAD;
}

static inline size_t
size_pool_slot_size(unsigned char pool_id)
{
    // required, segv
    GC_ASSERT(pool_id < SIZE_POOL_COUNT);

    size_t slot_size = (1 << pool_id) * BASE_SLOT_SIZE;

#if RGENGC_CHECK_MODE
    rb_objspace_t *objspace = &rb_objspace;
    GC_ASSERT(size_pools[pool_id].slot_size == (short)slot_size);
#endif

    slot_size -= RVALUE_OVERHEAD;

    return slot_size;
}

size_t
rb_size_pool_slot_size(unsigned char pool_id)
{
    // required, compilation hangs
    return size_pool_slot_size(pool_id);
}

bool
rb_gc_size_allocatable_p(size_t size)
{
    // required, segv
    return size <= size_pool_slot_size(SIZE_POOL_COUNT - 1);
}

static size_t size_pool_sizes[SIZE_POOL_COUNT + 1] = { 0 };

size_t *
rb_gc_size_pool_sizes(void)
{
    // required, segv
    if (size_pool_sizes[0] == 0) {
        for (unsigned char i = 0; i < SIZE_POOL_COUNT; i++) {
            size_pool_sizes[i] = rb_size_pool_slot_size(i);
        }
    }

    return size_pool_sizes;
}

size_t
rb_gc_size_pool_id_for_size(size_t size)
{
    // required, segv
    size += RVALUE_OVERHEAD;

    size_t slot_count = CEILDIV(size, BASE_SLOT_SIZE);

    /* size_pool_idx is ceil(log2(slot_count)) */
    size_t size_pool_idx = 64 - nlz_int64(slot_count - 1);

    if (size_pool_idx >= SIZE_POOL_COUNT) {
        rb_bug("rb_gc_size_pool_id_for_size: allocation size too large "
               "(size=%"PRIuSIZE"u, size_pool_idx=%"PRIuSIZE"u)", size, size_pool_idx);
    }

#if RGENGC_CHECK_MODE
    rb_objspace_t *objspace = &rb_objspace;
    GC_ASSERT(size <= (size_t)size_pools[size_pool_idx].slot_size);
    if (size_pool_idx > 0) GC_ASSERT(size > (size_t)size_pools[size_pool_idx - 1].slot_size);
#endif

    return size_pool_idx;
}

static inline VALUE
ractor_cache_allocate_slot(rb_objspace_t *objspace, rb_ractor_newobj_cache_t *cache,
                           size_t size_pool_idx)
{
    // required, segv
    rb_ractor_newobj_size_pool_cache_t *size_pool_cache = &cache->size_pool_caches[size_pool_idx];
    RVALUE *p = size_pool_cache->freelist;

    if (is_incremental_marking(objspace)) {
        // Not allowed to allocate without running an incremental marking step
        if (cache->incremental_mark_step_allocated_slots >= INCREMENTAL_MARK_STEP_ALLOCATIONS) {
            return Qfalse;
        }

        if (p) {
            cache->incremental_mark_step_allocated_slots++;
        }
    }

    if (p) {
        VALUE obj = (VALUE)p;
        MAYBE_UNUSED(const size_t) stride = size_pool_slot_size(size_pool_idx);
        size_pool_cache->freelist = p->as.free.next;
        asan_unpoison_memory_region(p, stride, true);
#if RGENGC_CHECK_MODE
        GC_ASSERT(rb_gc_obj_slot_size(obj) == stride);
        // zero clear
        MEMZERO((char *)obj, char, stride);
#endif
        return obj;
    }
    else {
        return Qfalse;
    }
}

static struct heap_page *
heap_next_free_page(rb_objspace_t *objspace, rb_size_pool_t *size_pool, rb_heap_t *heap)
{
    // required, segv
    ASSERT_vm_locking();

    struct heap_page *page;

    if (heap->free_pages == NULL) {
        heap_prepare(objspace, size_pool, heap);
    }

    page = heap->free_pages;
    heap->free_pages = page->free_next;

    GC_ASSERT(page->free_slots != 0);
    RUBY_DEBUG_LOG("page:%p freelist:%p cnt:%d", (void *)page, (void *)page->freelist, page->free_slots);

    asan_unlock_freelist(page);

    return page;
}

static inline void
ractor_cache_set_page(rb_ractor_newobj_cache_t *cache, size_t size_pool_idx,
                      struct heap_page *page)
{
    // required, segv
    gc_report(3, &rb_objspace, "ractor_set_cache: Using page %p\n", (void *)GET_PAGE_BODY(page->start));

    rb_ractor_newobj_size_pool_cache_t *size_pool_cache = &cache->size_pool_caches[size_pool_idx];

    GC_ASSERT(size_pool_cache->freelist == NULL);
    GC_ASSERT(page->free_slots != 0);
    GC_ASSERT(page->freelist != NULL);

    size_pool_cache->using_page = page;
    size_pool_cache->freelist = page->freelist;
    page->free_slots = 0;
    page->freelist = NULL;

    asan_unpoison_object((VALUE)size_pool_cache->freelist, false);
    GC_ASSERT(RB_TYPE_P((VALUE)size_pool_cache->freelist, T_NONE));
    asan_poison_object((VALUE)size_pool_cache->freelist);
}

static inline VALUE
newobj_fill(VALUE obj, VALUE v1, VALUE v2, VALUE v3)
{
    // required
    RVALUE *p = (RVALUE *)obj;
    p->as.values.v1 = v1;
    p->as.values.v2 = v2;
    p->as.values.v3 = v3;
    return obj;
}

static VALUE
newobj_alloc(rb_objspace_t *objspace, rb_ractor_newobj_cache_t *cache, size_t size_pool_idx, bool vm_locked)
{
    // required
    rb_size_pool_t *size_pool = &size_pools[size_pool_idx];
    rb_heap_t *heap = SIZE_POOL_EDEN_HEAP(size_pool);

    VALUE obj = ractor_cache_allocate_slot(objspace, cache, size_pool_idx);

    if (UNLIKELY(obj == Qfalse)) {
        unsigned int lev;
        bool unlock_vm = false;

        if (!vm_locked) {
            RB_VM_LOCK_ENTER_CR_LEV(GET_RACTOR(), &lev);
            vm_locked = true;
            unlock_vm = true;
        }

        {
            ASSERT_vm_locking();

            if (is_incremental_marking(objspace)) {
                gc_continue(objspace, size_pool, heap);
                cache->incremental_mark_step_allocated_slots = 0;

                // Retry allocation after resetting incremental_mark_step_allocated_slots
                obj = ractor_cache_allocate_slot(objspace, cache, size_pool_idx);
            }

            if (obj == Qfalse) {
                // Get next free page (possibly running GC)
                struct heap_page *page = heap_next_free_page(objspace, size_pool, heap);
                ractor_cache_set_page(cache, size_pool_idx, page);

                // Retry allocation after moving to new page
                obj = ractor_cache_allocate_slot(objspace, cache, size_pool_idx);

                GC_ASSERT(obj != Qfalse);
            }
        }

        if (unlock_vm) {
            RB_VM_LOCK_LEAVE_CR_LEV(GET_RACTOR(), &lev);
        }
    }

    size_pool->total_allocated_objects++;

    return obj;
}

static void
newobj_zero_slot(VALUE obj)
{
    print_for_debug(__func__);
}

ALWAYS_INLINE(static VALUE newobj_slowpath(VALUE klass, VALUE flags, rb_objspace_t *objspace, rb_ractor_newobj_cache_t *cache, int wb_protected, size_t size_pool_idx));

static inline VALUE
newobj_slowpath(VALUE klass, VALUE flags, rb_objspace_t *objspace, rb_ractor_newobj_cache_t *cache, int wb_protected, size_t size_pool_idx)
{
    // required, segv
    VALUE obj;
    unsigned int lev;

    RB_VM_LOCK_ENTER_CR_LEV(GET_RACTOR(), &lev);
    {
        if (UNLIKELY(during_gc || ruby_gc_stressful)) {
            if (during_gc) {
                dont_gc_on();
                during_gc = 0;
                rb_bug("object allocation during garbage collection phase");
            }

            if (ruby_gc_stressful) {
                if (!garbage_collect(objspace, GPR_FLAG_NEWOBJ)) {
                    rb_memerror();
                }
            }
        }

        obj = newobj_alloc(objspace, cache, size_pool_idx, true);
        newobj_init(klass, flags, wb_protected, objspace, obj);

        gc_event_hook_prep(objspace, RUBY_INTERNAL_EVENT_NEWOBJ, obj, newobj_zero_slot(obj));
    }
    RB_VM_LOCK_LEAVE_CR_LEV(GET_RACTOR(), &lev);

    return obj;
}

NOINLINE(static VALUE newobj_slowpath_wb_protected(VALUE klass, VALUE flags,
                                                   rb_objspace_t *objspace, rb_ractor_newobj_cache_t *cache, size_t size_pool_idx));
NOINLINE(static VALUE newobj_slowpath_wb_unprotected(VALUE klass, VALUE flags,
                                                     rb_objspace_t *objspace, rb_ractor_newobj_cache_t *cache, size_t size_pool_idx));

static VALUE
newobj_slowpath_wb_protected(VALUE klass, VALUE flags, rb_objspace_t *objspace, rb_ractor_newobj_cache_t *cache, size_t size_pool_idx)
{
    // required
    return newobj_slowpath(klass, flags, objspace, cache, TRUE, size_pool_idx);
}

static VALUE
newobj_slowpath_wb_unprotected(VALUE klass, VALUE flags, rb_objspace_t *objspace, rb_ractor_newobj_cache_t *cache, size_t size_pool_idx)
{
    // required
    return newobj_slowpath(klass, flags, objspace, cache, FALSE, size_pool_idx);
}

static inline VALUE
newobj_of(rb_ractor_t *cr, VALUE klass, VALUE flags, VALUE v1, VALUE v2, VALUE v3, int wb_protected, size_t alloc_size)
{
    // required
    VALUE obj;
    rb_objspace_t *objspace = &rb_objspace;

    RB_DEBUG_COUNTER_INC(obj_newobj);
    (void)RB_DEBUG_COUNTER_INC_IF(obj_newobj_wb_unprotected, !wb_protected);

    if (UNLIKELY(stress_to_class)) {
        long i, cnt = RARRAY_LEN(stress_to_class);
        for (i = 0; i < cnt; ++i) {
            if (klass == RARRAY_AREF(stress_to_class, i)) rb_memerror();
        }
    }

    size_t size_pool_idx = rb_gc_size_pool_id_for_size(alloc_size);

    rb_ractor_newobj_cache_t *cache = &cr->newobj_cache;

    if (!UNLIKELY(during_gc ||
                  ruby_gc_stressful ||
                  gc_event_newobj_hook_needed_p(objspace)) &&
            wb_protected) {
        obj = newobj_alloc(objspace, cache, size_pool_idx, false);
        newobj_init(klass, flags, wb_protected, objspace, obj);
    }
    else {
        RB_DEBUG_COUNTER_INC(obj_newobj_slowpath);

        obj = wb_protected ?
          newobj_slowpath_wb_protected(klass, flags, objspace, cache, size_pool_idx) :
          newobj_slowpath_wb_unprotected(klass, flags, objspace, cache, size_pool_idx);
    }

    return newobj_fill(obj, v1, v2, v3);
}

VALUE
rb_wb_unprotected_newobj_of(VALUE klass, VALUE flags, size_t size)
{
    // required
    GC_ASSERT((flags & FL_WB_PROTECTED) == 0);
    return newobj_of(GET_RACTOR(), klass, flags, 0, 0, 0, FALSE, size);
}

VALUE
rb_wb_protected_newobj_of(rb_execution_context_t *ec, VALUE klass, VALUE flags, size_t size)
{
    // required
    GC_ASSERT((flags & FL_WB_PROTECTED) == 0);
    return newobj_of(rb_ec_ractor_ptr(ec), klass, flags, 0, 0, 0, TRUE, size);
}

#define UNEXPECTED_NODE(func) \
    rb_bug(#func"(): GC does not handle T_NODE 0x%x(%p) 0x%"PRIxVALUE, \
           BUILTIN_TYPE(obj), (void*)(obj), RBASIC(obj)->flags)

static inline void
rb_data_object_check(VALUE klass)
{
    print_for_debug(__func__);
}

VALUE
rb_data_object_wrap(VALUE klass, void *datap, RUBY_DATA_FUNC dmark, RUBY_DATA_FUNC dfree)
{
    // required, segv
    RUBY_ASSERT_ALWAYS(dfree != (RUBY_DATA_FUNC)1);
    if (klass) rb_data_object_check(klass);
    return newobj_of(GET_RACTOR(), klass, T_DATA, (VALUE)dmark, (VALUE)dfree, (VALUE)datap, !dmark, sizeof(struct RTypedData));
}

VALUE
rb_data_object_zalloc(VALUE klass, size_t size, RUBY_DATA_FUNC dmark, RUBY_DATA_FUNC dfree)
{
    // required
    VALUE obj = rb_data_object_wrap(klass, 0, dmark, dfree);
    DATA_PTR(obj) = xcalloc(1, size);
    return obj;
}

static VALUE
typed_data_alloc(VALUE klass, VALUE typed_flag, void *datap, const rb_data_type_t *type, size_t size)
{
    // required
    RBIMPL_NONNULL_ARG(type);
    if (klass) rb_data_object_check(klass);
    bool wb_protected = (type->flags & RUBY_FL_WB_PROTECTED) || !type->function.dmark;
    return newobj_of(GET_RACTOR(), klass, T_DATA, (VALUE)type, 1 | typed_flag, (VALUE)datap, wb_protected, size);
}

VALUE
rb_data_typed_object_wrap(VALUE klass, void *datap, const rb_data_type_t *type)
{
    // required
    if (UNLIKELY(type->flags & RUBY_TYPED_EMBEDDABLE)) {
        rb_raise(rb_eTypeError, "Cannot wrap an embeddable TypedData");
    }

    return typed_data_alloc(klass, 0, datap, type, sizeof(struct RTypedData));
}

VALUE
rb_data_typed_object_zalloc(VALUE klass, size_t size, const rb_data_type_t *type)
{
    // required
    if (type->flags & RUBY_TYPED_EMBEDDABLE) {
        if (!(type->flags & RUBY_TYPED_FREE_IMMEDIATELY)) {
            rb_raise(rb_eTypeError, "Embeddable TypedData must be freed immediately");
        }

        size_t embed_size = offsetof(struct RTypedData, data) + size;
        if (rb_gc_size_allocatable_p(embed_size)) {
            VALUE obj = typed_data_alloc(klass, TYPED_DATA_EMBEDDED, 0, type, embed_size);
            memset((char *)obj + offsetof(struct RTypedData, data), 0, size);
            return obj;
        }
    }

    VALUE obj = typed_data_alloc(klass, 0, NULL, type, sizeof(struct RTypedData));
    DATA_PTR(obj) = xcalloc(1, size);
    return obj;
}

const char *
rb_objspace_data_type_name(VALUE obj)
{
    print_for_debug(__func__);
    return 0;
}

PUREFUNC(static inline int is_pointer_to_heap(rb_objspace_t *objspace, const void *ptr);)
static inline int
is_pointer_to_heap(rb_objspace_t *objspace, const void *ptr)
{
    print_for_debug(__func__);
    return 0;
}

#define ZOMBIE_OBJ_KEPT_FLAGS (FL_SEEN_OBJ_ID | FL_FINALIZE)

static int
obj_free(rb_objspace_t *objspace, VALUE obj)
{
    print_for_debug(__func__);
    return 0;
}


#define OBJ_ID_INCREMENT (sizeof(RVALUE) / 2)
#define OBJ_ID_INITIAL (OBJ_ID_INCREMENT * 2)

static int
object_id_cmp(st_data_t x, st_data_t y)
{
    print_for_debug(__func__);
    return 0;
}

static st_index_t
object_id_hash(st_data_t n)
{
    print_for_debug(__func__);
    return 0;
}
static const struct st_hash_type object_id_hash_type = {
    object_id_cmp,
    object_id_hash,
};

void
Init_heap(void)
{
    // required, fails to allocate memory
    rb_objspace_t *objspace = &rb_objspace;

#if defined(INIT_HEAP_PAGE_ALLOC_USE_MMAP)
    /* Need to determine if we can use mmap at runtime. */
    heap_page_alloc_use_mmap = INIT_HEAP_PAGE_ALLOC_USE_MMAP;
#endif

    objspace->next_object_id = INT2FIX(OBJ_ID_INITIAL);
    objspace->id_to_obj_tbl = st_init_table(&object_id_hash_type);
    objspace->obj_to_id_tbl = st_init_numtable();

#if RGENGC_ESTIMATE_OLDMALLOC
    objspace->rgengc.oldmalloc_increase_limit = gc_params.oldmalloc_limit_min;
#endif

    /* Set size pools allocatable pages. */
    for (int i = 0; i < SIZE_POOL_COUNT; i++) {
        rb_size_pool_t *size_pool = &size_pools[i];

        /* Set the default value of size_pool_init_slots. */
        gc_params.size_pool_init_slots[i] = GC_HEAP_INIT_SLOTS;

        size_pool->allocatable_pages = minimum_pages_for_size_pool(objspace, size_pool);
    }
    heap_pages_expand_sorted(objspace);

    init_mark_stack(&objspace->mark_stack);

    objspace->profile.invoke_time = getrusage_time();
    finalizer_table = st_init_numtable();
}

void
Init_gc_stress(void)
{
    print_for_debug(__func__);
}

typedef int each_obj_callback(void *, void *, size_t, void *);
typedef int each_page_callback(struct heap_page *, void *);

struct each_obj_data {
    rb_objspace_t *objspace;
    bool reenable_incremental;

    each_obj_callback *each_obj_callback;
    each_page_callback *each_page_callback;
    void *data;

    struct heap_page **pages[SIZE_POOL_COUNT];
    size_t pages_counts[SIZE_POOL_COUNT];
};

/*
 * rb_objspace_each_objects() is special C API to walk through
 * Ruby object space.  This C API is too difficult to use it.
 * To be frank, you should not use it. Or you need to read the
 * source code of this function and understand what this function does.
 *
 * 'callback' will be called several times (the number of heap page,
 * at current implementation) with:
 *   vstart: a pointer to the first living object of the heap_page.
 *   vend: a pointer to next to the valid heap_page area.
 *   stride: a distance to next VALUE.
 *
 * If callback() returns non-zero, the iteration will be stopped.
 *
 * This is a sample callback code to iterate liveness objects:
 *
 *   static int
 *   sample_callback(void *vstart, void *vend, int stride, void *data)
 *   {
 *       VALUE v = (VALUE)vstart;
 *       for (; v != (VALUE)vend; v += stride) {
 *           if (!rb_objspace_internal_object_p(v)) { // liveness check
 *               // do something with live object 'v'
 *           }
 *       }
 *       return 0; // continue to iteration
 *   }
 *
 * Note: 'vstart' is not a top of heap_page.  This point the first
 *       living object to grasp at least one object to avoid GC issue.
 *       This means that you can not walk through all Ruby object page
 *       including freed object page.
 *
 * Note: On this implementation, 'stride' is the same as sizeof(RVALUE).
 *       However, there are possibilities to pass variable values with
 *       'stride' with some reasons.  You must use stride instead of
 *       use some constant value in the iteration.
 */
void
rb_objspace_each_objects(each_obj_callback *callback, void *data)
{
    print_for_debug(__func__);
}

struct os_each_struct {
    size_t num;
    VALUE of;
};

int
rb_objspace_internal_object_p(VALUE obj)
{
    print_for_debug(__func__);
    return 0;
}

/*
 *  call-seq:
 *     ObjectSpace.each_object([module]) {|obj| ... } -> integer
 *     ObjectSpace.each_object([module])              -> an_enumerator
 *
 *  Calls the block once for each living, nonimmediate object in this
 *  Ruby process. If <i>module</i> is specified, calls the block
 *  for only those classes or modules that match (or are a subclass of)
 *  <i>module</i>. Returns the number of objects found. Immediate
 *  objects (<code>Fixnum</code>s, <code>Symbol</code>s
 *  <code>true</code>, <code>false</code>, and <code>nil</code>) are
 *  never returned. In the example below, #each_object returns both
 *  the numbers we defined and several constants defined in the Math
 *  module.
 *
 *  If no block is given, an enumerator is returned instead.
 *
 *     a = 102.7
 *     b = 95       # Won't be returned
 *     c = 12345678987654321
 *     count = ObjectSpace.each_object(Numeric) {|x| p x }
 *     puts "Total count: #{count}"
 *
 *  <em>produces:</em>
 *
 *     12345678987654321
 *     102.7
 *     2.71828182845905
 *     3.14159265358979
 *     2.22044604925031e-16
 *     1.7976931348623157e+308
 *     2.2250738585072e-308
 *     Total count: 7
 *
 */

static VALUE
os_each_obj(int argc, VALUE *argv, VALUE os)
{
    print_for_debug(__func__);
    return 0;
}

/*
 *  call-seq:
 *     ObjectSpace.undefine_finalizer(obj)
 *
 *  Removes all finalizers for <i>obj</i>.
 *
 */

static VALUE
undefine_final(VALUE os, VALUE obj)
{
    print_for_debug(__func__);
    return 0;
}

VALUE
rb_undefine_finalizer(VALUE obj)
{
    print_for_debug(__func__);
    return 0;
}

/*
 *  call-seq:
 *     ObjectSpace.define_finalizer(obj, aProc=proc())
 *
 *  Adds <i>aProc</i> as a finalizer, to be called after <i>obj</i>
 *  was destroyed. The object ID of the <i>obj</i> will be passed
 *  as an argument to <i>aProc</i>. If <i>aProc</i> is a lambda or
 *  method, make sure it can be called with a single argument.
 *
 *  The return value is an array <code>[0, aProc]</code>.
 *
 *  The two recommended patterns are to either create the finaliser proc
 *  in a non-instance method where it can safely capture the needed state,
 *  or to use a custom callable object that stores the needed state
 *  explicitly as instance variables.
 *
 *      class Foo
 *        def initialize(data_needed_for_finalization)
 *          ObjectSpace.define_finalizer(self, self.class.create_finalizer(data_needed_for_finalization))
 *        end
 *
 *        def self.create_finalizer(data_needed_for_finalization)
 *          proc {
 *            puts "finalizing #{data_needed_for_finalization}"
 *          }
 *        end
 *      end
 *
 *      class Bar
 *       class Remover
 *          def initialize(data_needed_for_finalization)
 *            @data_needed_for_finalization = data_needed_for_finalization
 *          end
 *
 *          def call(id)
 *            puts "finalizing #{@data_needed_for_finalization}"
 *          end
 *        end
 *
 *        def initialize(data_needed_for_finalization)
 *          ObjectSpace.define_finalizer(self, Remover.new(data_needed_for_finalization))
 *        end
 *      end
 *
 *  Note that if your finalizer references the object to be
 *  finalized it will never be run on GC, although it will still be
 *  run at exit. You will get a warning if you capture the object
 *  to be finalized as the receiver of the finalizer.
 *
 *      class CapturesSelf
 *        def initialize(name)
 *          ObjectSpace.define_finalizer(self, proc {
 *            # this finalizer will only be run on exit
 *            puts "finalizing #{name}"
 *          })
 *        end
 *      end
 *
 *  Also note that finalization can be unpredictable and is never guaranteed
 *  to be run except on exit.
 */

static VALUE
define_final(int argc, VALUE *argv, VALUE os)
{
    print_for_debug(__func__);
    return 0;
}

VALUE
rb_define_finalizer(VALUE obj, VALUE block)
{
    print_for_debug(__func__);
    return 0;
}

void
rb_gc_copy_finalizer(VALUE dest, VALUE obj)
{
    print_for_debug(__func__);
}

static void
gc_finalize_deferred(void *dmy)
{
    print_for_debug(__func__);
}

static void
gc_finalize_deferred_register(rb_objspace_t *objspace)
{
    print_for_debug(__func__);
}

static int pop_mark_stack(mark_stack_t *stack, VALUE *data);

struct force_finalize_list {
    VALUE obj;
    VALUE table;
    struct force_finalize_list *next;
};

bool rb_obj_is_main_ractor(VALUE gv);

void
rb_objspace_free_objects(rb_objspace_t *objspace)
{
    print_for_debug(__func__);
}

void
rb_objspace_call_finalizer(rb_objspace_t *objspace)
{
    print_for_debug(__func__);
}

static inline bool
is_live_object(rb_objspace_t *objspace, VALUE ptr)
{
    print_for_debug(__func__);
    return 0;
}

static inline int
is_markable_object(VALUE obj)
{
    print_for_debug(__func__);
    return 0;
}

int
rb_objspace_markable_object_p(VALUE obj)
{
    print_for_debug(__func__);
    return 0;
}

int
rb_objspace_garbage_object_p(VALUE obj)
{
    print_for_debug(__func__);
    return 0;
}

bool
rb_gc_is_ptr_to_obj(const void *ptr)
{
    print_for_debug(__func__);
    return 0;
}

/*
 *  call-seq:
 *     ObjectSpace._id2ref(object_id) -> an_object
 *
 *  Converts an object id to a reference to the object. May not be
 *  called on an object id passed as a parameter to a finalizer.
 *
 *     s = "I am a string"                    #=> "I am a string"
 *     r = ObjectSpace._id2ref(s.object_id)   #=> "I am a string"
 *     r == s                                 #=> true
 *
 *  On multi-ractor mode, if the object is not shareable, it raises
 *  RangeError.
 */

/* :nodoc: */
static VALUE
os_id2ref(VALUE os, VALUE objid)
{
    print_for_debug(__func__);
    return 0;
}

static VALUE
rb_find_object_id(VALUE obj, VALUE (*get_heap_object_id)(VALUE))
{
    // required, segv
    if (STATIC_SYM_P(obj)) {
        return (SYM2ID(obj) * sizeof(RVALUE) + (4 << 2)) | FIXNUM_FLAG;
    }
    else if (FLONUM_P(obj)) {
#if SIZEOF_LONG == SIZEOF_VOIDP
        return LONG2NUM((SIGNED_VALUE)obj);
#else
        return LL2NUM((SIGNED_VALUE)obj);
#endif
    }
    else if (SPECIAL_CONST_P(obj)) {
        return LONG2NUM((SIGNED_VALUE)obj);
    }

    return get_heap_object_id(obj);
}

static VALUE
cached_object_id(VALUE obj)
{
    // required, segv
    VALUE id;
    rb_objspace_t *objspace = &rb_objspace;

    RB_VM_LOCK_ENTER();
    if (st_lookup(objspace->obj_to_id_tbl, (st_data_t)obj, &id)) {
        GC_ASSERT(FL_TEST(obj, FL_SEEN_OBJ_ID));
    }
    else {
        GC_ASSERT(!FL_TEST(obj, FL_SEEN_OBJ_ID));

        id = objspace->next_object_id;
        objspace->next_object_id = rb_int_plus(id, INT2FIX(OBJ_ID_INCREMENT));

        VALUE already_disabled = rb_gc_disable_no_rest();
        st_insert(objspace->obj_to_id_tbl, (st_data_t)obj, (st_data_t)id);
        st_insert(objspace->id_to_obj_tbl, (st_data_t)id, (st_data_t)obj);
        if (already_disabled == Qfalse) rb_objspace_gc_enable(objspace);
        FL_SET(obj, FL_SEEN_OBJ_ID);
    }
    RB_VM_LOCK_LEAVE();

    return id;
}

VALUE
rb_memory_id(VALUE obj)
{
    print_for_debug(__func__);
    return 0;
}

/*
 *  Document-method: __id__
 *  Document-method: object_id
 *
 *  call-seq:
 *     obj.__id__       -> integer
 *     obj.object_id    -> integer
 *
 *  Returns an integer identifier for +obj+.
 *
 *  The same number will be returned on all calls to +object_id+ for a given
 *  object, and no two active objects will share an id.
 *
 *  Note: that some objects of builtin classes are reused for optimization.
 *  This is the case for immediate values and frozen string literals.
 *
 *  BasicObject implements +__id__+, Kernel implements +object_id+.
 *
 *  Immediate values are not passed by reference but are passed by value:
 *  +nil+, +true+, +false+, Fixnums, Symbols, and some Floats.
 *
 *      Object.new.object_id  == Object.new.object_id  # => false
 *      (21 * 2).object_id    == (21 * 2).object_id    # => true
 *      "hello".object_id     == "hello".object_id     # => false
 *      "hi".freeze.object_id == "hi".freeze.object_id # => true
 */

VALUE
rb_obj_id(VALUE obj)
{
    // required, segv
    /*
     *                32-bit VALUE space
     *          MSB ------------------------ LSB
     *  false   00000000000000000000000000000000
     *  true    00000000000000000000000000000010
     *  nil     00000000000000000000000000000100
     *  undef   00000000000000000000000000000110
     *  symbol  ssssssssssssssssssssssss00001110
     *  object  oooooooooooooooooooooooooooooo00        = 0 (mod sizeof(RVALUE))
     *  fixnum  fffffffffffffffffffffffffffffff1
     *
     *                    object_id space
     *                                       LSB
     *  false   00000000000000000000000000000000
     *  true    00000000000000000000000000000010
     *  nil     00000000000000000000000000000100
     *  undef   00000000000000000000000000000110
     *  symbol   000SSSSSSSSSSSSSSSSSSSSSSSSSSS0        S...S % A = 4 (S...S = s...s * A + 4)
     *  object   oooooooooooooooooooooooooooooo0        o...o % A = 0
     *  fixnum  fffffffffffffffffffffffffffffff1        bignum if required
     *
     *  where A = sizeof(RVALUE)/4
     *
     *  sizeof(RVALUE) is
     *  20 if 32-bit, double is 4-byte aligned
     *  24 if 32-bit, double is 8-byte aligned
     *  40 if 64-bit
     */

    return rb_find_object_id(obj, cached_object_id);
}

static size_t
obj_memsize_of(VALUE obj, int use_all_types)
{
    print_for_debug(__func__);
    return 0;
}

size_t
rb_obj_memsize_of(VALUE obj)
{
    return obj_memsize_of(obj, TRUE);
}

struct count_objects_data {
    size_t counts[T_MASK+1];
    size_t freed;
    size_t total;
};

/*
 *  call-seq:
 *     ObjectSpace.count_objects([result_hash]) -> hash
 *
 *  Counts all objects grouped by type.
 *
 *  It returns a hash, such as:
 *	{
 *	  :TOTAL=>10000,
 *	  :FREE=>3011,
 *	  :T_OBJECT=>6,
 *	  :T_CLASS=>404,
 *	  # ...
 *	}
 *
 *  The contents of the returned hash are implementation specific.
 *  It may be changed in future.
 *
 *  The keys starting with +:T_+ means live objects.
 *  For example, +:T_ARRAY+ is the number of arrays.
 *  +:FREE+ means object slots which is not used now.
 *  +:TOTAL+ means sum of above.
 *
 *  If the optional argument +result_hash+ is given,
 *  it is overwritten and returned. This is intended to avoid probe effect.
 *
 *    h = {}
 *    ObjectSpace.count_objects(h)
 *    puts h
 *    # => { :TOTAL=>10000, :T_CLASS=>158280, :T_MODULE=>20672, :T_STRING=>527249 }
 *
 *  This method is only expected to work on C Ruby.
 *
 */

static VALUE
count_objects(int argc, VALUE *argv, VALUE os)
{
    print_for_debug(__func__);
    return 0;
}

/*
  ------------------------ Garbage Collection ------------------------
*/

/* Sweeping */

static size_t
objspace_live_slots(rb_objspace_t *objspace)
{
    print_for_debug(__func__);
    return 0;
}

static void
gc_setup_mark_bits(struct heap_page *page)
{
    print_for_debug(__func__);
}

static int gc_is_moveable_obj(rb_objspace_t *objspace, VALUE obj);
static VALUE gc_move(rb_objspace_t *objspace, VALUE scan, VALUE free, size_t src_slot_size, size_t slot_size);

#if defined(_WIN32)
enum {HEAP_PAGE_LOCK = PAGE_NOACCESS, HEAP_PAGE_UNLOCK = PAGE_READWRITE};

static BOOL
protect_page_body(struct heap_page_body *body, DWORD protect)
{
    print_for_debug(__func__);
    return 0;
}
#else
enum {HEAP_PAGE_LOCK = PROT_NONE, HEAP_PAGE_UNLOCK = PROT_READ | PROT_WRITE};
#define protect_page_body(body, protect) !mprotect((body), HEAP_PAGE_SIZE, (protect))
#endif

static void
lock_page_body(rb_objspace_t *objspace, struct heap_page_body *body)
{
    if (!protect_page_body(body, HEAP_PAGE_LOCK)) {
        rb_bug("Couldn't protect page %p, errno: %s", (void *)body, strerror(errno));
    }
    else {
        gc_report(5, objspace, "Protecting page in move %p\n", (void *)body);
    }
}

static void
unlock_page_body(rb_objspace_t *objspace, struct heap_page_body *body)
{
    if (!protect_page_body(body, HEAP_PAGE_UNLOCK)) {
        rb_bug("Couldn't unprotect page %p, errno: %s", (void *)body, strerror(errno));
    }
    else {
        gc_report(5, objspace, "Unprotecting page in move %p\n", (void *)body);
    }
}

static bool
try_move(rb_objspace_t *objspace, rb_heap_t *heap, struct heap_page *free_page, VALUE src)
{
    GC_ASSERT(gc_is_moveable_obj(objspace, src));

    struct heap_page *src_page = GET_HEAP_PAGE(src);
    if (!free_page) {
        return false;
    }

    /* We should return true if either src is successfully moved, or src is
     * unmoveable. A false return will cause the sweeping cursor to be
     * incremented to the next page, and src will attempt to move again */
    GC_ASSERT(MARKED_IN_BITMAP(GET_HEAP_MARK_BITS(src), src));

    asan_unlock_freelist(free_page);
    VALUE dest = (VALUE)free_page->freelist;
    asan_lock_freelist(free_page);
    asan_unpoison_object(dest, false);
    if (!dest) {
        /* if we can't get something from the freelist then the page must be
         * full */
        return false;
    }
    asan_unlock_freelist(free_page);
    free_page->freelist = RANY(dest)->as.free.next;
    asan_lock_freelist(free_page);

    GC_ASSERT(RB_BUILTIN_TYPE(dest) == T_NONE);

    if (src_page->slot_size > free_page->slot_size) {
        objspace->rcompactor.moved_down_count_table[BUILTIN_TYPE(src)]++;
    }
    else if (free_page->slot_size > src_page->slot_size) {
        objspace->rcompactor.moved_up_count_table[BUILTIN_TYPE(src)]++;
    }
    objspace->rcompactor.moved_count_table[BUILTIN_TYPE(src)]++;
    objspace->rcompactor.total_moved++;

    gc_move(objspace, src, dest, src_page->slot_size, free_page->slot_size);
    gc_pin(objspace, src);
    free_page->free_slots--;

    return true;
}

static void
gc_unprotect_pages(rb_objspace_t *objspace, rb_heap_t *heap)
{
    struct heap_page *cursor = heap->compact_cursor;

    while (cursor) {
        unlock_page_body(objspace, GET_PAGE_BODY(cursor->start));
        cursor = ccan_list_next(&heap->pages, cursor, page_node);
    }
}

static void gc_update_references(rb_objspace_t * objspace);
#if GC_CAN_COMPILE_COMPACTION
static void invalidate_moved_page(rb_objspace_t *objspace, struct heap_page *page);
#endif

#if defined(__MINGW32__) || defined(_WIN32)
# define GC_COMPACTION_SUPPORTED 1
#else
/* If not MinGW, Windows, or does not have mmap, we cannot use mprotect for
 * the read barrier, so we must disable compaction. */
# define GC_COMPACTION_SUPPORTED (GC_CAN_COMPILE_COMPACTION && HEAP_PAGE_ALLOC_USE_MMAP)
#endif

#if GC_CAN_COMPILE_COMPACTION
static void
read_barrier_handler(uintptr_t original_address)
{
    VALUE obj;
    rb_objspace_t * objspace = &rb_objspace;

    /* Calculate address aligned to slots. */
    uintptr_t address = original_address - (original_address % BASE_SLOT_SIZE);

    obj = (VALUE)address;

    struct heap_page_body *page_body = GET_PAGE_BODY(obj);

    /* If the page_body is NULL, then mprotect cannot handle it and will crash
     * with "Cannot allocate memory". */
    if (page_body == NULL) {
        rb_bug("read_barrier_handler: segmentation fault at %p", (void *)original_address);
    }

    RB_VM_LOCK_ENTER();
    {
        unlock_page_body(objspace, page_body);

        objspace->profile.read_barrier_faults++;

        invalidate_moved_page(objspace, GET_HEAP_PAGE(obj));
    }
    RB_VM_LOCK_LEAVE();
}
#endif

#if !GC_CAN_COMPILE_COMPACTION
static void
uninstall_handlers(void)
{
    /* no-op */
}

static void
install_handlers(void)
{
    /* no-op */
}
#elif defined(_WIN32)
static LPTOP_LEVEL_EXCEPTION_FILTER old_handler;
typedef void (*signal_handler)(int);
static signal_handler old_sigsegv_handler;

static LONG WINAPI
read_barrier_signal(EXCEPTION_POINTERS * info)
{
    /* EXCEPTION_ACCESS_VIOLATION is what's raised by access to protected pages */
    if (info->ExceptionRecord->ExceptionCode == EXCEPTION_ACCESS_VIOLATION) {
        /* > The second array element specifies the virtual address of the inaccessible data.
         * https://docs.microsoft.com/en-us/windows/win32/api/winnt/ns-winnt-exception_record
         *
         * Use this address to invalidate the page */
        read_barrier_handler((uintptr_t)info->ExceptionRecord->ExceptionInformation[1]);
        return EXCEPTION_CONTINUE_EXECUTION;
    }
    else {
        return EXCEPTION_CONTINUE_SEARCH;
    }
}

static void
uninstall_handlers(void)
{
    signal(SIGSEGV, old_sigsegv_handler);
    SetUnhandledExceptionFilter(old_handler);
}

static void
install_handlers(void)
{
    /* Remove SEGV handler so that the Unhandled Exception Filter handles it */
    old_sigsegv_handler = signal(SIGSEGV, NULL);
    /* Unhandled Exception Filter has access to the violation address similar
     * to si_addr from sigaction */
    old_handler = SetUnhandledExceptionFilter(read_barrier_signal);
}
#else
static struct sigaction old_sigbus_handler;
static struct sigaction old_sigsegv_handler;

#ifdef HAVE_MACH_TASK_EXCEPTION_PORTS
static exception_mask_t old_exception_masks[32];
static mach_port_t old_exception_ports[32];
static exception_behavior_t old_exception_behaviors[32];
static thread_state_flavor_t old_exception_flavors[32];
static mach_msg_type_number_t old_exception_count;

static void
disable_mach_bad_access_exc(void)
{
    old_exception_count = sizeof(old_exception_masks) / sizeof(old_exception_masks[0]);
    task_swap_exception_ports(
        mach_task_self(), EXC_MASK_BAD_ACCESS,
        MACH_PORT_NULL, EXCEPTION_DEFAULT, 0,
        old_exception_masks, &old_exception_count,
        old_exception_ports, old_exception_behaviors, old_exception_flavors
    );
}

static void
restore_mach_bad_access_exc(void)
{
    for (mach_msg_type_number_t i = 0; i < old_exception_count; i++) {
        task_set_exception_ports(
            mach_task_self(),
            old_exception_masks[i], old_exception_ports[i],
            old_exception_behaviors[i], old_exception_flavors[i]
        );
    }
}
#endif

static void
read_barrier_signal(int sig, siginfo_t * info, void * data)
{
    // setup SEGV/BUS handlers for errors
    struct sigaction prev_sigbus, prev_sigsegv;
    sigaction(SIGBUS, &old_sigbus_handler, &prev_sigbus);
    sigaction(SIGSEGV, &old_sigsegv_handler, &prev_sigsegv);

    // enable SIGBUS/SEGV
    sigset_t set, prev_set;
    sigemptyset(&set);
    sigaddset(&set, SIGBUS);
    sigaddset(&set, SIGSEGV);
    sigprocmask(SIG_UNBLOCK, &set, &prev_set);
#ifdef HAVE_MACH_TASK_EXCEPTION_PORTS
    disable_mach_bad_access_exc();
#endif
    // run handler
    read_barrier_handler((uintptr_t)info->si_addr);

    // reset SEGV/BUS handlers
#ifdef HAVE_MACH_TASK_EXCEPTION_PORTS
    restore_mach_bad_access_exc();
#endif
    sigaction(SIGBUS, &prev_sigbus, NULL);
    sigaction(SIGSEGV, &prev_sigsegv, NULL);
    sigprocmask(SIG_SETMASK, &prev_set, NULL);
}

static void
uninstall_handlers(void)
{
#ifdef HAVE_MACH_TASK_EXCEPTION_PORTS
    restore_mach_bad_access_exc();
#endif
    sigaction(SIGBUS, &old_sigbus_handler, NULL);
    sigaction(SIGSEGV, &old_sigsegv_handler, NULL);
}

static void
install_handlers(void)
{
    struct sigaction action;
    memset(&action, 0, sizeof(struct sigaction));
    sigemptyset(&action.sa_mask);
    action.sa_sigaction = read_barrier_signal;
    action.sa_flags = SA_SIGINFO | SA_ONSTACK;

    sigaction(SIGBUS, &action, &old_sigbus_handler);
    sigaction(SIGSEGV, &action, &old_sigsegv_handler);
#ifdef HAVE_MACH_TASK_EXCEPTION_PORTS
    disable_mach_bad_access_exc();
#endif
}
#endif

static void
gc_compact_finish(rb_objspace_t *objspace)
{
    for (int i = 0; i < SIZE_POOL_COUNT; i++) {
        rb_size_pool_t *size_pool = &size_pools[i];
        rb_heap_t *heap = SIZE_POOL_EDEN_HEAP(size_pool);
        gc_unprotect_pages(objspace, heap);
    }

    uninstall_handlers();

    gc_update_references(objspace);
    objspace->profile.compact_count++;

    for (int i = 0; i < SIZE_POOL_COUNT; i++) {
        rb_size_pool_t *size_pool = &size_pools[i];
        rb_heap_t *heap = SIZE_POOL_EDEN_HEAP(size_pool);
        heap->compact_cursor = NULL;
        heap->free_pages = NULL;
        heap->compact_cursor_index = 0;
    }

    if (gc_prof_enabled(objspace)) {
        gc_profile_record *record = gc_prof_record(objspace);
        record->moved_objects = objspace->rcompactor.total_moved - record->moved_objects;
    }
    objspace->flags.during_compacting = FALSE;
}

struct gc_sweep_context {
    struct heap_page *page;
    int final_slots;
    int freed_slots;
    int empty_slots;
};

static inline void
gc_sweep_plane(rb_objspace_t *objspace, rb_heap_t *heap, uintptr_t p, bits_t bitset, struct gc_sweep_context *ctx)
{
    struct heap_page * sweep_page = ctx->page;
    short slot_size = sweep_page->slot_size;
    short slot_bits = slot_size / BASE_SLOT_SIZE;
    GC_ASSERT(slot_bits > 0);

    do {
        VALUE vp = (VALUE)p;
        GC_ASSERT(vp % BASE_SLOT_SIZE == 0);

        asan_unpoison_object(vp, false);
        if (bitset & 1) {
            switch (BUILTIN_TYPE(vp)) {
              default: /* majority case */
                gc_report(2, objspace, "page_sweep: free %p\n", (void *)p);
#if RGENGC_CHECK_MODE
                if (!is_full_marking(objspace)) {
                    if (RVALUE_OLD_P(vp)) rb_bug("page_sweep: %p - old while minor GC.", (void *)p);
                    if (RVALUE_REMEMBERED(vp)) rb_bug("page_sweep: %p - remembered.", (void *)p);
                }
#endif
                if (obj_free(objspace, vp)) {
                    // always add free slots back to the swept pages freelist,
                    // so that if we're comapacting, we can re-use the slots
                    (void)VALGRIND_MAKE_MEM_UNDEFINED((void*)p, BASE_SLOT_SIZE);
                    heap_page_add_freeobj(objspace, sweep_page, vp);
                    gc_report(3, objspace, "page_sweep: %s is added to freelist\n", obj_info(vp));
                    ctx->freed_slots++;
                }
                else {
                    ctx->final_slots++;
                }
                break;

              case T_MOVED:
                if (objspace->flags.during_compacting) {
                    /* The sweep cursor shouldn't have made it to any
                     * T_MOVED slots while the compact flag is enabled.
                     * The sweep cursor and compact cursor move in
                     * opposite directions, and when they meet references will
                     * get updated and "during_compacting" should get disabled */
                    rb_bug("T_MOVED shouldn't be seen until compaction is finished");
                }
                gc_report(3, objspace, "page_sweep: %s is added to freelist\n", obj_info(vp));
                ctx->empty_slots++;
                heap_page_add_freeobj(objspace, sweep_page, vp);
                break;
              case T_ZOMBIE:
                /* already counted */
                break;
              case T_NONE:
                ctx->empty_slots++; /* already freed */
                break;
            }
        }
        p += slot_size;
        bitset >>= slot_bits;
    } while (bitset);
}

static inline void
gc_sweep_page(rb_objspace_t *objspace, rb_heap_t *heap, struct gc_sweep_context *ctx)
{
    struct heap_page *sweep_page = ctx->page;
    GC_ASSERT(SIZE_POOL_EDEN_HEAP(sweep_page->size_pool) == heap);

    uintptr_t p;
    bits_t *bits, bitset;

    gc_report(2, objspace, "page_sweep: start.\n");

#if RGENGC_CHECK_MODE
    if (!objspace->flags.immediate_sweep) {
        GC_ASSERT(sweep_page->flags.before_sweep == TRUE);
    }
#endif
    sweep_page->flags.before_sweep = FALSE;
    sweep_page->free_slots = 0;

    p = (uintptr_t)sweep_page->start;
    bits = sweep_page->mark_bits;

    int page_rvalue_count = sweep_page->total_slots * (sweep_page->slot_size / BASE_SLOT_SIZE);
    int out_of_range_bits = (NUM_IN_PAGE(p) + page_rvalue_count) % BITS_BITLENGTH;
    if (out_of_range_bits != 0) { // sizeof(RVALUE) == 64
        bits[BITMAP_INDEX(p) + page_rvalue_count / BITS_BITLENGTH] |= ~(((bits_t)1 << out_of_range_bits) - 1);
    }

    /* The last bitmap plane may not be used if the last plane does not
     * have enough space for the slot_size. In that case, the last plane must
     * be skipped since none of the bits will be set. */
    int bitmap_plane_count = CEILDIV(NUM_IN_PAGE(p) + page_rvalue_count, BITS_BITLENGTH);
    GC_ASSERT(bitmap_plane_count == HEAP_PAGE_BITMAP_LIMIT - 1 ||
                  bitmap_plane_count == HEAP_PAGE_BITMAP_LIMIT);

    // Skip out of range slots at the head of the page
    bitset = ~bits[0];
    bitset >>= NUM_IN_PAGE(p);
    if (bitset) {
        gc_sweep_plane(objspace, heap, p, bitset, ctx);
    }
    p += (BITS_BITLENGTH - NUM_IN_PAGE(p)) * BASE_SLOT_SIZE;

    for (int i = 1; i < bitmap_plane_count; i++) {
        bitset = ~bits[i];
        if (bitset) {
            gc_sweep_plane(objspace, heap, p, bitset, ctx);
        }
        p += BITS_BITLENGTH * BASE_SLOT_SIZE;
    }

    if (!heap->compact_cursor) {
        gc_setup_mark_bits(sweep_page);
    }

#if GC_PROFILE_MORE_DETAIL
    if (gc_prof_enabled(objspace)) {
        gc_profile_record *record = gc_prof_record(objspace);
        record->removing_objects += ctx->final_slots + ctx->freed_slots;
        record->empty_objects += ctx->empty_slots;
    }
#endif
    if (0) fprintf(stderr, "gc_sweep_page(%"PRIdSIZE"): total_slots: %d, freed_slots: %d, empty_slots: %d, final_slots: %d\n",
                   rb_gc_count(),
                   sweep_page->total_slots,
                   ctx->freed_slots, ctx->empty_slots, ctx->final_slots);

    sweep_page->free_slots += ctx->freed_slots + ctx->empty_slots;
    sweep_page->size_pool->total_freed_objects += ctx->freed_slots;

    if (heap_pages_deferred_final && !finalizing) {
        rb_thread_t *th = GET_THREAD();
        if (th) {
            gc_finalize_deferred_register(objspace);
        }
    }

#if RGENGC_CHECK_MODE
    short freelist_len = 0;
    asan_unlock_freelist(sweep_page);
    RVALUE *ptr = sweep_page->freelist;
    while (ptr) {
        freelist_len++;
        ptr = ptr->as.free.next;
    }
    asan_lock_freelist(sweep_page);
    if (freelist_len != sweep_page->free_slots) {
        rb_bug("inconsistent freelist length: expected %d but was %d", sweep_page->free_slots, freelist_len);
    }
#endif

    gc_report(2, objspace, "page_sweep: end.\n");
}

static const char *
gc_mode_name(enum gc_mode mode)
{
    print_for_debug("gc_mode_name");
    return 0;
}

static void
gc_mode_transition(rb_objspace_t *objspace, enum gc_mode mode)
{
#if RGENGC_CHECK_MODE
    enum gc_mode prev_mode = gc_mode(objspace);
    switch (prev_mode) {
      case gc_mode_none:     GC_ASSERT(mode == gc_mode_marking); break;
      case gc_mode_marking:  GC_ASSERT(mode == gc_mode_sweeping); break;
      case gc_mode_sweeping: GC_ASSERT(mode == gc_mode_none || mode == gc_mode_compacting); break;
      case gc_mode_compacting: GC_ASSERT(mode == gc_mode_none); break;
    }
#endif
    if (0) fprintf(stderr, "gc_mode_transition: %s->%s\n", gc_mode_name(gc_mode(objspace)), gc_mode_name(mode));
    gc_mode_set(objspace, mode);
}

static void
heap_page_freelist_append(struct heap_page *page, RVALUE *freelist)
{
    if (freelist) {
        asan_unlock_freelist(page);
        if (page->freelist) {
            RVALUE *p = page->freelist;
            asan_unpoison_object((VALUE)p, false);
            while (p->as.free.next) {
                RVALUE *prev = p;
                p = p->as.free.next;
                asan_poison_object((VALUE)prev);
                asan_unpoison_object((VALUE)p, false);
            }
            p->as.free.next = freelist;
            asan_poison_object((VALUE)p);
        }
        else {
            page->freelist = freelist;
        }
        asan_lock_freelist(page);
    }
}

static void
gc_sweep_start_heap(rb_objspace_t *objspace, rb_heap_t *heap)
{
    heap->sweeping_page = ccan_list_top(&heap->pages, struct heap_page, page_node);
    heap->free_pages = NULL;
    heap->pooled_pages = NULL;
    if (!objspace->flags.immediate_sweep) {
        struct heap_page *page = NULL;

        ccan_list_for_each(&heap->pages, page, page_node) {
            page->flags.before_sweep = TRUE;
        }
    }
}

#if defined(__GNUC__) && __GNUC__ == 4 && __GNUC_MINOR__ == 4
__attribute__((noinline))
#endif

#if GC_CAN_COMPILE_COMPACTION
static void gc_sort_heap_by_compare_func(rb_objspace_t *objspace, gc_compact_compare_func compare_func);
static int compare_pinned_slots(const void *left, const void *right, void *d);
#endif

static void
gc_sweep_start(rb_objspace_t *objspace)
{
    gc_mode_transition(objspace, gc_mode_sweeping);
    objspace->rincgc.pooled_slots = 0;

#if GC_CAN_COMPILE_COMPACTION
    if (objspace->flags.during_compacting) {
        gc_sort_heap_by_compare_func(
            objspace,
            objspace->rcompactor.compare_func ? objspace->rcompactor.compare_func : compare_pinned_slots
        );
    }
#endif

    for (int i = 0; i < SIZE_POOL_COUNT; i++) {
        rb_size_pool_t *size_pool = &size_pools[i];
        rb_heap_t *heap = SIZE_POOL_EDEN_HEAP(size_pool);

        gc_sweep_start_heap(objspace, heap);

        /* We should call gc_sweep_finish_size_pool for size pools with no pages. */
        if (heap->sweeping_page == NULL) {
            GC_ASSERT(heap->total_pages == 0);
            GC_ASSERT(heap->total_slots == 0);
            gc_sweep_finish_size_pool(objspace, size_pool);
        }
    }

    rb_ractor_t *r = NULL;
    ccan_list_for_each(&GET_VM()->ractor.set, r, vmlr_node) {
        rb_gc_ractor_newobj_cache_clear(&r->newobj_cache);
    }
}

static void
gc_sweep_finish_size_pool(rb_objspace_t *objspace, rb_size_pool_t *size_pool)
{
    rb_heap_t *heap = SIZE_POOL_EDEN_HEAP(size_pool);
    size_t total_slots = heap->total_slots + SIZE_POOL_TOMB_HEAP(size_pool)->total_slots;
    size_t total_pages = heap->total_pages + SIZE_POOL_TOMB_HEAP(size_pool)->total_pages;
    size_t swept_slots = size_pool->freed_slots + size_pool->empty_slots;

    size_t init_slots = gc_params.size_pool_init_slots[size_pool - size_pools];
    size_t min_free_slots = (size_t)(MAX(total_slots, init_slots) * gc_params.heap_free_slots_min_ratio);

    /* If we don't have enough slots and we have pages on the tomb heap, move
     * pages from the tomb heap to the eden heap. This may prevent page
     * creation thrashing (frequently allocating and deallocting pages) and
     * GC thrashing (running GC more frequently than required). */
    struct heap_page *resurrected_page;
    while (swept_slots < min_free_slots &&
            (resurrected_page = heap_page_resurrect(objspace, size_pool))) {
        swept_slots += resurrected_page->free_slots;

        heap_add_page(objspace, size_pool, heap, resurrected_page);
        heap_add_freepage(heap, resurrected_page);
    }

    if (swept_slots < min_free_slots) {
        bool grow_heap = is_full_marking(objspace);

        /* Consider growing or starting a major GC if we are not currently in a
         * major GC and we can't allocate any more pages. */
        if (!is_full_marking(objspace) && size_pool->allocatable_pages == 0) {
            /* The heap is a growth heap if it freed more slots than had empty slots. */
            bool is_growth_heap = size_pool->empty_slots == 0 || size_pool->freed_slots > size_pool->empty_slots;

            /* Grow this heap if we haven't run at least RVALUE_OLD_AGE minor
             * GC since the last major GC or if this heap is smaller than the
             * the configured initial size. */
            if (objspace->profile.count - objspace->rgengc.last_major_gc < RVALUE_OLD_AGE ||
                    total_slots < init_slots) {
                grow_heap = TRUE;
            }
            else if (is_growth_heap) { /* Only growth heaps are allowed to start a major GC. */
                objspace->rgengc.need_major_gc |= GPR_FLAG_MAJOR_BY_NOFREE;
                size_pool->force_major_gc_count++;
            }
        }

        if (grow_heap) {
            size_t extend_page_count = heap_extend_pages(objspace, size_pool, swept_slots, total_slots, total_pages);

            if (extend_page_count > size_pool->allocatable_pages) {
                size_pool_allocatable_pages_set(objspace, size_pool, extend_page_count);
            }
        }
    }
}

static void
gc_sweep_finish(rb_objspace_t *objspace)
{
    gc_report(1, objspace, "gc_sweep_finish\n");

    gc_prof_set_heap_info(objspace);
    heap_pages_free_unused_pages(objspace);

    for (int i = 0; i < SIZE_POOL_COUNT; i++) {
        rb_size_pool_t *size_pool = &size_pools[i];

        /* if heap_pages has unused pages, then assign them to increment */
        size_t tomb_pages = SIZE_POOL_TOMB_HEAP(size_pool)->total_pages;
        if (size_pool->allocatable_pages < tomb_pages) {
            size_pool->allocatable_pages = tomb_pages;
        }

        size_pool->freed_slots = 0;
        size_pool->empty_slots = 0;

        if (!will_be_incremental_marking(objspace)) {
            rb_heap_t *eden_heap = SIZE_POOL_EDEN_HEAP(size_pool);
            struct heap_page *end_page = eden_heap->free_pages;
            if (end_page) {
                while (end_page->free_next) end_page = end_page->free_next;
                end_page->free_next = eden_heap->pooled_pages;
            }
            else {
                eden_heap->free_pages = eden_heap->pooled_pages;
            }
            eden_heap->pooled_pages = NULL;
            objspace->rincgc.pooled_slots = 0;
        }
    }
    heap_pages_expand_sorted(objspace);

    gc_event_hook(objspace, RUBY_INTERNAL_EVENT_GC_END_SWEEP, 0);
    gc_mode_transition(objspace, gc_mode_none);

#if RGENGC_CHECK_MODE >= 2
    gc_verify_internal_consistency(objspace);
#endif
}

static int
gc_sweep_step(rb_objspace_t *objspace, rb_size_pool_t *size_pool, rb_heap_t *heap)
{
    struct heap_page *sweep_page = heap->sweeping_page;
    int unlink_limit = GC_SWEEP_PAGES_FREEABLE_PER_STEP;
    int swept_slots = 0;
    int pooled_slots = 0;

    if (sweep_page == NULL) return FALSE;

#if GC_ENABLE_LAZY_SWEEP
    gc_prof_sweep_timer_start(objspace);
#endif

    do {
        RUBY_DEBUG_LOG("sweep_page:%p", (void *)sweep_page);

        struct gc_sweep_context ctx = {
            .page = sweep_page,
            .final_slots = 0,
            .freed_slots = 0,
            .empty_slots = 0,
        };
        gc_sweep_page(objspace, heap, &ctx);
        int free_slots = ctx.freed_slots + ctx.empty_slots;

        heap->sweeping_page = ccan_list_next(&heap->pages, sweep_page, page_node);

        if (sweep_page->final_slots + free_slots == sweep_page->total_slots &&
            heap_pages_freeable_pages > 0 &&
            unlink_limit > 0) {
            heap_pages_freeable_pages--;
            unlink_limit--;
            /* there are no living objects -> move this page to tomb heap */
            heap_unlink_page(objspace, heap, sweep_page);
            heap_add_page(objspace, size_pool, SIZE_POOL_TOMB_HEAP(size_pool), sweep_page);
        }
        else if (free_slots > 0) {
            size_pool->freed_slots += ctx.freed_slots;
            size_pool->empty_slots += ctx.empty_slots;

            if (pooled_slots < GC_INCREMENTAL_SWEEP_POOL_SLOT_COUNT) {
                heap_add_poolpage(objspace, heap, sweep_page);
                pooled_slots += free_slots;
            }
            else {
                heap_add_freepage(heap, sweep_page);
                swept_slots += free_slots;
                if (swept_slots > GC_INCREMENTAL_SWEEP_SLOT_COUNT) {
                    break;
                }
            }
        }
        else {
            sweep_page->free_next = NULL;
        }
    } while ((sweep_page = heap->sweeping_page));

    if (!heap->sweeping_page) {
        gc_sweep_finish_size_pool(objspace, size_pool);

        if (!has_sweeping_pages(objspace)) {
            gc_sweep_finish(objspace);
        }
    }

#if GC_ENABLE_LAZY_SWEEP
    gc_prof_sweep_timer_stop(objspace);
#endif

    return heap->free_pages != NULL;
}

static void
gc_sweep_rest(rb_objspace_t *objspace)
{
    for (int i = 0; i < SIZE_POOL_COUNT; i++) {
        rb_size_pool_t *size_pool = &size_pools[i];

        while (SIZE_POOL_EDEN_HEAP(size_pool)->sweeping_page) {
            gc_sweep_step(objspace, size_pool, SIZE_POOL_EDEN_HEAP(size_pool));
        }
    }
}

#if GC_CAN_COMPILE_COMPACTION
static void
invalidate_moved_plane(rb_objspace_t *objspace, struct heap_page *page, uintptr_t p, bits_t bitset)
{
    if (bitset) {
        do {
            if (bitset & 1) {
                VALUE forwarding_object = (VALUE)p;
                VALUE object;

                if (BUILTIN_TYPE(forwarding_object) == T_MOVED) {
                    GC_ASSERT(MARKED_IN_BITMAP(GET_HEAP_PINNED_BITS(forwarding_object), forwarding_object));
                    GC_ASSERT(!MARKED_IN_BITMAP(GET_HEAP_MARK_BITS(forwarding_object), forwarding_object));

                    CLEAR_IN_BITMAP(GET_HEAP_PINNED_BITS(forwarding_object), forwarding_object);

                    object = rb_gc_location(forwarding_object);

                    shape_id_t original_shape_id = 0;
                    if (RB_TYPE_P(object, T_OBJECT)) {
                        original_shape_id = RMOVED(forwarding_object)->original_shape_id;
                    }

                    gc_move(objspace, object, forwarding_object, GET_HEAP_PAGE(object)->slot_size, page->slot_size);
                    /* forwarding_object is now our actual object, and "object"
                     * is the free slot for the original page */

                    if (original_shape_id) {
                        ROBJECT_SET_SHAPE_ID(forwarding_object, original_shape_id);
                    }

                    struct heap_page *orig_page = GET_HEAP_PAGE(object);
                    orig_page->free_slots++;
                    heap_page_add_freeobj(objspace, orig_page, object);

                    GC_ASSERT(MARKED_IN_BITMAP(GET_HEAP_MARK_BITS(forwarding_object), forwarding_object));
                    GC_ASSERT(BUILTIN_TYPE(forwarding_object) != T_MOVED);
                    GC_ASSERT(BUILTIN_TYPE(forwarding_object) != T_NONE);
                }
            }
            p += BASE_SLOT_SIZE;
            bitset >>= 1;
        } while (bitset);
    }
}

static void
invalidate_moved_page(rb_objspace_t *objspace, struct heap_page *page)
{
    int i;
    bits_t *mark_bits, *pin_bits;
    bits_t bitset;

    mark_bits = page->mark_bits;
    pin_bits = page->pinned_bits;

    uintptr_t p = page->start;

    // Skip out of range slots at the head of the page
    bitset = pin_bits[0] & ~mark_bits[0];
    bitset >>= NUM_IN_PAGE(p);
    invalidate_moved_plane(objspace, page, p, bitset);
    p += (BITS_BITLENGTH - NUM_IN_PAGE(p)) * BASE_SLOT_SIZE;

    for (i=1; i < HEAP_PAGE_BITMAP_LIMIT; i++) {
        /* Moved objects are pinned but never marked. We reuse the pin bits
         * to indicate there is a moved object in this slot. */
        bitset = pin_bits[i] & ~mark_bits[i];

        invalidate_moved_plane(objspace, page, p, bitset);
        p += BITS_BITLENGTH * BASE_SLOT_SIZE;
    }
}
#endif

static void
gc_compact_start(rb_objspace_t *objspace)
{
    struct heap_page *page = NULL;
    gc_mode_transition(objspace, gc_mode_compacting);

    for (int i = 0; i < SIZE_POOL_COUNT; i++) {
        rb_heap_t *heap = SIZE_POOL_EDEN_HEAP(&size_pools[i]);
        ccan_list_for_each(&heap->pages, page, page_node) {
            page->flags.before_sweep = TRUE;
        }

        heap->compact_cursor = ccan_list_tail(&heap->pages, struct heap_page, page_node);
        heap->compact_cursor_index = 0;
    }

    if (gc_prof_enabled(objspace)) {
        gc_profile_record *record = gc_prof_record(objspace);
        record->moved_objects = objspace->rcompactor.total_moved;
    }

    memset(objspace->rcompactor.considered_count_table, 0, T_MASK * sizeof(size_t));
    memset(objspace->rcompactor.moved_count_table, 0, T_MASK * sizeof(size_t));
    memset(objspace->rcompactor.moved_up_count_table, 0, T_MASK * sizeof(size_t));
    memset(objspace->rcompactor.moved_down_count_table, 0, T_MASK * sizeof(size_t));

    /* Set up read barrier for pages containing MOVED objects */
    install_handlers();
}

static void gc_sweep_compact(rb_objspace_t *objspace);

static void
gc_sweep(rb_objspace_t *objspace)
{
    gc_sweeping_enter(objspace);

    const unsigned int immediate_sweep = objspace->flags.immediate_sweep;

    gc_report(1, objspace, "gc_sweep: immediate: %d\n", immediate_sweep);

    gc_sweep_start(objspace);
    if (objspace->flags.during_compacting) {
        gc_sweep_compact(objspace);
    }

    if (immediate_sweep) {
#if !GC_ENABLE_LAZY_SWEEP
        gc_prof_sweep_timer_start(objspace);
#endif
        gc_sweep_rest(objspace);
#if !GC_ENABLE_LAZY_SWEEP
        gc_prof_sweep_timer_stop(objspace);
#endif
    }
    else {

        /* Sweep every size pool. */
        for (int i = 0; i < SIZE_POOL_COUNT; i++) {
            rb_size_pool_t *size_pool = &size_pools[i];
            gc_sweep_step(objspace, size_pool, SIZE_POOL_EDEN_HEAP(size_pool));
        }
    }

    gc_sweeping_exit(objspace);
}

/* Marking - Marking stack */

static stack_chunk_t *
stack_chunk_alloc(void)
{
    stack_chunk_t *res;

    res = malloc(sizeof(stack_chunk_t));
    if (!res)
        rb_memerror();

    return res;
}

static inline int
is_mark_stack_empty(mark_stack_t *stack)
{
    return stack->chunk == NULL;
}

static size_t
mark_stack_size(mark_stack_t *stack)
{
    size_t size = stack->index;
    stack_chunk_t *chunk = stack->chunk ? stack->chunk->next : NULL;

    while (chunk) {
        size += stack->limit;
        chunk = chunk->next;
    }
    return size;
}

static void
add_stack_chunk_cache(mark_stack_t *stack, stack_chunk_t *chunk)
{
    chunk->next = stack->cache;
    stack->cache = chunk;
    stack->cache_size++;
}

static void
shrink_stack_chunk_cache(mark_stack_t *stack)
{
    stack_chunk_t *chunk;

    if (stack->unused_cache_size > (stack->cache_size/2)) {
        chunk = stack->cache;
        stack->cache = stack->cache->next;
        stack->cache_size--;
        free(chunk);
    }
    stack->unused_cache_size = stack->cache_size;
}

static void
push_mark_stack_chunk(mark_stack_t *stack)
{
    stack_chunk_t *next;

    GC_ASSERT(stack->index == stack->limit);

    if (stack->cache_size > 0) {
        next = stack->cache;
        stack->cache = stack->cache->next;
        stack->cache_size--;
        if (stack->unused_cache_size > stack->cache_size)
            stack->unused_cache_size = stack->cache_size;
    }
    else {
        next = stack_chunk_alloc();
    }
    next->next = stack->chunk;
    stack->chunk = next;
    stack->index = 0;
}

static void
pop_mark_stack_chunk(mark_stack_t *stack)
{
    stack_chunk_t *prev;

    prev = stack->chunk->next;
    GC_ASSERT(stack->index == 0);
    add_stack_chunk_cache(stack, stack->chunk);
    stack->chunk = prev;
    stack->index = stack->limit;
}

static void
push_mark_stack(mark_stack_t *stack, VALUE obj)
{
    switch (BUILTIN_TYPE(obj)) {
      case T_OBJECT:
      case T_CLASS:
      case T_MODULE:
      case T_FLOAT:
      case T_STRING:
      case T_REGEXP:
      case T_ARRAY:
      case T_HASH:
      case T_STRUCT:
      case T_BIGNUM:
      case T_FILE:
      case T_DATA:
      case T_MATCH:
      case T_COMPLEX:
      case T_RATIONAL:
      case T_TRUE:
      case T_FALSE:
      case T_SYMBOL:
      case T_IMEMO:
      case T_ICLASS:
        if (stack->index == stack->limit) {
            push_mark_stack_chunk(stack);
        }
        stack->chunk->data[stack->index++] = obj;
        return;

      case T_NONE:
      case T_NIL:
      case T_FIXNUM:
      case T_MOVED:
      case T_ZOMBIE:
      case T_UNDEF:
      case T_MASK:
        rb_bug("push_mark_stack() called for broken object");
        break;

      case T_NODE:
        UNEXPECTED_NODE(push_mark_stack);
        break;
    }

    rb_bug("rb_gc_mark(): unknown data type 0x%x(%p) %s",
            BUILTIN_TYPE(obj), (void *)obj,
            is_pointer_to_heap(&rb_objspace, (void *)obj) ? "corrupted object" : "non object");
}

static int
pop_mark_stack(mark_stack_t *stack, VALUE *data)
{
    if (is_mark_stack_empty(stack)) {
        return FALSE;
    }
    if (stack->index == 1) {
        *data = stack->chunk->data[--stack->index];
        pop_mark_stack_chunk(stack);
    }
    else {
        *data = stack->chunk->data[--stack->index];
    }
    return TRUE;
}

static void
init_mark_stack(mark_stack_t *stack)
{
    int i;

    MEMZERO(stack, mark_stack_t, 1);
    stack->index = stack->limit = STACK_CHUNK_SIZE;

    for (i=0; i < 4; i++) {
        add_stack_chunk_cache(stack, stack_chunk_alloc());
    }
    stack->unused_cache_size = stack->cache_size;
}

/* Marking */

#define SET_STACK_END SET_MACHINE_STACK_END(&ec->machine.stack_end)

#define STACK_START (ec->machine.stack_start)
#define STACK_END (ec->machine.stack_end)
#define STACK_LEVEL_MAX (ec->machine.stack_maxsize/sizeof(VALUE))

#if STACK_GROW_DIRECTION < 0
# define STACK_LENGTH  (size_t)(STACK_START - STACK_END)
#elif STACK_GROW_DIRECTION > 0
# define STACK_LENGTH  (size_t)(STACK_END - STACK_START + 1)
#else
# define STACK_LENGTH  ((STACK_END < STACK_START) ? (size_t)(STACK_START - STACK_END) \
                        : (size_t)(STACK_END - STACK_START + 1))
#endif
#if !STACK_GROW_DIRECTION
int ruby_stack_grow_direction;
int
ruby_get_stack_grow_direction(volatile VALUE *addr)
{
    VALUE *end;
    SET_MACHINE_STACK_END(&end);

    if (end > addr) return ruby_stack_grow_direction = 1;
    return ruby_stack_grow_direction = -1;
}
#endif

size_t
ruby_stack_length(VALUE **p)
{
    rb_execution_context_t *ec = GET_EC();
    SET_STACK_END;
    if (p) *p = STACK_UPPER(STACK_END, STACK_START, STACK_END);
    return STACK_LENGTH;
}

#define PREVENT_STACK_OVERFLOW 1
#ifndef PREVENT_STACK_OVERFLOW
#if !(defined(POSIX_SIGNAL) && defined(SIGSEGV) && defined(HAVE_SIGALTSTACK))
# define PREVENT_STACK_OVERFLOW 1
#else
# define PREVENT_STACK_OVERFLOW 0
#endif
#endif
#if PREVENT_STACK_OVERFLOW && !defined(__EMSCRIPTEN__)
static int
stack_check(rb_execution_context_t *ec, int water_mark)
{
    SET_STACK_END;

    size_t length = STACK_LENGTH;
    size_t maximum_length = STACK_LEVEL_MAX - water_mark;

    return length > maximum_length;
}
#else
#define stack_check(ec, water_mark) FALSE
#endif

#define STACKFRAME_FOR_CALL_CFUNC 2048

int
rb_ec_stack_check(rb_execution_context_t *ec)
{
    return stack_check(ec, STACKFRAME_FOR_CALL_CFUNC);
}

int
ruby_stack_check(void)
{
    return stack_check(GET_EC(), STACKFRAME_FOR_CALL_CFUNC);
}

ATTRIBUTE_NO_ADDRESS_SAFETY_ANALYSIS(static void each_location(rb_objspace_t *objspace, register const VALUE *x, register long n, void (*cb)(rb_objspace_t *, VALUE)));
static void
each_location(rb_objspace_t *objspace, register const VALUE *x, register long n, void (*cb)(rb_objspace_t *, VALUE))
{
    VALUE v;
    while (n--) {
        v = *x;
        cb(objspace, v);
        x++;
    }
}

static void
gc_mark_locations(rb_objspace_t *objspace, const VALUE *start, const VALUE *end, void (*cb)(rb_objspace_t *, VALUE))
{
    long n;

    if (end <= start) return;
    n = end - start;
    each_location(objspace, start, n, cb);
}

void
rb_gc_mark_locations(const VALUE *start, const VALUE *end)
{
    gc_mark_locations(&rb_objspace, start, end, gc_mark_maybe);
}

void
rb_gc_mark_values(long n, const VALUE *values)
{
    long i;
    rb_objspace_t *objspace = &rb_objspace;

    for (i=0; i<n; i++) {
        gc_mark(objspace, values[i]);
    }
}

void
rb_gc_mark_vm_stack_values(long n, const VALUE *values)
{
    rb_objspace_t *objspace = &rb_objspace;

    for (long i = 0; i < n; i++) {
        gc_mark_and_pin(objspace, values[i]);
    }
}

static int
mark_value(st_data_t key, st_data_t value, st_data_t data)
{
    rb_objspace_t *objspace = (rb_objspace_t *)data;
    gc_mark(objspace, (VALUE)value);
    return ST_CONTINUE;
}

static int
mark_value_pin(st_data_t key, st_data_t value, st_data_t data)
{
    rb_objspace_t *objspace = (rb_objspace_t *)data;
    gc_mark_and_pin(objspace, (VALUE)value);
    return ST_CONTINUE;
}

static void
mark_tbl_no_pin(rb_objspace_t *objspace, st_table *tbl)
{
    if (!tbl || tbl->num_entries == 0) return;
    st_foreach(tbl, mark_value, (st_data_t)objspace);
}

static void
mark_tbl(rb_objspace_t *objspace, st_table *tbl)
{
    if (!tbl || tbl->num_entries == 0) return;
    st_foreach(tbl, mark_value_pin, (st_data_t)objspace);
}

static int
mark_key(st_data_t key, st_data_t value, st_data_t data)
{
    rb_objspace_t *objspace = (rb_objspace_t *)data;
    gc_mark_and_pin(objspace, (VALUE)key);
    return ST_CONTINUE;
}

static void
mark_set(rb_objspace_t *objspace, st_table *tbl)
{
    if (!tbl) return;
    st_foreach(tbl, mark_key, (st_data_t)objspace);
}

static int
pin_value(st_data_t key, st_data_t value, st_data_t data)
{
    rb_objspace_t *objspace = (rb_objspace_t *)data;
    gc_mark_and_pin(objspace, (VALUE)value);
    return ST_CONTINUE;
}

static void
mark_finalizer_tbl(rb_objspace_t *objspace, st_table *tbl)
{
    if (!tbl) return;
    st_foreach(tbl, pin_value, (st_data_t)objspace);
}

void
rb_mark_set(st_table *tbl)
{
    mark_set(&rb_objspace, tbl);
}

static int
mark_keyvalue(st_data_t key, st_data_t value, st_data_t data)
{
    rb_objspace_t *objspace = (rb_objspace_t *)data;

    gc_mark(objspace, (VALUE)key);
    gc_mark(objspace, (VALUE)value);
    return ST_CONTINUE;
}

static int
pin_key_pin_value(st_data_t key, st_data_t value, st_data_t data)
{
    rb_objspace_t *objspace = (rb_objspace_t *)data;

    gc_mark_and_pin(objspace, (VALUE)key);
    gc_mark_and_pin(objspace, (VALUE)value);
    return ST_CONTINUE;
}

static int
pin_key_mark_value(st_data_t key, st_data_t value, st_data_t data)
{
    rb_objspace_t *objspace = (rb_objspace_t *)data;

    gc_mark_and_pin(objspace, (VALUE)key);
    gc_mark(objspace, (VALUE)value);
    return ST_CONTINUE;
}

static void
mark_hash(rb_objspace_t *objspace, VALUE hash)
{
    if (rb_hash_compare_by_id_p(hash)) {
        rb_hash_stlike_foreach(hash, pin_key_mark_value, (st_data_t)objspace);
    }
    else {
        rb_hash_stlike_foreach(hash, mark_keyvalue, (st_data_t)objspace);
    }

    gc_mark(objspace, RHASH(hash)->ifnone);
}

static void
mark_st(rb_objspace_t *objspace, st_table *tbl)
{
    if (!tbl) return;
    st_foreach(tbl, pin_key_pin_value, (st_data_t)objspace);
}

void
rb_mark_hash(st_table *tbl)
{
    mark_st(&rb_objspace, tbl);
}

static enum rb_id_table_iterator_result
mark_method_entry_i(VALUE me, void *data)
{
    rb_objspace_t *objspace = (rb_objspace_t *)data;

    gc_mark(objspace, me);
    return ID_TABLE_CONTINUE;
}

static void
mark_m_tbl(rb_objspace_t *objspace, struct rb_id_table *tbl)
{
    if (tbl) {
        rb_id_table_foreach_values(tbl, mark_method_entry_i, objspace);
    }
}

static enum rb_id_table_iterator_result
mark_const_entry_i(VALUE value, void *data)
{
    const rb_const_entry_t *ce = (const rb_const_entry_t *)value;
    rb_objspace_t *objspace = data;

    gc_mark(objspace, ce->value);
    gc_mark(objspace, ce->file);
    return ID_TABLE_CONTINUE;
}

static void
mark_const_tbl(rb_objspace_t *objspace, struct rb_id_table *tbl)
{
    if (!tbl) return;
    rb_id_table_foreach_values(tbl, mark_const_entry_i, objspace);
}

#if STACK_GROW_DIRECTION < 0
#define GET_STACK_BOUNDS(start, end, appendix) ((start) = STACK_END, (end) = STACK_START)
#elif STACK_GROW_DIRECTION > 0
#define GET_STACK_BOUNDS(start, end, appendix) ((start) = STACK_START, (end) = STACK_END+(appendix))
#else
#define GET_STACK_BOUNDS(start, end, appendix) \
    ((STACK_END < STACK_START) ? \
     ((start) = STACK_END, (end) = STACK_START) : ((start) = STACK_START, (end) = STACK_END+(appendix)))
#endif

static void each_stack_location(rb_objspace_t *objspace, const rb_execution_context_t *ec,
                                 const VALUE *stack_start, const VALUE *stack_end, void (*cb)(rb_objspace_t *, VALUE));

static void
gc_mark_machine_stack_location_maybe(rb_objspace_t *objspace, VALUE obj)
{
    gc_mark_maybe(objspace, obj);

#ifdef RUBY_ASAN_ENABLED
    rb_execution_context_t *ec = objspace->marking_machine_context_ec;
    void *fake_frame_start;
    void *fake_frame_end;
    bool is_fake_frame = asan_get_fake_stack_extents(
        ec->thread_ptr->asan_fake_stack_handle, obj,
        ec->machine.stack_start, ec->machine.stack_end,
        &fake_frame_start, &fake_frame_end
    );
    if (is_fake_frame) {
        each_stack_location(objspace, ec, fake_frame_start, fake_frame_end, gc_mark_maybe);
    }
#endif
}

#if defined(__wasm__)


static VALUE *rb_stack_range_tmp[2];

static void
rb_mark_locations(void *begin, void *end)
{
    rb_stack_range_tmp[0] = begin;
    rb_stack_range_tmp[1] = end;
}

# if defined(__EMSCRIPTEN__)

static void
mark_current_machine_context(rb_objspace_t *objspace, rb_execution_context_t *ec)
{
    emscripten_scan_stack(rb_mark_locations);
    each_stack_location(objspace, ec, rb_stack_range_tmp[0], rb_stack_range_tmp[1], gc_mark_maybe);

    emscripten_scan_registers(rb_mark_locations);
    each_stack_location(objspace, ec, rb_stack_range_tmp[0], rb_stack_range_tmp[1], gc_mark_maybe);
}
# else // use Asyncify version

static void
mark_current_machine_context(rb_objspace_t *objspace, rb_execution_context_t *ec)
{
    VALUE *stack_start, *stack_end;
    SET_STACK_END;
    GET_STACK_BOUNDS(stack_start, stack_end, 1);
    each_stack_location(objspace, ec, stack_start, stack_end, gc_mark_maybe);

    rb_wasm_scan_locals(rb_mark_locations);
    each_stack_location(objspace, ec, rb_stack_range_tmp[0], rb_stack_range_tmp[1], gc_mark_maybe);
}

# endif

#else // !defined(__wasm__)

static void
mark_current_machine_context(rb_objspace_t *objspace, rb_execution_context_t *ec)
{
    union {
        rb_jmp_buf j;
        VALUE v[sizeof(rb_jmp_buf) / (sizeof(VALUE))];
    } save_regs_gc_mark;
    VALUE *stack_start, *stack_end;

    FLUSH_REGISTER_WINDOWS;
    memset(&save_regs_gc_mark, 0, sizeof(save_regs_gc_mark));
    /* This assumes that all registers are saved into the jmp_buf (and stack) */
    rb_setjmp(save_regs_gc_mark.j);

    /* SET_STACK_END must be called in this function because
     * the stack frame of this function may contain
     * callee save registers and they should be marked. */
    SET_STACK_END;
    GET_STACK_BOUNDS(stack_start, stack_end, 1);

#ifdef RUBY_ASAN_ENABLED
    objspace->marking_machine_context_ec = ec;
#endif

    each_location(objspace, save_regs_gc_mark.v, numberof(save_regs_gc_mark.v), gc_mark_machine_stack_location_maybe);
    each_stack_location(objspace, ec, stack_start, stack_end, gc_mark_machine_stack_location_maybe);

#ifdef RUBY_ASAN_ENABLED
    objspace->marking_machine_context_ec = NULL;
#endif
}
#endif

void
rb_gc_mark_machine_stack(const rb_execution_context_t *ec)
{
    VALUE *stack_start, *stack_end;
    GET_STACK_BOUNDS(stack_start, stack_end, 0);
    RUBY_DEBUG_LOG("ec->th:%u stack_start:%p stack_end:%p", rb_ec_thread_ptr(ec)->serial, stack_start, stack_end);

    rb_gc_mark_locations(stack_start, stack_end);
}

void
rb_gc_mark_machine_context(const rb_execution_context_t *ec)
{
    rb_objspace_t *objspace = &rb_objspace;
#ifdef RUBY_ASAN_ENABLED
    objspace->marking_machine_context_ec = ec;
#endif

    VALUE *stack_start, *stack_end;

    GET_STACK_BOUNDS(stack_start, stack_end, 0);
    RUBY_DEBUG_LOG("ec->th:%u stack_start:%p stack_end:%p", rb_ec_thread_ptr(ec)->serial, stack_start, stack_end);

    each_stack_location(objspace, ec, stack_start, stack_end, gc_mark_machine_stack_location_maybe);
    int num_regs = sizeof(ec->machine.regs)/(sizeof(VALUE));
    each_location(objspace, (VALUE*)&ec->machine.regs, num_regs, gc_mark_machine_stack_location_maybe);

#ifdef RUBY_ASAN_ENABLED
    objspace->marking_machine_context_ec = NULL;
#endif
}

static void
each_stack_location(rb_objspace_t *objspace, const rb_execution_context_t *ec,
                     const VALUE *stack_start, const VALUE *stack_end, void (*cb)(rb_objspace_t *, VALUE))
{

    gc_mark_locations(objspace, stack_start, stack_end, cb);

#if defined(__mc68000__)
    gc_mark_locations(objspace,
                      (VALUE*)((char*)stack_start + 2),
                      (VALUE*)((char*)stack_end - 2), cb);
#endif
}

void
rb_mark_tbl(st_table *tbl)
{
    mark_tbl(&rb_objspace, tbl);
}

void
rb_mark_tbl_no_pin(st_table *tbl)
{
    mark_tbl_no_pin(&rb_objspace, tbl);
}

static void
gc_mark_maybe(rb_objspace_t *objspace, VALUE obj)
{
    (void)VALGRIND_MAKE_MEM_DEFINED(&obj, sizeof(obj));

    if (is_pointer_to_heap(objspace, (void *)obj)) {
        void *ptr = asan_unpoison_object_temporary(obj);

        /* Garbage can live on the stack, so do not mark or pin */
        switch (BUILTIN_TYPE(obj)) {
          case T_ZOMBIE:
          case T_NONE:
            break;
          default:
            gc_mark_and_pin(objspace, obj);
            break;
        }

        if (ptr) {
            GC_ASSERT(BUILTIN_TYPE(obj) == T_NONE);
            asan_poison_object(obj);
        }
    }
}

void
rb_gc_mark_maybe(VALUE obj)
{
    gc_mark_maybe(&rb_objspace, obj);
}

static inline int
gc_mark_set(rb_objspace_t *objspace, VALUE obj)
{
    ASSERT_vm_locking();
    if (RVALUE_MARKED(obj)) return 0;
    MARK_IN_BITMAP(GET_HEAP_MARK_BITS(obj), obj);
    return 1;
}

static int
gc_remember_unprotected(rb_objspace_t *objspace, VALUE obj)
{
    struct heap_page *page = GET_HEAP_PAGE(obj);
    bits_t *uncollectible_bits = &page->uncollectible_bits[0];

    if (!MARKED_IN_BITMAP(uncollectible_bits, obj)) {
        page->flags.has_uncollectible_wb_unprotected_objects = TRUE;
        MARK_IN_BITMAP(uncollectible_bits, obj);
        objspace->rgengc.uncollectible_wb_unprotected_objects++;

#if RGENGC_PROFILE > 0
        objspace->profile.total_remembered_shady_object_count++;
#if RGENGC_PROFILE >= 2
        objspace->profile.remembered_shady_object_count_types[BUILTIN_TYPE(obj)]++;
#endif
#endif
        return TRUE;
    }
    else {
        return FALSE;
    }
}

static void
rgengc_check_relation(rb_objspace_t *objspace, VALUE obj)
{
    const VALUE old_parent = objspace->rgengc.parent_object;

    if (old_parent) { /* parent object is old */
        if (RVALUE_WB_UNPROTECTED(obj) || !RVALUE_OLD_P(obj)) {
            rgengc_remember(objspace, old_parent);
        }
    }

    GC_ASSERT(old_parent == objspace->rgengc.parent_object);
}

static void
gc_grey(rb_objspace_t *objspace, VALUE obj)
{
#if RGENGC_CHECK_MODE
    if (RVALUE_MARKED(obj) == FALSE) rb_bug("gc_grey: %s is not marked.", obj_info(obj));
    if (RVALUE_MARKING(obj) == TRUE) rb_bug("gc_grey: %s is marking/remembered.", obj_info(obj));
#endif

    if (is_incremental_marking(objspace)) {
        MARK_IN_BITMAP(GET_HEAP_MARKING_BITS(obj), obj);
    }

    push_mark_stack(&objspace->mark_stack, obj);
}

static void
gc_aging(rb_objspace_t *objspace, VALUE obj)
{
    struct heap_page *page = GET_HEAP_PAGE(obj);

    GC_ASSERT(RVALUE_MARKING(obj) == FALSE);
    check_rvalue_consistency(obj);

    if (!RVALUE_PAGE_WB_UNPROTECTED(page, obj)) {
        if (!RVALUE_OLD_P(obj)) {
            gc_report(3, objspace, "gc_aging: YOUNG: %s\n", obj_info(obj));
            RVALUE_AGE_INC(objspace, obj);
        }
        else if (is_full_marking(objspace)) {
            GC_ASSERT(RVALUE_PAGE_UNCOLLECTIBLE(page, obj) == FALSE);
            RVALUE_PAGE_OLD_UNCOLLECTIBLE_SET(objspace, page, obj);
        }
    }
    check_rvalue_consistency(obj);

    objspace->marked_slots++;
}

NOINLINE(static void gc_mark_ptr(rb_objspace_t *objspace, VALUE obj));
static void reachable_objects_from_callback(VALUE obj);

static void
gc_mark_ptr(rb_objspace_t *objspace, VALUE obj)
{
    if (LIKELY(during_gc)) {
        rgengc_check_relation(objspace, obj);
        if (!gc_mark_set(objspace, obj)) return; /* already marked */

        if (0) { // for debug GC marking miss
            if (objspace->rgengc.parent_object) {
                RUBY_DEBUG_LOG("%p (%s) parent:%p (%s)",
                               (void *)obj, obj_type_name(obj),
                               (void *)objspace->rgengc.parent_object, obj_type_name(objspace->rgengc.parent_object));
            }
            else {
                RUBY_DEBUG_LOG("%p (%s)", (void *)obj, obj_type_name(obj));
            }
        }

        if (UNLIKELY(RB_TYPE_P(obj, T_NONE))) {
            rp(obj);
            rb_bug("try to mark T_NONE object"); /* check here will help debugging */
        }
        gc_aging(objspace, obj);
        gc_grey(objspace, obj);
    }
    else {
        reachable_objects_from_callback(obj);
    }
}

static inline void
gc_pin(rb_objspace_t *objspace, VALUE obj)
{
    GC_ASSERT(is_markable_object(obj));
    if (UNLIKELY(objspace->flags.during_compacting)) {
        if (LIKELY(during_gc)) {
            if (!MARKED_IN_BITMAP(GET_HEAP_PINNED_BITS(obj), obj)) {
                GC_ASSERT(GET_HEAP_PAGE(obj)->pinned_slots <= GET_HEAP_PAGE(obj)->total_slots);
                GET_HEAP_PAGE(obj)->pinned_slots++;
                MARK_IN_BITMAP(GET_HEAP_PINNED_BITS(obj), obj);
            }
        }
    }
}

static inline void
gc_mark_and_pin(rb_objspace_t *objspace, VALUE obj)
{
    if (!is_markable_object(obj)) return;
    gc_pin(objspace, obj);
    gc_mark_ptr(objspace, obj);
}

static inline void
gc_mark(rb_objspace_t *objspace, VALUE obj)
{
    if (!is_markable_object(obj)) return;
    gc_mark_ptr(objspace, obj);
}

void
rb_gc_mark_movable(VALUE ptr)
{
    gc_mark(&rb_objspace, ptr);
}

void
rb_gc_mark(VALUE ptr)
{
    gc_mark_and_pin(&rb_objspace, ptr);
}

void
rb_gc_mark_and_move(VALUE *ptr)
{
    rb_objspace_t *objspace = &rb_objspace;
    if (RB_SPECIAL_CONST_P(*ptr)) return;

    if (UNLIKELY(objspace->flags.during_reference_updating)) {
        GC_ASSERT(objspace->flags.during_compacting);
        GC_ASSERT(during_gc);

        *ptr = rb_gc_location(*ptr);
    }
    else {
        gc_mark_ptr(objspace, *ptr);
    }
}

void
rb_gc_mark_weak(VALUE *ptr)
{
    rb_objspace_t *objspace = &rb_objspace;

    if (UNLIKELY(!during_gc)) return;

    VALUE obj = *ptr;
    if (RB_SPECIAL_CONST_P(obj)) return;

    GC_ASSERT(objspace->rgengc.parent_object == 0 || FL_TEST(objspace->rgengc.parent_object, FL_WB_PROTECTED));

    if (UNLIKELY(RB_TYPE_P(obj, T_NONE))) {
        rp(obj);
        rb_bug("try to mark T_NONE object");
    }

    /* If we are in a minor GC and the other object is old, then obj should
     * already be marked and cannot be reclaimed in this GC cycle so we don't
     * need to add it to the weak refences list. */
    if (!is_full_marking(objspace) && RVALUE_OLD_P(obj)) {
        GC_ASSERT(RVALUE_MARKED(obj));
        GC_ASSERT(!objspace->flags.during_compacting);

        return;
    }

    rgengc_check_relation(objspace, obj);

    rb_darray_append_without_gc(&objspace->weak_references, ptr);

    objspace->profile.weak_references_count++;
}

void
rb_gc_remove_weak(VALUE parent_obj, VALUE *ptr)
{
    rb_objspace_t *objspace = &rb_objspace;

    /* If we're not incremental marking, then the state of the objects can't
     * change so we don't need to do anything. */
    if (!is_incremental_marking(objspace)) return;
    /* If parent_obj has not been marked, then ptr has not yet been marked
     * weak, so we don't need to do anything. */
    if (!RVALUE_MARKED(parent_obj)) return;

    VALUE **ptr_ptr;
    rb_darray_foreach(objspace->weak_references, i, ptr_ptr) {
        if (*ptr_ptr == ptr) {
            *ptr_ptr = NULL;
            break;
        }
    }
}

static inline void
gc_mark_set_parent(rb_objspace_t *objspace, VALUE obj)
{
    if (RVALUE_OLD_P(obj)) {
        objspace->rgengc.parent_object = obj;
    }
    else {
        objspace->rgengc.parent_object = Qfalse;
    }
}

static bool
gc_declarative_marking_p(const rb_data_type_t *type)
{
    return (type->flags & RUBY_TYPED_DECL_MARKING) != 0;
}

static void mark_cvc_tbl(rb_objspace_t *objspace, VALUE klass);

static void
gc_mark_children(rb_objspace_t *objspace, VALUE obj)
{
    register RVALUE *any = RANY(obj);
    gc_mark_set_parent(objspace, obj);

    if (FL_TEST(obj, FL_EXIVAR)) {
        rb_mark_generic_ivar(obj);
    }

    switch (BUILTIN_TYPE(obj)) {
      case T_FLOAT:
      case T_BIGNUM:
      case T_SYMBOL:
        /* Not immediates, but does not have references and singleton class.
         *
         * RSYMBOL(obj)->fstr intentionally not marked. See log for 96815f1e
         * ("symbol.c: remove rb_gc_mark_symbols()") */
        return;

      case T_NIL:
      case T_FIXNUM:
        rb_bug("rb_gc_mark() called for broken object");
        break;

      case T_NODE:
        UNEXPECTED_NODE(rb_gc_mark);
        break;

      case T_IMEMO:
        rb_imemo_mark_and_move(obj, false);
        return;

      default:
        break;
    }

    gc_mark(objspace, any->as.basic.klass);

    switch (BUILTIN_TYPE(obj)) {
      case T_CLASS:
        if (FL_TEST(obj, FL_SINGLETON)) {
            gc_mark(objspace, RCLASS_ATTACHED_OBJECT(obj));
        }
        // Continue to the shared T_CLASS/T_MODULE
      case T_MODULE:
        if (RCLASS_SUPER(obj)) {
            gc_mark(objspace, RCLASS_SUPER(obj));
        }

        mark_m_tbl(objspace, RCLASS_M_TBL(obj));
        mark_cvc_tbl(objspace, obj);
        rb_cc_table_mark(obj);
        if (rb_shape_obj_too_complex(obj)) {
            mark_tbl_no_pin(objspace, (st_table *)RCLASS_IVPTR(obj));
        }
        else {
            for (attr_index_t i = 0; i < RCLASS_IV_COUNT(obj); i++) {
                gc_mark(objspace, RCLASS_IVPTR(obj)[i]);
            }
        }
        mark_const_tbl(objspace, RCLASS_CONST_TBL(obj));

        gc_mark(objspace, RCLASS_EXT(obj)->classpath);
        break;

      case T_ICLASS:
        if (RICLASS_OWNS_M_TBL_P(obj)) {
            mark_m_tbl(objspace, RCLASS_M_TBL(obj));
        }
        if (RCLASS_SUPER(obj)) {
            gc_mark(objspace, RCLASS_SUPER(obj));
        }

        if (RCLASS_INCLUDER(obj)) {
            gc_mark(objspace, RCLASS_INCLUDER(obj));
        }
        mark_m_tbl(objspace, RCLASS_CALLABLE_M_TBL(obj));
        rb_cc_table_mark(obj);
        break;

      case T_ARRAY:
        if (ARY_SHARED_P(obj)) {
            VALUE root = ARY_SHARED_ROOT(obj);
            gc_mark(objspace, root);
        }
        else {
            long i, len = RARRAY_LEN(obj);
            const VALUE *ptr = RARRAY_CONST_PTR(obj);
            for (i=0; i < len; i++) {
                gc_mark(objspace, ptr[i]);
            }
        }
        break;

      case T_HASH:
        mark_hash(objspace, obj);
        break;

      case T_STRING:
        if (STR_SHARED_P(obj)) {
            if (STR_EMBED_P(any->as.string.as.heap.aux.shared)) {
                /* Embedded shared strings cannot be moved because this string
                 * points into the slot of the shared string. There may be code
                 * using the RSTRING_PTR on the stack, which would pin this
                 * string but not pin the shared string, causing it to move. */
                gc_mark_and_pin(objspace, any->as.string.as.heap.aux.shared);
            }
            else {
                gc_mark(objspace, any->as.string.as.heap.aux.shared);
            }
        }
        break;

      case T_DATA:
        {
            void *const ptr = RTYPEDDATA_P(obj) ? RTYPEDDATA_GET_DATA(obj) : DATA_PTR(obj);

            if (ptr) {
                if (RTYPEDDATA_P(obj) && gc_declarative_marking_p(any->as.typeddata.type)) {
                    size_t *offset_list = (size_t *)RANY(obj)->as.typeddata.type->function.dmark;

                    for (size_t offset = *offset_list; offset != RUBY_REF_END; offset = *offset_list++) {
                        rb_gc_mark_movable(*(VALUE *)((char *)ptr + offset));
                    }
                }
                else {
                    RUBY_DATA_FUNC mark_func = RTYPEDDATA_P(obj) ?
                        any->as.typeddata.type->function.dmark :
                        any->as.data.dmark;
                    if (mark_func) (*mark_func)(ptr);
                }
            }
        }
        break;

      case T_OBJECT:
        {
            rb_shape_t *shape = rb_shape_get_shape_by_id(ROBJECT_SHAPE_ID(obj));
            if (rb_shape_obj_too_complex(obj)) {
                mark_tbl_no_pin(objspace, ROBJECT_IV_HASH(obj));
            }
            else {
                const VALUE * const ptr = ROBJECT_IVPTR(obj);

                uint32_t i, len = ROBJECT_IV_COUNT(obj);
                for (i  = 0; i < len; i++) {
                    gc_mark(objspace, ptr[i]);
                }
            }
            if (shape) {
                VALUE klass = RBASIC_CLASS(obj);

                // Increment max_iv_count if applicable, used to determine size pool allocation
                attr_index_t num_of_ivs = shape->next_iv_index;
                if (RCLASS_EXT(klass)->max_iv_count < num_of_ivs) {
                    RCLASS_EXT(klass)->max_iv_count = num_of_ivs;
                }
            }
        }
        break;

      case T_FILE:
        if (any->as.file.fptr) {
            gc_mark(objspace, any->as.file.fptr->self);
            gc_mark(objspace, any->as.file.fptr->pathv);
            gc_mark(objspace, any->as.file.fptr->tied_io_for_writing);
            gc_mark(objspace, any->as.file.fptr->writeconv_asciicompat);
            gc_mark(objspace, any->as.file.fptr->writeconv_pre_ecopts);
            gc_mark(objspace, any->as.file.fptr->encs.ecopts);
            gc_mark(objspace, any->as.file.fptr->write_lock);
            gc_mark(objspace, any->as.file.fptr->timeout);
        }
        break;

      case T_REGEXP:
        gc_mark(objspace, any->as.regexp.src);
        break;

      case T_MATCH:
        gc_mark(objspace, any->as.match.regexp);
        if (any->as.match.str) {
            gc_mark(objspace, any->as.match.str);
        }
        break;

      case T_RATIONAL:
        gc_mark(objspace, any->as.rational.num);
        gc_mark(objspace, any->as.rational.den);
        break;

      case T_COMPLEX:
        gc_mark(objspace, any->as.complex.real);
        gc_mark(objspace, any->as.complex.imag);
        break;

      case T_STRUCT:
        {
            long i;
            const long len = RSTRUCT_LEN(obj);
            const VALUE * const ptr = RSTRUCT_CONST_PTR(obj);

            for (i=0; i<len; i++) {
                gc_mark(objspace, ptr[i]);
            }
        }
        break;

      default:
#if GC_DEBUG
        rb_gcdebug_print_obj_condition((VALUE)obj);
#endif
        if (BUILTIN_TYPE(obj) == T_MOVED)   rb_bug("rb_gc_mark(): %p is T_MOVED", (void *)obj);
        if (BUILTIN_TYPE(obj) == T_NONE)   rb_bug("rb_gc_mark(): %p is T_NONE", (void *)obj);
        if (BUILTIN_TYPE(obj) == T_ZOMBIE) rb_bug("rb_gc_mark(): %p is T_ZOMBIE", (void *)obj);
        rb_bug("rb_gc_mark(): unknown data type 0x%x(%p) %s",
               BUILTIN_TYPE(obj), (void *)any,
               is_pointer_to_heap(objspace, any) ? "corrupted object" : "non object");
    }
}

/**
 * incremental: 0 -> not incremental (do all)
 * incremental: n -> mark at most `n' objects
 */
static inline int
gc_mark_stacked_objects(rb_objspace_t *objspace, int incremental, size_t count)
{
    mark_stack_t *mstack = &objspace->mark_stack;
    VALUE obj;
    size_t marked_slots_at_the_beginning = objspace->marked_slots;
    size_t popped_count = 0;

    while (pop_mark_stack(mstack, &obj)) {
        if (UNDEF_P(obj)) continue; /* skip */

        if (RGENGC_CHECK_MODE && !RVALUE_MARKED(obj)) {
            rb_bug("gc_mark_stacked_objects: %s is not marked.", obj_info(obj));
        }
        gc_mark_children(objspace, obj);

        if (incremental) {
            if (RGENGC_CHECK_MODE && !RVALUE_MARKING(obj)) {
                rb_bug("gc_mark_stacked_objects: incremental, but marking bit is 0");
            }
            CLEAR_IN_BITMAP(GET_HEAP_MARKING_BITS(obj), obj);
            popped_count++;

            if (popped_count + (objspace->marked_slots - marked_slots_at_the_beginning) > count) {
                break;
            }
        }
        else {
            /* just ignore marking bits */
        }
    }

    if (RGENGC_CHECK_MODE >= 3) gc_verify_internal_consistency(objspace);

    if (is_mark_stack_empty(mstack)) {
        shrink_stack_chunk_cache(mstack);
        return TRUE;
    }
    else {
        return FALSE;
    }
}

static int
gc_mark_stacked_objects_incremental(rb_objspace_t *objspace, size_t count)
{
    return gc_mark_stacked_objects(objspace, TRUE, count);
}

static int
gc_mark_stacked_objects_all(rb_objspace_t *objspace)
{
    return gc_mark_stacked_objects(objspace, FALSE, 0);
}

#if PRINT_ROOT_TICKS
#define MAX_TICKS 0x100
static tick_t mark_ticks[MAX_TICKS];
static const char *mark_ticks_categories[MAX_TICKS];

static void
show_mark_ticks(void)
{
    int i;
    fprintf(stderr, "mark ticks result:\n");
    for (i=0; i<MAX_TICKS; i++) {
        const char *category = mark_ticks_categories[i];
        if (category) {
            fprintf(stderr, "%s\t%8lu\n", category, (unsigned long)mark_ticks[i]);
        }
        else {
            break;
        }
    }
}

#endif /* PRINT_ROOT_TICKS */

static void
gc_mark_roots(rb_objspace_t *objspace, const char **categoryp)
{
    rb_execution_context_t *ec = GET_EC();
    rb_vm_t *vm = rb_ec_vm_ptr(ec);

#if PRINT_ROOT_TICKS
    tick_t start_tick = tick();
    int tick_count = 0;
    const char *prev_category = 0;

    if (mark_ticks_categories[0] == 0) {
        atexit(show_mark_ticks);
    }
#endif

    if (categoryp) *categoryp = "xxx";

    objspace->rgengc.parent_object = Qfalse;

#if PRINT_ROOT_TICKS
#define MARK_CHECKPOINT_PRINT_TICK(category) do { \
    if (prev_category) { \
        tick_t t = tick(); \
        mark_ticks[tick_count] = t - start_tick; \
        mark_ticks_categories[tick_count] = prev_category; \
        tick_count++; \
    } \
    prev_category = category; \
    start_tick = tick(); \
} while (0)
#else /* PRINT_ROOT_TICKS */
#define MARK_CHECKPOINT_PRINT_TICK(category)
#endif

#define MARK_CHECKPOINT(category) do { \
    if (categoryp) *categoryp = category; \
    MARK_CHECKPOINT_PRINT_TICK(category); \
} while (0)

    MARK_CHECKPOINT("vm");
    SET_STACK_END;
    rb_vm_mark(vm);
    if (vm->self) gc_mark(objspace, vm->self);

    MARK_CHECKPOINT("finalizers");
    mark_finalizer_tbl(objspace, finalizer_table);

    MARK_CHECKPOINT("machine_context");
    mark_current_machine_context(objspace, ec);

    /* mark protected global variables */

    MARK_CHECKPOINT("end_proc");
    rb_mark_end_proc();

    MARK_CHECKPOINT("global_tbl");
    rb_gc_mark_global_tbl();

    MARK_CHECKPOINT("object_id");
    rb_gc_mark(objspace->next_object_id);
    mark_tbl_no_pin(objspace, objspace->obj_to_id_tbl); /* Only mark ids */

    if (stress_to_class) rb_gc_mark(stress_to_class);

    MARK_CHECKPOINT("finish");
#undef MARK_CHECKPOINT
}

#if RGENGC_CHECK_MODE >= 4

#define MAKE_ROOTSIG(obj) (((VALUE)(obj) << 1) | 0x01)
#define IS_ROOTSIG(obj)   ((VALUE)(obj) & 0x01)
#define GET_ROOTSIG(obj)  ((const char *)((VALUE)(obj) >> 1))

struct reflist {
    VALUE *list;
    int pos;
    int size;
};

static struct reflist *
reflist_create(VALUE obj)
{
    struct reflist *refs = xmalloc(sizeof(struct reflist));
    refs->size = 1;
    refs->list = ALLOC_N(VALUE, refs->size);
    refs->list[0] = obj;
    refs->pos = 1;
    return refs;
}

static void
reflist_destruct(struct reflist *refs)
{
    xfree(refs->list);
    xfree(refs);
}

static void
reflist_add(struct reflist *refs, VALUE obj)
{
    if (refs->pos == refs->size) {
        refs->size *= 2;
        SIZED_REALLOC_N(refs->list, VALUE, refs->size, refs->size/2);
    }

    refs->list[refs->pos++] = obj;
}

static void
reflist_dump(struct reflist *refs)
{
    int i;
    for (i=0; i<refs->pos; i++) {
        VALUE obj = refs->list[i];
        if (IS_ROOTSIG(obj)) { /* root */
            fprintf(stderr, "<root@%s>", GET_ROOTSIG(obj));
        }
        else {
            fprintf(stderr, "<%s>", obj_info(obj));
        }
        if (i+1 < refs->pos) fprintf(stderr, ", ");
    }
}

static int
reflist_referred_from_machine_context(struct reflist *refs)
{
    int i;
    for (i=0; i<refs->pos; i++) {
        VALUE obj = refs->list[i];
        if (IS_ROOTSIG(obj) && strcmp(GET_ROOTSIG(obj), "machine_context") == 0) return 1;
    }
    return 0;
}

struct allrefs {
    rb_objspace_t *objspace;
    /* a -> obj1
     * b -> obj1
     * c -> obj1
     * c -> obj2
     * d -> obj3
     * #=> {obj1 => [a, b, c], obj2 => [c, d]}
     */
    struct st_table *references;
    const char *category;
    VALUE root_obj;
    mark_stack_t mark_stack;
};

static int
allrefs_add(struct allrefs *data, VALUE obj)
{
    struct reflist *refs;
    st_data_t r;

    if (st_lookup(data->references, obj, &r)) {
        refs = (struct reflist *)r;
        reflist_add(refs, data->root_obj);
        return 0;
    }
    else {
        refs = reflist_create(data->root_obj);
        st_insert(data->references, obj, (st_data_t)refs);
        return 1;
    }
}

static void
allrefs_i(VALUE obj, void *ptr)
{
    struct allrefs *data = (struct allrefs *)ptr;

    if (allrefs_add(data, obj)) {
        push_mark_stack(&data->mark_stack, obj);
    }
}

static void
allrefs_roots_i(VALUE obj, void *ptr)
{
    struct allrefs *data = (struct allrefs *)ptr;
    if (strlen(data->category) == 0) rb_bug("!!!");
    data->root_obj = MAKE_ROOTSIG(data->category);

    if (allrefs_add(data, obj)) {
        push_mark_stack(&data->mark_stack, obj);
    }
}
#define PUSH_MARK_FUNC_DATA(v) do { \
    struct gc_mark_func_data_struct *prev_mark_func_data = GET_RACTOR()->mfd; \
    GET_RACTOR()->mfd = (v);

#define POP_MARK_FUNC_DATA() GET_RACTOR()->mfd = prev_mark_func_data;} while (0)

static st_table *
objspace_allrefs(rb_objspace_t *objspace)
{
    struct allrefs data;
    struct gc_mark_func_data_struct mfd;
    VALUE obj;
    int prev_dont_gc = dont_gc_val();
    dont_gc_on();

    data.objspace = objspace;
    data.references = st_init_numtable();
    init_mark_stack(&data.mark_stack);

    mfd.mark_func = allrefs_roots_i;
    mfd.data = &data;

    /* traverse root objects */
    PUSH_MARK_FUNC_DATA(&mfd);
    GET_RACTOR()->mfd = &mfd;
    gc_mark_roots(objspace, &data.category);
    POP_MARK_FUNC_DATA();

    /* traverse rest objects reachable from root objects */
    while (pop_mark_stack(&data.mark_stack, &obj)) {
        rb_objspace_reachable_objects_from(data.root_obj = obj, allrefs_i, &data);
    }
    free_stack_chunks(&data.mark_stack);

    dont_gc_set(prev_dont_gc);
    return data.references;
}

static int
objspace_allrefs_destruct_i(st_data_t key, st_data_t value, st_data_t ptr)
{
    struct reflist *refs = (struct reflist *)value;
    reflist_destruct(refs);
    return ST_CONTINUE;
}

static void
objspace_allrefs_destruct(struct st_table *refs)
{
    st_foreach(refs, objspace_allrefs_destruct_i, 0);
    st_free_table(refs);
}

#if RGENGC_CHECK_MODE >= 5
static int
allrefs_dump_i(st_data_t k, st_data_t v, st_data_t ptr)
{
    VALUE obj = (VALUE)k;
    struct reflist *refs = (struct reflist *)v;
    fprintf(stderr, "[allrefs_dump_i] %s <- ", obj_info(obj));
    reflist_dump(refs);
    fprintf(stderr, "\n");
    return ST_CONTINUE;
}

static void
allrefs_dump(rb_objspace_t *objspace)
{
    VALUE size = objspace->rgengc.allrefs_table->num_entries;
    fprintf(stderr, "[all refs] (size: %"PRIuVALUE")\n", size);
    st_foreach(objspace->rgengc.allrefs_table, allrefs_dump_i, 0);
}
#endif

static int
gc_check_after_marks_i(st_data_t k, st_data_t v, st_data_t ptr)
{
    VALUE obj = k;
    struct reflist *refs = (struct reflist *)v;
    rb_objspace_t *objspace = (rb_objspace_t *)ptr;

    /* object should be marked or oldgen */
    if (!MARKED_IN_BITMAP(GET_HEAP_MARK_BITS(obj), obj)) {
        fprintf(stderr, "gc_check_after_marks_i: %s is not marked and not oldgen.\n", obj_info(obj));
        fprintf(stderr, "gc_check_after_marks_i: %p is referred from ", (void *)obj);
        reflist_dump(refs);

        if (reflist_referred_from_machine_context(refs)) {
            fprintf(stderr, " (marked from machine stack).\n");
            /* marked from machine context can be false positive */
        }
        else {
            objspace->rgengc.error_count++;
            fprintf(stderr, "\n");
        }
    }
    return ST_CONTINUE;
}

static void
gc_marks_check(rb_objspace_t *objspace, st_foreach_callback_func *checker_func, const char *checker_name)
{
    size_t saved_malloc_increase = objspace->malloc_params.increase;
#if RGENGC_ESTIMATE_OLDMALLOC
    size_t saved_oldmalloc_increase = objspace->rgengc.oldmalloc_increase;
#endif
    VALUE already_disabled = rb_objspace_gc_disable(objspace);

    objspace->rgengc.allrefs_table = objspace_allrefs(objspace);

    if (checker_func) {
        st_foreach(objspace->rgengc.allrefs_table, checker_func, (st_data_t)objspace);
    }

    if (objspace->rgengc.error_count > 0) {
#if RGENGC_CHECK_MODE >= 5
        allrefs_dump(objspace);
#endif
        if (checker_name) rb_bug("%s: GC has problem.", checker_name);
    }

    objspace_allrefs_destruct(objspace->rgengc.allrefs_table);
    objspace->rgengc.allrefs_table = 0;

    if (already_disabled == Qfalse) rb_objspace_gc_enable(objspace);
    objspace->malloc_params.increase = saved_malloc_increase;
#if RGENGC_ESTIMATE_OLDMALLOC
    objspace->rgengc.oldmalloc_increase = saved_oldmalloc_increase;
#endif
}
#endif /* RGENGC_CHECK_MODE >= 4 */

struct verify_internal_consistency_struct {
    rb_objspace_t *objspace;
    int err_count;
    size_t live_object_count;
    size_t zombie_object_count;

    VALUE parent;
    size_t old_object_count;
    size_t remembered_shady_count;
};

static void
check_generation_i(const VALUE child, void *ptr)
{
    struct verify_internal_consistency_struct *data = (struct verify_internal_consistency_struct *)ptr;
    const VALUE parent = data->parent;

    if (RGENGC_CHECK_MODE) GC_ASSERT(RVALUE_OLD_P(parent));

    if (!RVALUE_OLD_P(child)) {
        if (!RVALUE_REMEMBERED(parent) &&
            !RVALUE_REMEMBERED(child) &&
            !RVALUE_UNCOLLECTIBLE(child)) {
            fprintf(stderr, "verify_internal_consistency_reachable_i: WB miss (O->Y) %s -> %s\n", obj_info(parent), obj_info(child));
            data->err_count++;
        }
    }
}

static void
check_color_i(const VALUE child, void *ptr)
{
    struct verify_internal_consistency_struct *data = (struct verify_internal_consistency_struct *)ptr;
    const VALUE parent = data->parent;

    if (!RVALUE_WB_UNPROTECTED(parent) && RVALUE_WHITE_P(child)) {
        fprintf(stderr, "verify_internal_consistency_reachable_i: WB miss (B->W) - %s -> %s\n",
                obj_info(parent), obj_info(child));
        data->err_count++;
    }
}

static void
check_children_i(const VALUE child, void *ptr)
{
    struct verify_internal_consistency_struct *data = (struct verify_internal_consistency_struct *)ptr;
    if (check_rvalue_consistency_force(child, FALSE) != 0) {
        fprintf(stderr, "check_children_i: %s has error (referenced from %s)",
                obj_info(child), obj_info(data->parent));
        rb_print_backtrace(stderr); /* C backtrace will help to debug */

        data->err_count++;
    }
}

static int
verify_internal_consistency_i(void *page_start, void *page_end, size_t stride,
                              struct verify_internal_consistency_struct *data)
{
    VALUE obj;
    rb_objspace_t *objspace = data->objspace;

    for (obj = (VALUE)page_start; obj != (VALUE)page_end; obj += stride) {
        void *poisoned = asan_unpoison_object_temporary(obj);

        if (is_live_object(objspace, obj)) {
            /* count objects */
            data->live_object_count++;
            data->parent = obj;

            /* Normally, we don't expect T_MOVED objects to be in the heap.
             * But they can stay alive on the stack, */
            if (!gc_object_moved_p(objspace, obj)) {
                /* moved slots don't have children */
                rb_objspace_reachable_objects_from(obj, check_children_i, (void *)data);
            }

            /* check health of children */
            if (RVALUE_OLD_P(obj)) data->old_object_count++;
            if (RVALUE_WB_UNPROTECTED(obj) && RVALUE_UNCOLLECTIBLE(obj)) data->remembered_shady_count++;

            if (!is_marking(objspace) && RVALUE_OLD_P(obj)) {
                /* reachable objects from an oldgen object should be old or (young with remember) */
                data->parent = obj;
                rb_objspace_reachable_objects_from(obj, check_generation_i, (void *)data);
            }

            if (is_incremental_marking(objspace)) {
                if (RVALUE_BLACK_P(obj)) {
                    /* reachable objects from black objects should be black or grey objects */
                    data->parent = obj;
                    rb_objspace_reachable_objects_from(obj, check_color_i, (void *)data);
                }
            }
        }
        else {
            if (BUILTIN_TYPE(obj) == T_ZOMBIE) {
                data->zombie_object_count++;

                if ((RBASIC(obj)->flags & ~ZOMBIE_OBJ_KEPT_FLAGS) != T_ZOMBIE) {
                    fprintf(stderr, "verify_internal_consistency_i: T_ZOMBIE has extra flags set: %s\n",
                            obj_info(obj));
                    data->err_count++;
                }

                if (!!FL_TEST(obj, FL_FINALIZE) != !!st_is_member(finalizer_table, obj)) {
                    fprintf(stderr, "verify_internal_consistency_i: FL_FINALIZE %s but %s finalizer_table: %s\n",
                            FL_TEST(obj, FL_FINALIZE) ? "set" : "not set", st_is_member(finalizer_table, obj) ? "in" : "not in",
                            obj_info(obj));
                    data->err_count++;
                }
            }
        }
        if (poisoned) {
            GC_ASSERT(BUILTIN_TYPE(obj) == T_NONE);
            asan_poison_object(obj);
        }
    }

    return 0;
}

static int
gc_verify_heap_page(rb_objspace_t *objspace, struct heap_page *page, VALUE obj)
{
    unsigned int has_remembered_shady = FALSE;
    unsigned int has_remembered_old = FALSE;
    int remembered_old_objects = 0;
    int free_objects = 0;
    int zombie_objects = 0;

    short slot_size = page->slot_size;
    uintptr_t start = (uintptr_t)page->start;
    uintptr_t end = start + page->total_slots * slot_size;

    for (uintptr_t ptr = start; ptr < end; ptr += slot_size) {
        VALUE val = (VALUE)ptr;
        void *poisoned = asan_unpoison_object_temporary(val);
        enum ruby_value_type type = BUILTIN_TYPE(val);

        if (type == T_NONE) free_objects++;
        if (type == T_ZOMBIE) zombie_objects++;
        if (RVALUE_PAGE_UNCOLLECTIBLE(page, val) && RVALUE_PAGE_WB_UNPROTECTED(page, val)) {
            has_remembered_shady = TRUE;
        }
        if (RVALUE_PAGE_MARKING(page, val)) {
            has_remembered_old = TRUE;
            remembered_old_objects++;
        }

        if (poisoned) {
            GC_ASSERT(BUILTIN_TYPE(val) == T_NONE);
            asan_poison_object(val);
        }
    }

    if (!is_incremental_marking(objspace) &&
        page->flags.has_remembered_objects == FALSE && has_remembered_old == TRUE) {

        for (uintptr_t ptr = start; ptr < end; ptr += slot_size) {
            VALUE val = (VALUE)ptr;
            if (RVALUE_PAGE_MARKING(page, val)) {
                fprintf(stderr, "marking -> %s\n", obj_info(val));
            }
        }
        rb_bug("page %p's has_remembered_objects should be false, but there are remembered old objects (%d). %s",
               (void *)page, remembered_old_objects, obj ? obj_info(obj) : "");
    }

    if (page->flags.has_uncollectible_wb_unprotected_objects == FALSE && has_remembered_shady == TRUE) {
        rb_bug("page %p's has_remembered_shady should be false, but there are remembered shady objects. %s",
               (void *)page, obj ? obj_info(obj) : "");
    }

    if (0) {
        /* free_slots may not equal to free_objects */
        if (page->free_slots != free_objects) {
            rb_bug("page %p's free_slots should be %d, but %d", (void *)page, page->free_slots, free_objects);
        }
    }
    if (page->final_slots != zombie_objects) {
        rb_bug("page %p's final_slots should be %d, but %d", (void *)page, page->final_slots, zombie_objects);
    }

    return remembered_old_objects;
}

static int
gc_verify_heap_pages_(rb_objspace_t *objspace, struct ccan_list_head *head)
{
    int remembered_old_objects = 0;
    struct heap_page *page = 0;

    ccan_list_for_each(head, page, page_node) {
        asan_unlock_freelist(page);
        RVALUE *p = page->freelist;
        while (p) {
            VALUE vp = (VALUE)p;
            VALUE prev = vp;
            asan_unpoison_object(vp, false);
            if (BUILTIN_TYPE(vp) != T_NONE) {
                fprintf(stderr, "freelist slot expected to be T_NONE but was: %s\n", obj_info(vp));
            }
            p = p->as.free.next;
            asan_poison_object(prev);
        }
        asan_lock_freelist(page);

        if (page->flags.has_remembered_objects == FALSE) {
            remembered_old_objects += gc_verify_heap_page(objspace, page, Qfalse);
        }
    }

    return remembered_old_objects;
}

static int
gc_verify_heap_pages(rb_objspace_t *objspace)
{
    int remembered_old_objects = 0;
    for (int i = 0; i < SIZE_POOL_COUNT; i++) {
        remembered_old_objects += gc_verify_heap_pages_(objspace, &(SIZE_POOL_EDEN_HEAP(&size_pools[i])->pages));
        remembered_old_objects += gc_verify_heap_pages_(objspace, &(SIZE_POOL_TOMB_HEAP(&size_pools[i])->pages));
    }
    return remembered_old_objects;
}

/*
 *  call-seq:
 *     GC.verify_internal_consistency                  -> nil
 *
 *  Verify internal consistency.
 *
 *  This method is implementation specific.
 *  Now this method checks generational consistency
 *  if RGenGC is supported.
 */
static VALUE
gc_verify_internal_consistency_m(VALUE dummy)
{
    gc_verify_internal_consistency(&rb_objspace);
    return Qnil;
}

static void
gc_verify_internal_consistency_(rb_objspace_t *objspace)
{
    struct verify_internal_consistency_struct data = {0};

    data.objspace = objspace;
    gc_report(5, objspace, "gc_verify_internal_consistency: start\n");

    /* check relations */
    for (size_t i = 0; i < heap_allocated_pages; i++) {
        struct heap_page *page = heap_pages_sorted[i];
        short slot_size = page->slot_size;

        uintptr_t start = (uintptr_t)page->start;
        uintptr_t end = start + page->total_slots * slot_size;

        verify_internal_consistency_i((void *)start, (void *)end, slot_size, &data);
    }

    if (data.err_count != 0) {
#if RGENGC_CHECK_MODE >= 5
        objspace->rgengc.error_count = data.err_count;
        gc_marks_check(objspace, NULL, NULL);
        allrefs_dump(objspace);
#endif
        rb_bug("gc_verify_internal_consistency: found internal inconsistency.");
    }

    /* check heap_page status */
    gc_verify_heap_pages(objspace);

    /* check counters */

    if (!is_lazy_sweeping(objspace) &&
        !finalizing &&
        ruby_single_main_ractor != NULL) {
        if (objspace_live_slots(objspace) != data.live_object_count) {
            fprintf(stderr, "heap_pages_final_slots: %"PRIdSIZE", total_freed_objects: %"PRIdSIZE"\n",
                    heap_pages_final_slots, total_freed_objects(objspace));
            rb_bug("inconsistent live slot number: expect %"PRIuSIZE", but %"PRIuSIZE".",
                   objspace_live_slots(objspace), data.live_object_count);
        }
    }

    if (!is_marking(objspace)) {
        if (objspace->rgengc.old_objects != data.old_object_count) {
            rb_bug("inconsistent old slot number: expect %"PRIuSIZE", but %"PRIuSIZE".",
                   objspace->rgengc.old_objects, data.old_object_count);
        }
        if (objspace->rgengc.uncollectible_wb_unprotected_objects != data.remembered_shady_count) {
            rb_bug("inconsistent number of wb unprotected objects: expect %"PRIuSIZE", but %"PRIuSIZE".",
                   objspace->rgengc.uncollectible_wb_unprotected_objects, data.remembered_shady_count);
        }
    }

    if (!finalizing) {
        size_t list_count = 0;

        {
            VALUE z = heap_pages_deferred_final;
            while (z) {
                list_count++;
                z = RZOMBIE(z)->next;
            }
        }

        if (heap_pages_final_slots != data.zombie_object_count ||
            heap_pages_final_slots != list_count) {

            rb_bug("inconsistent finalizing object count:\n"
                    "  expect %"PRIuSIZE"\n"
                    "  but    %"PRIuSIZE" zombies\n"
                    "  heap_pages_deferred_final list has %"PRIuSIZE" items.",
                    heap_pages_final_slots,
                    data.zombie_object_count,
                    list_count);
        }
    }

    gc_report(5, objspace, "gc_verify_internal_consistency: OK\n");
}

static void
gc_verify_internal_consistency(rb_objspace_t *objspace)
{
    RB_VM_LOCK_ENTER();
    {
        rb_vm_barrier(); // stop other ractors

        unsigned int prev_during_gc = during_gc;
        during_gc = FALSE; // stop gc here
        {
            gc_verify_internal_consistency_(objspace);
        }
        during_gc = prev_during_gc;
    }
    RB_VM_LOCK_LEAVE();
}

void
rb_gc_verify_internal_consistency(void)
{
    gc_verify_internal_consistency(&rb_objspace);
}

static void
heap_move_pooled_pages_to_free_pages(rb_heap_t *heap)
{
    if (heap->pooled_pages) {
        if (heap->free_pages) {
            struct heap_page *free_pages_tail = heap->free_pages;
            while (free_pages_tail->free_next) {
                free_pages_tail = free_pages_tail->free_next;
            }
            free_pages_tail->free_next = heap->pooled_pages;
        }
        else {
            heap->free_pages = heap->pooled_pages;
        }

        heap->pooled_pages = NULL;
    }
}

/* marks */

static void
gc_marks_start(rb_objspace_t *objspace, int full_mark)
{
    /* start marking */
    gc_report(1, objspace, "gc_marks_start: (%s)\n", full_mark ? "full" : "minor");
    gc_mode_transition(objspace, gc_mode_marking);

    if (full_mark) {
        size_t incremental_marking_steps = (objspace->rincgc.pooled_slots / INCREMENTAL_MARK_STEP_ALLOCATIONS) + 1;
        objspace->rincgc.step_slots = (objspace->marked_slots * 2) / incremental_marking_steps;

        if (0) fprintf(stderr, "objspace->marked_slots: %"PRIdSIZE", "
                       "objspace->rincgc.pooled_page_num: %"PRIdSIZE", "
                       "objspace->rincgc.step_slots: %"PRIdSIZE", \n",
                       objspace->marked_slots, objspace->rincgc.pooled_slots, objspace->rincgc.step_slots);
        objspace->flags.during_minor_gc = FALSE;
        if (ruby_enable_autocompact) {
            objspace->flags.during_compacting |= TRUE;
        }
        objspace->profile.major_gc_count++;
        objspace->rgengc.uncollectible_wb_unprotected_objects = 0;
        objspace->rgengc.old_objects = 0;
        objspace->rgengc.last_major_gc = objspace->profile.count;
        objspace->marked_slots = 0;

        for (int i = 0; i < SIZE_POOL_COUNT; i++) {
            rb_size_pool_t *size_pool = &size_pools[i];
            rb_heap_t *heap = SIZE_POOL_EDEN_HEAP(size_pool);
            rgengc_mark_and_rememberset_clear(objspace, heap);
            heap_move_pooled_pages_to_free_pages(heap);

            if (objspace->flags.during_compacting) {
                struct heap_page *page = NULL;

                ccan_list_for_each(&heap->pages, page, page_node) {
                    page->pinned_slots = 0;
                }
            }
        }
    }
    else {
        objspace->flags.during_minor_gc = TRUE;
        objspace->marked_slots =
          objspace->rgengc.old_objects + objspace->rgengc.uncollectible_wb_unprotected_objects; /* uncollectible objects are marked already */
        objspace->profile.minor_gc_count++;

        for (int i = 0; i < SIZE_POOL_COUNT; i++) {
            rgengc_rememberset_mark(objspace, SIZE_POOL_EDEN_HEAP(&size_pools[i]));
        }
    }

    gc_mark_roots(objspace, NULL);

    gc_report(1, objspace, "gc_marks_start: (%s) end, stack in %"PRIdSIZE"\n",
              full_mark ? "full" : "minor", mark_stack_size(&objspace->mark_stack));
}

static inline void
gc_marks_wb_unprotected_objects_plane(rb_objspace_t *objspace, uintptr_t p, bits_t bits)
{
    if (bits) {
        do {
            if (bits & 1) {
                gc_report(2, objspace, "gc_marks_wb_unprotected_objects: marked shady: %s\n", obj_info((VALUE)p));
                GC_ASSERT(RVALUE_WB_UNPROTECTED((VALUE)p));
                GC_ASSERT(RVALUE_MARKED((VALUE)p));
                gc_mark_children(objspace, (VALUE)p);
            }
            p += BASE_SLOT_SIZE;
            bits >>= 1;
        } while (bits);
    }
}

static void
gc_marks_wb_unprotected_objects(rb_objspace_t *objspace, rb_heap_t *heap)
{
    struct heap_page *page = 0;

    ccan_list_for_each(&heap->pages, page, page_node) {
        bits_t *mark_bits = page->mark_bits;
        bits_t *wbun_bits = page->wb_unprotected_bits;
        uintptr_t p = page->start;
        size_t j;

        bits_t bits = mark_bits[0] & wbun_bits[0];
        bits >>= NUM_IN_PAGE(p);
        gc_marks_wb_unprotected_objects_plane(objspace, p, bits);
        p += (BITS_BITLENGTH - NUM_IN_PAGE(p)) * BASE_SLOT_SIZE;

        for (j=1; j<HEAP_PAGE_BITMAP_LIMIT; j++) {
            bits_t bits = mark_bits[j] & wbun_bits[j];

            gc_marks_wb_unprotected_objects_plane(objspace, p, bits);
            p += BITS_BITLENGTH * BASE_SLOT_SIZE;
        }
    }

    gc_mark_stacked_objects_all(objspace);
}

static void
gc_update_weak_references(rb_objspace_t *objspace)
{
    size_t retained_weak_references_count = 0;
    VALUE **ptr_ptr;
    rb_darray_foreach(objspace->weak_references, i, ptr_ptr) {
        if (!*ptr_ptr) continue;

        VALUE obj = **ptr_ptr;

        if (RB_SPECIAL_CONST_P(obj)) continue;

        if (!RVALUE_MARKED(obj)) {
            **ptr_ptr = Qundef;
        }
        else {
            retained_weak_references_count++;
        }
    }

    objspace->profile.retained_weak_references_count = retained_weak_references_count;

    rb_darray_clear(objspace->weak_references);
    rb_darray_resize_capa_without_gc(&objspace->weak_references, retained_weak_references_count);
}

static void
gc_marks_finish(rb_objspace_t *objspace)
{
    /* finish incremental GC */
    if (is_incremental_marking(objspace)) {
        if (RGENGC_CHECK_MODE && is_mark_stack_empty(&objspace->mark_stack) == 0) {
            rb_bug("gc_marks_finish: mark stack is not empty (%"PRIdSIZE").",
                   mark_stack_size(&objspace->mark_stack));
        }

        gc_mark_roots(objspace, 0);
        while (gc_mark_stacked_objects_incremental(objspace, INT_MAX) == false);

#if RGENGC_CHECK_MODE >= 2
        if (gc_verify_heap_pages(objspace) != 0) {
            rb_bug("gc_marks_finish (incremental): there are remembered old objects.");
        }
#endif

        objspace->flags.during_incremental_marking = FALSE;
        /* check children of all marked wb-unprotected objects */
        for (int i = 0; i < SIZE_POOL_COUNT; i++) {
            gc_marks_wb_unprotected_objects(objspace, SIZE_POOL_EDEN_HEAP(&size_pools[i]));
        }
    }

    gc_update_weak_references(objspace);

#if RGENGC_CHECK_MODE >= 2
    gc_verify_internal_consistency(objspace);
#endif

#if RGENGC_CHECK_MODE >= 4
    during_gc = FALSE;
    gc_marks_check(objspace, gc_check_after_marks_i, "after_marks");
    during_gc = TRUE;
#endif

    {
        /* decide full GC is needed or not */
        size_t total_slots = heap_allocatable_slots(objspace) + heap_eden_total_slots(objspace);
        size_t sweep_slots = total_slots - objspace->marked_slots; /* will be swept slots */
        size_t max_free_slots = (size_t)(total_slots * gc_params.heap_free_slots_max_ratio);
        size_t min_free_slots = (size_t)(total_slots * gc_params.heap_free_slots_min_ratio);
        int full_marking = is_full_marking(objspace);
        const int r_cnt = GET_VM()->ractor.cnt;
        const int r_mul = r_cnt > 8 ? 8 : r_cnt; // upto 8

        GC_ASSERT(heap_eden_total_slots(objspace) >= objspace->marked_slots);

        /* Setup freeable slots. */
        size_t total_init_slots = 0;
        for (int i = 0; i < SIZE_POOL_COUNT; i++) {
            total_init_slots += gc_params.size_pool_init_slots[i] * r_mul;
        }

        if (max_free_slots < total_init_slots) {
            max_free_slots = total_init_slots;
        }

        if (sweep_slots > max_free_slots) {
            heap_pages_freeable_pages = (sweep_slots - max_free_slots) / HEAP_PAGE_OBJ_LIMIT;
        }
        else {
            heap_pages_freeable_pages = 0;
        }

        /* check free_min */
        if (min_free_slots < gc_params.heap_free_slots * r_mul) {
            min_free_slots = gc_params.heap_free_slots * r_mul;
        }

        if (sweep_slots < min_free_slots) {
            if (!full_marking) {
                if (objspace->profile.count - objspace->rgengc.last_major_gc < RVALUE_OLD_AGE) {
                    full_marking = TRUE;
                    /* do not update last_major_gc, because full marking is not done. */
                    /* goto increment; */
                }
                else {
                    gc_report(1, objspace, "gc_marks_finish: next is full GC!!)\n");
                    objspace->rgengc.need_major_gc |= GPR_FLAG_MAJOR_BY_NOFREE;
                }
            }
        }

        if (full_marking) {
            /* See the comment about RUBY_GC_HEAP_OLDOBJECT_LIMIT_FACTOR */
            const double r = gc_params.oldobject_limit_factor;
            objspace->rgengc.uncollectible_wb_unprotected_objects_limit = MAX(
                (size_t)(objspace->rgengc.uncollectible_wb_unprotected_objects * r),
                (size_t)(objspace->rgengc.old_objects * gc_params.uncollectible_wb_unprotected_objects_limit_ratio)
            );
            objspace->rgengc.old_objects_limit = (size_t)(objspace->rgengc.old_objects * r);
        }

        if (objspace->rgengc.uncollectible_wb_unprotected_objects > objspace->rgengc.uncollectible_wb_unprotected_objects_limit) {
            objspace->rgengc.need_major_gc |= GPR_FLAG_MAJOR_BY_SHADY;
        }
        if (objspace->rgengc.old_objects > objspace->rgengc.old_objects_limit) {
            objspace->rgengc.need_major_gc |= GPR_FLAG_MAJOR_BY_OLDGEN;
        }
        if (RGENGC_FORCE_MAJOR_GC) {
            objspace->rgengc.need_major_gc = GPR_FLAG_MAJOR_BY_FORCE;
        }

        gc_report(1, objspace, "gc_marks_finish (marks %"PRIdSIZE" objects, "
                  "old %"PRIdSIZE" objects, total %"PRIdSIZE" slots, "
                  "sweep %"PRIdSIZE" slots, increment: %"PRIdSIZE", next GC: %s)\n",
                  objspace->marked_slots, objspace->rgengc.old_objects, heap_eden_total_slots(objspace), sweep_slots, heap_allocatable_pages(objspace),
                  objspace->rgengc.need_major_gc ? "major" : "minor");
    }

    rb_ractor_finish_marking();

    gc_event_hook(objspace, RUBY_INTERNAL_EVENT_GC_END_MARK, 0);
}

static bool
gc_compact_heap_cursors_met_p(rb_heap_t *heap)
{
    return heap->sweeping_page == heap->compact_cursor;
}

static rb_size_pool_t *
gc_compact_destination_pool(rb_objspace_t *objspace, rb_size_pool_t *src_pool, VALUE src)
{
    size_t obj_size;
    size_t idx = 0;

    switch (BUILTIN_TYPE(src)) {
      case T_ARRAY:
        obj_size = rb_ary_size_as_embedded(src);
        break;

      case T_OBJECT:
        if (rb_shape_obj_too_complex(src)) {
            return &size_pools[0];
        }
        else {
            obj_size = rb_obj_embedded_size(ROBJECT_IV_CAPACITY(src));
        }
        break;

      case T_STRING:
        obj_size = rb_str_size_as_embedded(src);
        break;

      case T_HASH:
        obj_size = sizeof(struct RHash) + (RHASH_ST_TABLE_P(src) ? sizeof(st_table) : sizeof(ar_table));
        break;

      default:
        return src_pool;
    }

    if (rb_gc_size_allocatable_p(obj_size)){
        idx = rb_gc_size_pool_id_for_size(obj_size);
    }
    return &size_pools[idx];
}

static bool
gc_compact_move(rb_objspace_t *objspace, rb_heap_t *heap, rb_size_pool_t *size_pool, VALUE src)
{
    GC_ASSERT(BUILTIN_TYPE(src) != T_MOVED);
    GC_ASSERT(gc_is_moveable_obj(objspace, src));

    rb_size_pool_t *dest_pool = gc_compact_destination_pool(objspace, size_pool, src);
    rb_heap_t *dheap = SIZE_POOL_EDEN_HEAP(dest_pool);
    rb_shape_t *new_shape = NULL;
    rb_shape_t *orig_shape = NULL;

    if (gc_compact_heap_cursors_met_p(dheap)) {
        return dheap != heap;
    }

    if (RB_TYPE_P(src, T_OBJECT)) {
        orig_shape = rb_shape_get_shape(src);
        if (dheap != heap && !rb_shape_obj_too_complex(src)) {
            rb_shape_t *initial_shape = rb_shape_get_shape_by_id((shape_id_t)((dest_pool - size_pools) + FIRST_T_OBJECT_SHAPE_ID));
            new_shape = rb_shape_traverse_from_new_root(initial_shape, orig_shape);

            if (!new_shape) {
                dest_pool = size_pool;
                dheap = heap;
            }
        }
    }

    while (!try_move(objspace, dheap, dheap->free_pages, src)) {
        struct gc_sweep_context ctx = {
            .page = dheap->sweeping_page,
            .final_slots = 0,
            .freed_slots = 0,
            .empty_slots = 0,
        };

        /* The page of src could be partially compacted, so it may contain
         * T_MOVED. Sweeping a page may read objects on this page, so we
         * need to lock the page. */
        lock_page_body(objspace, GET_PAGE_BODY(src));
        gc_sweep_page(objspace, dheap, &ctx);
        unlock_page_body(objspace, GET_PAGE_BODY(src));

        if (dheap->sweeping_page->free_slots > 0) {
            heap_add_freepage(dheap, dheap->sweeping_page);
        }

        dheap->sweeping_page = ccan_list_next(&dheap->pages, dheap->sweeping_page, page_node);
        if (gc_compact_heap_cursors_met_p(dheap)) {
            return dheap != heap;
        }
    }

    if (orig_shape) {
        if (new_shape) {
            VALUE dest = rb_gc_location(src);
            rb_shape_set_shape(dest, new_shape);
        }
        RMOVED(src)->original_shape_id = rb_shape_id(orig_shape);
    }

    return true;
}

static bool
gc_compact_plane(rb_objspace_t *objspace, rb_size_pool_t *size_pool, rb_heap_t *heap, uintptr_t p, bits_t bitset, struct heap_page *page)
{
    short slot_size = page->slot_size;
    short slot_bits = slot_size / BASE_SLOT_SIZE;
    GC_ASSERT(slot_bits > 0);

    do {
        VALUE vp = (VALUE)p;
        GC_ASSERT(vp % sizeof(RVALUE) == 0);

        if (bitset & 1) {
            objspace->rcompactor.considered_count_table[BUILTIN_TYPE(vp)]++;

            if (gc_is_moveable_obj(objspace, vp)) {
                if (!gc_compact_move(objspace, heap, size_pool, vp)) {
                    //the cursors met. bubble up
                    return false;
                }
            }
        }
        p += slot_size;
        bitset >>= slot_bits;
    } while (bitset);

    return true;
}

// Iterate up all the objects in page, moving them to where they want to go
static bool
gc_compact_page(rb_objspace_t *objspace, rb_size_pool_t *size_pool, rb_heap_t *heap, struct heap_page *page)
{
    GC_ASSERT(page == heap->compact_cursor);

    bits_t *mark_bits, *pin_bits;
    bits_t bitset;
    uintptr_t p = page->start;

    mark_bits = page->mark_bits;
    pin_bits = page->pinned_bits;

    // objects that can be moved are marked and not pinned
    bitset = (mark_bits[0] & ~pin_bits[0]);
    bitset >>= NUM_IN_PAGE(p);
    if (bitset) {
        if (!gc_compact_plane(objspace, size_pool, heap, (uintptr_t)p, bitset, page))
            return false;
    }
    p += (BITS_BITLENGTH - NUM_IN_PAGE(p)) * BASE_SLOT_SIZE;

    for (int j = 1; j < HEAP_PAGE_BITMAP_LIMIT; j++) {
        bitset = (mark_bits[j] & ~pin_bits[j]);
        if (bitset) {
            if (!gc_compact_plane(objspace, size_pool, heap, (uintptr_t)p, bitset, page))
                return false;
        }
        p += BITS_BITLENGTH * BASE_SLOT_SIZE;
    }

    return true;
}

static bool
gc_compact_all_compacted_p(rb_objspace_t *objspace)
{
    for (int i = 0; i < SIZE_POOL_COUNT; i++) {
        rb_size_pool_t *size_pool = &size_pools[i];
        rb_heap_t *heap = SIZE_POOL_EDEN_HEAP(size_pool);

        if (heap->total_pages > 0 &&
                !gc_compact_heap_cursors_met_p(heap)) {
            return false;
        }
    }

    return true;
}

static void
gc_sweep_compact(rb_objspace_t *objspace)
{
    gc_compact_start(objspace);
#if RGENGC_CHECK_MODE >= 2
    gc_verify_internal_consistency(objspace);
#endif

    while (!gc_compact_all_compacted_p(objspace)) {
        for (int i = 0; i < SIZE_POOL_COUNT; i++) {
            rb_size_pool_t *size_pool = &size_pools[i];
            rb_heap_t *heap = SIZE_POOL_EDEN_HEAP(size_pool);

            if (gc_compact_heap_cursors_met_p(heap)) {
                continue;
            }

            struct heap_page *start_page = heap->compact_cursor;

            if (!gc_compact_page(objspace, size_pool, heap, start_page)) {
                lock_page_body(objspace, GET_PAGE_BODY(start_page->start));

                continue;
            }

            // If we get here, we've finished moving all objects on the compact_cursor page
            // So we can lock it and move the cursor on to the next one.
            lock_page_body(objspace, GET_PAGE_BODY(start_page->start));
            heap->compact_cursor = ccan_list_prev(&heap->pages, heap->compact_cursor, page_node);
        }
    }

    gc_compact_finish(objspace);

#if RGENGC_CHECK_MODE >= 2
    gc_verify_internal_consistency(objspace);
#endif
}

static void
gc_marks_rest(rb_objspace_t *objspace)
{
    gc_report(1, objspace, "gc_marks_rest\n");

    for (int i = 0; i < SIZE_POOL_COUNT; i++) {
        SIZE_POOL_EDEN_HEAP(&size_pools[i])->pooled_pages = NULL;
    }

    if (is_incremental_marking(objspace)) {
        while (gc_mark_stacked_objects_incremental(objspace, INT_MAX) == FALSE);
    }
    else {
        gc_mark_stacked_objects_all(objspace);
    }

    gc_marks_finish(objspace);
}

static bool
gc_marks(rb_objspace_t *objspace, int full_mark)
{
    gc_prof_mark_timer_start(objspace);
    gc_marking_enter(objspace);

    bool marking_finished = false;

    /* setup marking */

    gc_marks_start(objspace, full_mark);
    if (!is_incremental_marking(objspace)) {
        gc_marks_rest(objspace);
        marking_finished = true;
    }

#if RGENGC_PROFILE > 0
    if (gc_prof_record(objspace)) {
        gc_profile_record *record = gc_prof_record(objspace);
        record->old_objects = objspace->rgengc.old_objects;
    }
#endif

    gc_marking_exit(objspace);
    gc_prof_mark_timer_stop(objspace);

    return marking_finished;
}

/* RGENGC */

static void
gc_report_body(int level, rb_objspace_t *objspace, const char *fmt, ...)
{
    if (level <= RGENGC_DEBUG) {
        char buf[1024];
        FILE *out = stderr;
        va_list args;
        const char *status = " ";

        if (during_gc) {
            status = is_full_marking(objspace) ? "+" : "-";
        }
        else {
            if (is_lazy_sweeping(objspace)) {
                status = "S";
            }
            if (is_incremental_marking(objspace)) {
                status = "M";
            }
        }

        va_start(args, fmt);
        vsnprintf(buf, 1024, fmt, args);
        va_end(args);

        fprintf(out, "%s|", status);
        fputs(buf, out);
    }
}

/* bit operations */

static int
rgengc_remembersetbits_set(rb_objspace_t *objspace, VALUE obj)
{
    struct heap_page *page = GET_HEAP_PAGE(obj);
    bits_t *bits = &page->remembered_bits[0];

    if (MARKED_IN_BITMAP(bits, obj)) {
        return FALSE;
    }
    else {
        page->flags.has_remembered_objects = TRUE;
        MARK_IN_BITMAP(bits, obj);
        return TRUE;
    }
}

/* wb, etc */

/* return FALSE if already remembered */
static int
rgengc_remember(rb_objspace_t *objspace, VALUE obj)
{
    gc_report(6, objspace, "rgengc_remember: %s %s\n", obj_info(obj),
              RVALUE_REMEMBERED(obj) ? "was already remembered" : "is remembered now");

    check_rvalue_consistency(obj);

    if (RGENGC_CHECK_MODE) {
        if (RVALUE_WB_UNPROTECTED(obj)) rb_bug("rgengc_remember: %s is not wb protected.", obj_info(obj));
    }

#if RGENGC_PROFILE > 0
    if (!RVALUE_REMEMBERED(obj)) {
        if (RVALUE_WB_UNPROTECTED(obj) == 0) {
            objspace->profile.total_remembered_normal_object_count++;
#if RGENGC_PROFILE >= 2
            objspace->profile.remembered_normal_object_count_types[BUILTIN_TYPE(obj)]++;
#endif
        }
    }
#endif /* RGENGC_PROFILE > 0 */

    return rgengc_remembersetbits_set(objspace, obj);
}

#ifndef PROFILE_REMEMBERSET_MARK
#define PROFILE_REMEMBERSET_MARK 0
#endif

static inline void
rgengc_rememberset_mark_plane(rb_objspace_t *objspace, uintptr_t p, bits_t bitset)
{
    if (bitset) {
        do {
            if (bitset & 1) {
                VALUE obj = (VALUE)p;
                gc_report(2, objspace, "rgengc_rememberset_mark: mark %s\n", obj_info(obj));
                GC_ASSERT(RVALUE_UNCOLLECTIBLE(obj));
                GC_ASSERT(RVALUE_OLD_P(obj) || RVALUE_WB_UNPROTECTED(obj));

                gc_mark_children(objspace, obj);
            }
            p += BASE_SLOT_SIZE;
            bitset >>= 1;
        } while (bitset);
    }
}

static void
rgengc_rememberset_mark(rb_objspace_t *objspace, rb_heap_t *heap)
{
    size_t j;
    struct heap_page *page = 0;
#if PROFILE_REMEMBERSET_MARK
    int has_old = 0, has_shady = 0, has_both = 0, skip = 0;
#endif
    gc_report(1, objspace, "rgengc_rememberset_mark: start\n");

    ccan_list_for_each(&heap->pages, page, page_node) {
        if (page->flags.has_remembered_objects | page->flags.has_uncollectible_wb_unprotected_objects) {
            uintptr_t p = page->start;
            bits_t bitset, bits[HEAP_PAGE_BITMAP_LIMIT];
            bits_t *remembered_bits = page->remembered_bits;
            bits_t *uncollectible_bits = page->uncollectible_bits;
            bits_t *wb_unprotected_bits = page->wb_unprotected_bits;
#if PROFILE_REMEMBERSET_MARK
            if (page->flags.has_remembered_objects && page->flags.has_uncollectible_wb_unprotected_objects) has_both++;
            else if (page->flags.has_remembered_objects) has_old++;
            else if (page->flags.has_uncollectible_wb_unprotected_objects) has_shady++;
#endif
            for (j=0; j<HEAP_PAGE_BITMAP_LIMIT; j++) {
                bits[j] = remembered_bits[j] | (uncollectible_bits[j] & wb_unprotected_bits[j]);
                remembered_bits[j] = 0;
            }
            page->flags.has_remembered_objects = FALSE;

            bitset = bits[0];
            bitset >>= NUM_IN_PAGE(p);
            rgengc_rememberset_mark_plane(objspace, p, bitset);
            p += (BITS_BITLENGTH - NUM_IN_PAGE(p)) * BASE_SLOT_SIZE;

            for (j=1; j < HEAP_PAGE_BITMAP_LIMIT; j++) {
                bitset = bits[j];
                rgengc_rememberset_mark_plane(objspace, p, bitset);
                p += BITS_BITLENGTH * BASE_SLOT_SIZE;
            }
        }
#if PROFILE_REMEMBERSET_MARK
        else {
            skip++;
        }
#endif
    }

#if PROFILE_REMEMBERSET_MARK
    fprintf(stderr, "%d\t%d\t%d\t%d\n", has_both, has_old, has_shady, skip);
#endif
    gc_report(1, objspace, "rgengc_rememberset_mark: finished\n");
}

static void
rgengc_mark_and_rememberset_clear(rb_objspace_t *objspace, rb_heap_t *heap)
{
    struct heap_page *page = 0;

    ccan_list_for_each(&heap->pages, page, page_node) {
        memset(&page->mark_bits[0],       0, HEAP_PAGE_BITMAP_SIZE);
        memset(&page->uncollectible_bits[0], 0, HEAP_PAGE_BITMAP_SIZE);
        memset(&page->marking_bits[0],    0, HEAP_PAGE_BITMAP_SIZE);
        memset(&page->remembered_bits[0], 0, HEAP_PAGE_BITMAP_SIZE);
        memset(&page->pinned_bits[0],     0, HEAP_PAGE_BITMAP_SIZE);
        page->flags.has_uncollectible_wb_unprotected_objects = FALSE;
        page->flags.has_remembered_objects = FALSE;
    }
}

/* RGENGC: APIs */

NOINLINE(static void gc_writebarrier_generational(VALUE a, VALUE b, rb_objspace_t *objspace));

static void
gc_writebarrier_generational(VALUE a, VALUE b, rb_objspace_t *objspace)
{
    if (RGENGC_CHECK_MODE) {
        if (!RVALUE_OLD_P(a)) rb_bug("gc_writebarrier_generational: %s is not an old object.", obj_info(a));
        if ( RVALUE_OLD_P(b)) rb_bug("gc_writebarrier_generational: %s is an old object.", obj_info(b));
        if (is_incremental_marking(objspace)) rb_bug("gc_writebarrier_generational: called while incremental marking: %s -> %s", obj_info(a), obj_info(b));
    }

    /* mark `a' and remember (default behavior) */
    if (!RVALUE_REMEMBERED(a)) {
        RB_VM_LOCK_ENTER_NO_BARRIER();
        {
            rgengc_remember(objspace, a);
        }
        RB_VM_LOCK_LEAVE_NO_BARRIER();
        gc_report(1, objspace, "gc_writebarrier_generational: %s (remembered) -> %s\n", obj_info(a), obj_info(b));
    }

    check_rvalue_consistency(a);
    check_rvalue_consistency(b);
}

static void
gc_mark_from(rb_objspace_t *objspace, VALUE obj, VALUE parent)
{
    gc_mark_set_parent(objspace, parent);
    rgengc_check_relation(objspace, obj);
    if (gc_mark_set(objspace, obj) == FALSE) return;
    gc_aging(objspace, obj);
    gc_grey(objspace, obj);
}

NOINLINE(static void gc_writebarrier_incremental(VALUE a, VALUE b, rb_objspace_t *objspace));

static void
gc_writebarrier_incremental(VALUE a, VALUE b, rb_objspace_t *objspace)
{
    gc_report(2, objspace, "gc_writebarrier_incremental: [LG] %p -> %s\n", (void *)a, obj_info(b));

    if (RVALUE_BLACK_P(a)) {
        if (RVALUE_WHITE_P(b)) {
            if (!RVALUE_WB_UNPROTECTED(a)) {
                gc_report(2, objspace, "gc_writebarrier_incremental: [IN] %p -> %s\n", (void *)a, obj_info(b));
                gc_mark_from(objspace, b, a);
            }
        }
        else if (RVALUE_OLD_P(a) && !RVALUE_OLD_P(b)) {
            rgengc_remember(objspace, a);
        }

        if (UNLIKELY(objspace->flags.during_compacting)) {
            MARK_IN_BITMAP(GET_HEAP_PINNED_BITS(b), b);
        }
    }
}

void
rb_gc_writebarrier(VALUE a, VALUE b)
{
    rb_objspace_t *objspace = &rb_objspace;

    if (RGENGC_CHECK_MODE) {
        if (SPECIAL_CONST_P(a)) rb_bug("rb_gc_writebarrier: a is special const: %"PRIxVALUE, a);
        if (SPECIAL_CONST_P(b)) rb_bug("rb_gc_writebarrier: b is special const: %"PRIxVALUE, b);
    }

  retry:
    if (!is_incremental_marking(objspace)) {
        if (!RVALUE_OLD_P(a) || RVALUE_OLD_P(b)) {
            // do nothing
        }
        else {
            gc_writebarrier_generational(a, b, objspace);
        }
    }
    else {
        bool retry = false;
        /* slow path */
        RB_VM_LOCK_ENTER_NO_BARRIER();
        {
            if (is_incremental_marking(objspace)) {
                gc_writebarrier_incremental(a, b, objspace);
            }
            else {
                retry = true;
            }
        }
        RB_VM_LOCK_LEAVE_NO_BARRIER();

        if (retry) goto retry;
    }
    return;
}

void
rb_gc_writebarrier_unprotect(VALUE obj)
{
    if (RVALUE_WB_UNPROTECTED(obj)) {
        return;
    }
    else {
        rb_objspace_t *objspace = &rb_objspace;

        gc_report(2, objspace, "rb_gc_writebarrier_unprotect: %s %s\n", obj_info(obj),
                  RVALUE_REMEMBERED(obj) ? " (already remembered)" : "");

        RB_VM_LOCK_ENTER_NO_BARRIER();
        {
            if (RVALUE_OLD_P(obj)) {
                gc_report(1, objspace, "rb_gc_writebarrier_unprotect: %s\n", obj_info(obj));
                RVALUE_DEMOTE(objspace, obj);
                gc_mark_set(objspace, obj);
                gc_remember_unprotected(objspace, obj);

#if RGENGC_PROFILE
                objspace->profile.total_shade_operation_count++;
#if RGENGC_PROFILE >= 2
                objspace->profile.shade_operation_count_types[BUILTIN_TYPE(obj)]++;
#endif /* RGENGC_PROFILE >= 2 */
#endif /* RGENGC_PROFILE */
            }
            else {
                RVALUE_AGE_RESET(obj);
            }

            RB_DEBUG_COUNTER_INC(obj_wb_unprotect);
            MARK_IN_BITMAP(GET_HEAP_WB_UNPROTECTED_BITS(obj), obj);
        }
        RB_VM_LOCK_LEAVE_NO_BARRIER();
    }
}

/*
 * remember `obj' if needed.
 */
void
rb_gc_writebarrier_remember(VALUE obj)
{
    rb_objspace_t *objspace = &rb_objspace;

    gc_report(1, objspace, "rb_gc_writebarrier_remember: %s\n", obj_info(obj));

    if (is_incremental_marking(objspace)) {
        if (RVALUE_BLACK_P(obj)) {
            gc_grey(objspace, obj);
        }
    }
    else {
        if (RVALUE_OLD_P(obj)) {
            rgengc_remember(objspace, obj);
        }
    }
}

void
rb_copy_wb_protected_attribute(VALUE dest, VALUE obj)
{
    if (RVALUE_WB_UNPROTECTED(obj)) {
        rb_gc_writebarrier_unprotect(dest);
    }
}

size_t
rb_obj_gc_flags(VALUE obj, ID* flags, size_t max)
{
    size_t n = 0;
    static ID ID_marked;
    static ID ID_wb_protected, ID_old, ID_marking, ID_uncollectible, ID_pinned;

    if (!ID_marked) {
#define I(s) ID_##s = rb_intern(#s);
        I(marked);
        I(wb_protected);
        I(old);
        I(marking);
        I(uncollectible);
        I(pinned);
#undef I
    }

    if (RVALUE_WB_UNPROTECTED(obj) == 0 && n<max)                   flags[n++] = ID_wb_protected;
    if (RVALUE_OLD_P(obj) && n<max)                                 flags[n++] = ID_old;
    if (RVALUE_UNCOLLECTIBLE(obj) && n<max)                         flags[n++] = ID_uncollectible;
    if (MARKED_IN_BITMAP(GET_HEAP_MARKING_BITS(obj), obj) && n<max) flags[n++] = ID_marking;
    if (MARKED_IN_BITMAP(GET_HEAP_MARK_BITS(obj), obj) && n<max)    flags[n++] = ID_marked;
    if (MARKED_IN_BITMAP(GET_HEAP_PINNED_BITS(obj), obj) && n<max)  flags[n++] = ID_pinned;
    return n;
}

/* GC */

void
rb_gc_ractor_newobj_cache_clear(rb_ractor_newobj_cache_t *newobj_cache)
{
    newobj_cache->incremental_mark_step_allocated_slots = 0;

    for (size_t size_pool_idx = 0; size_pool_idx < SIZE_POOL_COUNT; size_pool_idx++) {
        rb_ractor_newobj_size_pool_cache_t *cache = &newobj_cache->size_pool_caches[size_pool_idx];

        struct heap_page *page = cache->using_page;
        RVALUE *freelist = cache->freelist;
        RUBY_DEBUG_LOG("ractor using_page:%p freelist:%p", (void *)page, (void *)freelist);

        heap_page_freelist_append(page, freelist);

        cache->using_page = NULL;
        cache->freelist = NULL;
    }
}

void
rb_gc_force_recycle(VALUE obj)
{
    /* no-op */
}

void
rb_gc_register_mark_object(VALUE obj)
{
    if (!is_pointer_to_heap(&rb_objspace, (void *)obj))
        return;

    rb_vm_register_global_object(obj);
}

void
rb_gc_register_address(VALUE *addr)
{
    rb_vm_t *vm = GET_VM();

    VALUE obj = *addr;

    struct global_object_list *tmp = ALLOC(struct global_object_list);
    tmp->next = vm->global_object_list;
    tmp->varptr = addr;
    vm->global_object_list = tmp;

    /*
     * Because some C extensions have assignment-then-register bugs,
     * we guard `obj` here so that it would not get swept defensively.
     */
    RB_GC_GUARD(obj);
    if (0 && !SPECIAL_CONST_P(obj)) {
        rb_warn("Object is assigned to registering address already: %"PRIsVALUE,
                rb_obj_class(obj));
        rb_print_backtrace(stderr);
    }
}

void
rb_gc_unregister_address(VALUE *addr)
{
    rb_vm_t *vm = GET_VM();
    struct global_object_list *tmp = vm->global_object_list;

    if (tmp->varptr == addr) {
        vm->global_object_list = tmp->next;
        xfree(tmp);
        return;
    }
    while (tmp->next) {
        if (tmp->next->varptr == addr) {
            struct global_object_list *t = tmp->next;

            tmp->next = tmp->next->next;
            xfree(t);
            break;
        }
        tmp = tmp->next;
    }
}

void
rb_global_variable(VALUE *var)
{
    rb_gc_register_address(var);
}

enum {
    gc_stress_no_major,
    gc_stress_no_immediate_sweep,
    gc_stress_full_mark_after_malloc,
    gc_stress_max
};

#define gc_stress_full_mark_after_malloc_p() \
    (FIXNUM_P(ruby_gc_stress_mode) && (FIX2LONG(ruby_gc_stress_mode) & (1<<gc_stress_full_mark_after_malloc)))

static void
heap_ready_to_gc(rb_objspace_t *objspace, rb_size_pool_t *size_pool, rb_heap_t *heap)
{
    if (!heap->free_pages) {
        if (!heap_increment(objspace, size_pool, heap)) {
            size_pool_allocatable_pages_set(objspace, size_pool, 1);
            heap_increment(objspace, size_pool, heap);
        }
    }
}

static int
ready_to_gc(rb_objspace_t *objspace)
{
    if (dont_gc_val() || during_gc || ruby_disable_gc) {
        for (int i = 0; i < SIZE_POOL_COUNT; i++) {
            rb_size_pool_t *size_pool = &size_pools[i];
            heap_ready_to_gc(objspace, size_pool, SIZE_POOL_EDEN_HEAP(size_pool));
        }
        return FALSE;
    }
    else {
        return TRUE;
    }
}

static void
gc_reset_malloc_info(rb_objspace_t *objspace, bool full_mark)
{
    gc_prof_set_malloc_info(objspace);
    {
        size_t inc = ATOMIC_SIZE_EXCHANGE(malloc_increase, 0);
        size_t old_limit = malloc_limit;

        if (inc > malloc_limit) {
            malloc_limit = (size_t)(inc * gc_params.malloc_limit_growth_factor);
            if (malloc_limit > gc_params.malloc_limit_max) {
                malloc_limit = gc_params.malloc_limit_max;
            }
        }
        else {
            malloc_limit = (size_t)(malloc_limit * 0.98); /* magic number */
            if (malloc_limit < gc_params.malloc_limit_min) {
                malloc_limit = gc_params.malloc_limit_min;
            }
        }

        if (0) {
            if (old_limit != malloc_limit) {
                fprintf(stderr, "[%"PRIuSIZE"] malloc_limit: %"PRIuSIZE" -> %"PRIuSIZE"\n",
                        rb_gc_count(), old_limit, malloc_limit);
            }
            else {
                fprintf(stderr, "[%"PRIuSIZE"] malloc_limit: not changed (%"PRIuSIZE")\n",
                        rb_gc_count(), malloc_limit);
            }
        }
    }

    /* reset oldmalloc info */
#if RGENGC_ESTIMATE_OLDMALLOC
    if (!full_mark) {
        if (objspace->rgengc.oldmalloc_increase > objspace->rgengc.oldmalloc_increase_limit) {
            objspace->rgengc.need_major_gc |= GPR_FLAG_MAJOR_BY_OLDMALLOC;
            objspace->rgengc.oldmalloc_increase_limit =
              (size_t)(objspace->rgengc.oldmalloc_increase_limit * gc_params.oldmalloc_limit_growth_factor);

            if (objspace->rgengc.oldmalloc_increase_limit > gc_params.oldmalloc_limit_max) {
                objspace->rgengc.oldmalloc_increase_limit = gc_params.oldmalloc_limit_max;
            }
        }

        if (0) fprintf(stderr, "%"PRIdSIZE"\t%d\t%"PRIuSIZE"\t%"PRIuSIZE"\t%"PRIdSIZE"\n",
                       rb_gc_count(),
                       objspace->rgengc.need_major_gc,
                       objspace->rgengc.oldmalloc_increase,
                       objspace->rgengc.oldmalloc_increase_limit,
                       gc_params.oldmalloc_limit_max);
    }
    else {
        /* major GC */
        objspace->rgengc.oldmalloc_increase = 0;

        if ((objspace->profile.latest_gc_info & GPR_FLAG_MAJOR_BY_OLDMALLOC) == 0) {
            objspace->rgengc.oldmalloc_increase_limit =
              (size_t)(objspace->rgengc.oldmalloc_increase_limit / ((gc_params.oldmalloc_limit_growth_factor - 1)/10 + 1));
            if (objspace->rgengc.oldmalloc_increase_limit < gc_params.oldmalloc_limit_min) {
                objspace->rgengc.oldmalloc_increase_limit = gc_params.oldmalloc_limit_min;
            }
        }
    }
#endif
}

static int
garbage_collect(rb_objspace_t *objspace, unsigned int reason)
{
    int ret;

    RB_VM_LOCK_ENTER();
    {
#if GC_PROFILE_MORE_DETAIL
        objspace->profile.prepare_time = getrusage_time();
#endif

        gc_rest(objspace);

#if GC_PROFILE_MORE_DETAIL
        objspace->profile.prepare_time = getrusage_time() - objspace->profile.prepare_time;
#endif

        ret = gc_start(objspace, reason);
    }
    RB_VM_LOCK_LEAVE();

    return ret;
}

static int
gc_start(rb_objspace_t *objspace, unsigned int reason)
{
    unsigned int do_full_mark = !!(reason & GPR_FLAG_FULL_MARK);

    /* reason may be clobbered, later, so keep set immediate_sweep here */
    objspace->flags.immediate_sweep = !!(reason & GPR_FLAG_IMMEDIATE_SWEEP);

    if (!heap_allocated_pages) return FALSE; /* heap is not ready */
    if (!(reason & GPR_FLAG_METHOD) && !ready_to_gc(objspace)) return TRUE; /* GC is not allowed */

    GC_ASSERT(gc_mode(objspace) == gc_mode_none);
    GC_ASSERT(!is_lazy_sweeping(objspace));
    GC_ASSERT(!is_incremental_marking(objspace));

    unsigned int lock_lev;
    gc_enter(objspace, gc_enter_event_start, &lock_lev);

#if RGENGC_CHECK_MODE >= 2
    gc_verify_internal_consistency(objspace);
#endif

    if (ruby_gc_stressful) {
        int flag = FIXNUM_P(ruby_gc_stress_mode) ? FIX2INT(ruby_gc_stress_mode) : 0;

        if ((flag & (1<<gc_stress_no_major)) == 0) {
            do_full_mark = TRUE;
        }

        objspace->flags.immediate_sweep = !(flag & (1<<gc_stress_no_immediate_sweep));
    }

    if (objspace->rgengc.need_major_gc) {
        reason |= objspace->rgengc.need_major_gc;
        do_full_mark = TRUE;
    }
    else if (RGENGC_FORCE_MAJOR_GC) {
        reason = GPR_FLAG_MAJOR_BY_FORCE;
        do_full_mark = TRUE;
    }

    objspace->rgengc.need_major_gc = GPR_FLAG_NONE;

    if (do_full_mark && (reason & GPR_FLAG_MAJOR_MASK) == 0) {
        reason |= GPR_FLAG_MAJOR_BY_FORCE; /* GC by CAPI, METHOD, and so on. */
    }

    if (objspace->flags.dont_incremental ||
            reason & GPR_FLAG_IMMEDIATE_MARK ||
            ruby_gc_stressful) {
        objspace->flags.during_incremental_marking = FALSE;
    }
    else {
        objspace->flags.during_incremental_marking = do_full_mark;
    }

    /* Explicitly enable compaction (GC.compact) */
    if (do_full_mark && ruby_enable_autocompact) {
        objspace->flags.during_compacting = TRUE;
#if RGENGC_CHECK_MODE
        objspace->rcompactor.compare_func = ruby_autocompact_compare_func;
#endif
    }
    else {
        objspace->flags.during_compacting = !!(reason & GPR_FLAG_COMPACT);
    }

    if (!GC_ENABLE_LAZY_SWEEP || objspace->flags.dont_incremental) {
        objspace->flags.immediate_sweep = TRUE;
    }

    if (objspace->flags.immediate_sweep) reason |= GPR_FLAG_IMMEDIATE_SWEEP;

    gc_report(1, objspace, "gc_start(reason: %x) => %u, %d, %d\n",
              reason,
              do_full_mark, !is_incremental_marking(objspace), objspace->flags.immediate_sweep);

#if USE_DEBUG_COUNTER
    RB_DEBUG_COUNTER_INC(gc_count);

    if (reason & GPR_FLAG_MAJOR_MASK) {
        (void)RB_DEBUG_COUNTER_INC_IF(gc_major_nofree, reason & GPR_FLAG_MAJOR_BY_NOFREE);
        (void)RB_DEBUG_COUNTER_INC_IF(gc_major_oldgen, reason & GPR_FLAG_MAJOR_BY_OLDGEN);
        (void)RB_DEBUG_COUNTER_INC_IF(gc_major_shady,  reason & GPR_FLAG_MAJOR_BY_SHADY);
        (void)RB_DEBUG_COUNTER_INC_IF(gc_major_force,  reason & GPR_FLAG_MAJOR_BY_FORCE);
#if RGENGC_ESTIMATE_OLDMALLOC
        (void)RB_DEBUG_COUNTER_INC_IF(gc_major_oldmalloc, reason & GPR_FLAG_MAJOR_BY_OLDMALLOC);
#endif
    }
    else {
        (void)RB_DEBUG_COUNTER_INC_IF(gc_minor_newobj, reason & GPR_FLAG_NEWOBJ);
        (void)RB_DEBUG_COUNTER_INC_IF(gc_minor_malloc, reason & GPR_FLAG_MALLOC);
        (void)RB_DEBUG_COUNTER_INC_IF(gc_minor_method, reason & GPR_FLAG_METHOD);
        (void)RB_DEBUG_COUNTER_INC_IF(gc_minor_capi,   reason & GPR_FLAG_CAPI);
        (void)RB_DEBUG_COUNTER_INC_IF(gc_minor_stress, reason & GPR_FLAG_STRESS);
    }
#endif

    objspace->profile.count++;
    objspace->profile.latest_gc_info = reason;
    objspace->profile.total_allocated_objects_at_gc_start = total_allocated_objects(objspace);
    objspace->profile.heap_used_at_gc_start = heap_allocated_pages;
    objspace->profile.weak_references_count = 0;
    objspace->profile.retained_weak_references_count = 0;
    gc_prof_setup_new_record(objspace, reason);
    gc_reset_malloc_info(objspace, do_full_mark);

    gc_event_hook(objspace, RUBY_INTERNAL_EVENT_GC_START, 0 /* TODO: pass minor/immediate flag? */);
    GC_ASSERT(during_gc);

    gc_prof_timer_start(objspace);
    {
        if (gc_marks(objspace, do_full_mark)) {
            gc_sweep(objspace);
        }
    }
    gc_prof_timer_stop(objspace);

    gc_exit(objspace, gc_enter_event_start, &lock_lev);
    return TRUE;
}

static void
gc_rest(rb_objspace_t *objspace)
{
    int marking = is_incremental_marking(objspace);
    int sweeping = is_lazy_sweeping(objspace);

    if (marking || sweeping) {
        unsigned int lock_lev;
        gc_enter(objspace, gc_enter_event_rest, &lock_lev);

        if (RGENGC_CHECK_MODE >= 2) gc_verify_internal_consistency(objspace);

        if (is_incremental_marking(objspace)) {
            gc_marking_enter(objspace);
            gc_marks_rest(objspace);
            gc_marking_exit(objspace);

            gc_sweep(objspace);
        }

        if (is_lazy_sweeping(objspace)) {
            gc_sweeping_enter(objspace);
            gc_sweep_rest(objspace);
            gc_sweeping_exit(objspace);
        }

        gc_exit(objspace, gc_enter_event_rest, &lock_lev);
    }
}

struct objspace_and_reason {
    rb_objspace_t *objspace;
    unsigned int reason;
};

static const char *
gc_current_status(rb_objspace_t *objspace)
{
    print_for_debug("gc_current_status");
    return 0;
}

#if PRINT_ENTER_EXIT_TICK

static tick_t last_exit_tick;
static tick_t enter_tick;
static int enter_count = 0;
static char last_gc_status[0x10];

#endif

static inline void
gc_record(rb_objspace_t *objspace, int direction, const char *event)
{
    print_for_debug("gc_record");
}

static const char *
gc_enter_event_cstr(enum gc_enter_event event)
{
    print_for_debug("gc_enter_event_cstr");
    return 0;
}

static void
gc_enter_count(enum gc_enter_event event)
{
    print_for_debug("gc_enter_count");
}

static inline void
gc_enter(rb_objspace_t *objspace, enum gc_enter_event event, unsigned int *lock_lev)
{
    // required, segv otherwise
    RB_VM_LOCK_ENTER_LEV(lock_lev);

    switch (event) {
      case gc_enter_event_rest:
        if (!is_marking(objspace)) break;
        // fall through
      case gc_enter_event_start:
      case gc_enter_event_continue:
        // stop other ractors
        rb_vm_barrier();
        break;
      default:
        break;
    }

    gc_enter_count(event);
    if (UNLIKELY(during_gc != 0)) rb_bug("during_gc != 0");
    if (RGENGC_CHECK_MODE >= 3) gc_verify_internal_consistency(objspace);

    during_gc = TRUE;
    RUBY_DEBUG_LOG("%s (%s)",gc_enter_event_cstr(event), gc_current_status(objspace));
    gc_report(1, objspace, "gc_enter: %s [%s]\n", gc_enter_event_cstr(event), gc_current_status(objspace));
    gc_record(objspace, 0, gc_enter_event_cstr(event));
    gc_event_hook(objspace, RUBY_INTERNAL_EVENT_GC_ENTER, 0); /* TODO: which parameter should be passed? */
}

static inline void
gc_exit(rb_objspace_t *objspace, enum gc_enter_event event, unsigned int *lock_lev)
{
    // required, segv otherwise
    GC_ASSERT(during_gc != 0);

    gc_event_hook(objspace, RUBY_INTERNAL_EVENT_GC_EXIT, 0); /* TODO: which parameter should be passed? */
    gc_record(objspace, 1, gc_enter_event_cstr(event));
    RUBY_DEBUG_LOG("%s (%s)", gc_enter_event_cstr(event), gc_current_status(objspace));
    gc_report(1, objspace, "gc_exit: %s [%s]\n", gc_enter_event_cstr(event), gc_current_status(objspace));
    during_gc = FALSE;

    RB_VM_LOCK_LEAVE_LEV(lock_lev);
}

#ifndef MEASURE_GC
#define MEASURE_GC (objspace->flags.measure_gc)
#endif

static void
gc_marking_enter(rb_objspace_t *objspace)
{
    print_for_debug("gc_marking_enter");
}

static void
gc_marking_exit(rb_objspace_t *objspace)
{
    print_for_debug("gc_marking_exit");
}

static void
gc_sweeping_enter(rb_objspace_t *objspace)
{
    print_for_debug("gc_sweeping_enter");
}

static void
gc_sweeping_exit(rb_objspace_t *objspace)
{
    print_for_debug("gc_sweeping_exit");
}

static int
garbage_collect_with_gvl(rb_objspace_t *objspace, unsigned int reason)
{
    print_for_debug("garbage_collect_with_gvl");
    return 0;
}

static VALUE
gc_start_internal(rb_execution_context_t *ec, VALUE self, VALUE full_mark, VALUE immediate_mark, VALUE immediate_sweep, VALUE compact)
{
    print_for_debug("gc_start_internal");
    return 0;
}

void
rb_gc_prepare_heap(void)
{
    print_for_debug("rb_gc_prepare_heap");
}

static int
gc_is_moveable_obj(rb_objspace_t *objspace, VALUE obj)
{
    print_for_debug("gc_is_moveable_obj");
    return 0;
}

static VALUE
gc_move(rb_objspace_t *objspace, VALUE scan, VALUE free, size_t src_slot_size, size_t slot_size)
{
    print_for_debug("gc_move");
    return 0;
}

#if GC_CAN_COMPILE_COMPACTION
static int
compare_pinned_slots(const void *left, const void *right, void *dummy)
{
    print_for_debug(__func__);
    return 0;
}

static void
gc_sort_heap_by_compare_func(rb_objspace_t *objspace, gc_compact_compare_func compare_func)
{
    print_for_debug(__func__);
}
#endif

void
rb_gc_ref_update_table_values_only(st_table *tbl)
{
    print_for_debug(__func__);
}

/* Update MOVED references in a VALUE=>VALUE st_table */
void
rb_gc_update_tbl_refs(st_table *ptr)
{
    print_for_debug(__func__);
}

void
rb_gc_update_values(long n, VALUE *values)
{
    print_for_debug("rb_gc_update_values");
}

/* Returns the new location of an object, if it moved.  Otherwise returns
 * the existing location. */
VALUE
rb_gc_location(VALUE value)
{

    print_for_debug("rb_gc_location");
    return 0;
}

static void
mark_cvc_tbl(rb_objspace_t *objspace, VALUE klass)
{
    print_for_debug(__func__);
}

extern rb_symbols_t ruby_global_symbols;
#define global_symbols ruby_global_symbols

static void
gc_update_references(rb_objspace_t *objspace)
{
    print_for_debug(__func__);
}

#if GC_CAN_COMPILE_COMPACTION
/*
 *  call-seq:
 *     GC.latest_compact_info -> hash
 *
 * Returns information about object moved in the most recent \GC compaction.
 *
 * The returned +hash+ contains the following keys:
 *
 * [considered]
 *   Hash containing the type of the object as the key and the number of
 *   objects of that type that were considered for movement.
 * [moved]
 *   Hash containing the type of the object as the key and the number of
 *   objects of that type that were actually moved.
 * [moved_up]
 *   Hash containing the type of the object as the key and the number of
 *   objects of that type that were increased in size.
 * [moved_down]
 *   Hash containing the type of the object as the key and the number of
 *   objects of that type that were decreased in size.
 *
 * Some objects can't be moved (due to pinning) so these numbers can be used to
 * calculate compaction efficiency.
 */
static VALUE
gc_compact_stats(VALUE self)
{
    print_for_debug("gc_compact_stats");
    return 0;
}
#else
#  define gc_compact_stats rb_f_notimplement
#endif

#if GC_CAN_COMPILE_COMPACTION
/*
 *  call-seq:
 *     GC.compact -> hash
 *
 * This function compacts objects together in Ruby's heap. It eliminates
 * unused space (or fragmentation) in the heap by moving objects in to that
 * unused space.
 *
 * The returned +hash+ contains statistics about the objects that were moved;
 * see GC.latest_compact_info.
 *
 * This method is only expected to work on CRuby.
 *
 * To test whether \GC compaction is supported, use the idiom:
 *
 *   GC.respond_to?(:compact)
 */
static VALUE
gc_compact(VALUE self)
{
    /* Run GC with compaction enabled */
    gc_start_internal(NULL, self, Qtrue, Qtrue, Qtrue, Qtrue);

    return gc_compact_stats(self);
}
#else
#  define gc_compact rb_f_notimplement
#endif

#if GC_CAN_COMPILE_COMPACTION

static VALUE
gc_verify_compaction_references(rb_execution_context_t *ec, VALUE self, VALUE double_heap, VALUE expand_heap, VALUE toward_empty)
{
    print_for_debug(__func__);
    return 0;
}
#else
#  define gc_verify_compaction_references (rb_builtin_arity3_function_type)rb_f_notimplement
#endif

VALUE
rb_gc_start(void)
{
    print_for_debug(__func__);
    return 0;
}

void
rb_gc(void)
{
    print_for_debug(__func__);
}

int
rb_during_gc(void)
{
    print_for_debug(__func__);
    return 0;
}

#if RGENGC_PROFILE >= 2

static const char *type_name(int type, VALUE obj);

static void
gc_count_add_each_types(VALUE hash, const char *name, const size_t *types)
{
    print_for_debug("gc_count_add_each_types");
    return 0;
}
#endif

size_t
rb_gc_count(void)
{
    print_for_debug("rb_gc_count");
    return 0;
}

static VALUE
gc_count(rb_execution_context_t *ec, VALUE self)
{
    print_for_debug("gc_count");
    return 0;
}

VALUE
rb_gc_latest_gc_info(VALUE key)
{
    print_for_debug("rb_gc_latest_gc_info");
    return 0;
}

static VALUE
gc_latest_gc_info(rb_execution_context_t *ec, VALUE self, VALUE arg)
{
    print_for_debug("gc_latest_gc_info");
    return 0;
}

enum gc_stat_sym {
    gc_stat_sym_count,
    gc_stat_sym_time,
    gc_stat_sym_marking_time,
    gc_stat_sym_sweeping_time,
    gc_stat_sym_heap_allocated_pages,
    gc_stat_sym_heap_sorted_length,
    gc_stat_sym_heap_allocatable_pages,
    gc_stat_sym_heap_available_slots,
    gc_stat_sym_heap_live_slots,
    gc_stat_sym_heap_free_slots,
    gc_stat_sym_heap_final_slots,
    gc_stat_sym_heap_marked_slots,
    gc_stat_sym_heap_eden_pages,
    gc_stat_sym_heap_tomb_pages,
    gc_stat_sym_total_allocated_pages,
    gc_stat_sym_total_freed_pages,
    gc_stat_sym_total_allocated_objects,
    gc_stat_sym_total_freed_objects,
    gc_stat_sym_malloc_increase_bytes,
    gc_stat_sym_malloc_increase_bytes_limit,
    gc_stat_sym_minor_gc_count,
    gc_stat_sym_major_gc_count,
    gc_stat_sym_compact_count,
    gc_stat_sym_read_barrier_faults,
    gc_stat_sym_total_moved_objects,
    gc_stat_sym_remembered_wb_unprotected_objects,
    gc_stat_sym_remembered_wb_unprotected_objects_limit,
    gc_stat_sym_old_objects,
    gc_stat_sym_old_objects_limit,
#if RGENGC_ESTIMATE_OLDMALLOC
    gc_stat_sym_oldmalloc_increase_bytes,
    gc_stat_sym_oldmalloc_increase_bytes_limit,
#endif
    gc_stat_sym_weak_references_count,
#if RGENGC_PROFILE
    gc_stat_sym_total_generated_normal_object_count,
    gc_stat_sym_total_generated_shady_object_count,
    gc_stat_sym_total_shade_operation_count,
    gc_stat_sym_total_promoted_count,
    gc_stat_sym_total_remembered_normal_object_count,
    gc_stat_sym_total_remembered_shady_object_count,
#endif
    gc_stat_sym_last
};

static VALUE
gc_stat(rb_execution_context_t *ec, VALUE self, VALUE arg) // arg is (nil || hash || symbol)
{
    print_for_debug("gc_stat");
    return 0;
}

size_t
rb_gc_stat(VALUE key)
{
    print_for_debug("rb_gc_stat");
    return 0;
}


enum gc_stat_heap_sym {
    gc_stat_heap_sym_slot_size,
    gc_stat_heap_sym_heap_allocatable_pages,
    gc_stat_heap_sym_heap_eden_pages,
    gc_stat_heap_sym_heap_eden_slots,
    gc_stat_heap_sym_heap_tomb_pages,
    gc_stat_heap_sym_heap_tomb_slots,
    gc_stat_heap_sym_total_allocated_pages,
    gc_stat_heap_sym_total_freed_pages,
    gc_stat_heap_sym_force_major_gc_count,
    gc_stat_heap_sym_force_incremental_marking_finish_count,
    gc_stat_heap_sym_total_allocated_objects,
    gc_stat_heap_sym_total_freed_objects,
    gc_stat_heap_sym_last
};

static VALUE
gc_stat_heap(rb_execution_context_t *ec, VALUE self, VALUE heap_name, VALUE arg)
{
    print_for_debug("gc_stat_heap");
    return 0;
}

static VALUE
gc_stress_get(rb_execution_context_t *ec, VALUE self)
{
    print_for_debug(__func__);
    return 0;
}

void
rb_gc_stress_set(VALUE flag)
{
    print_for_debug(__func__);
}

static VALUE
gc_stress_set_m(rb_execution_context_t *ec, VALUE self, VALUE flag)
{
    print_for_debug(__func__);
    return 0;
}

VALUE
rb_gc_enable(void)
{
    print_for_debug(__func__);
    return 0;
}

VALUE
rb_objspace_gc_enable(rb_objspace_t *objspace)
{
    print_for_debug(__func__);
    return 0;
}

static VALUE
gc_enable(rb_execution_context_t *ec, VALUE _)
{
    print_for_debug(__func__);
    return 0;
}

VALUE
rb_gc_disable_no_rest(void)
{
    print_for_debug(__func__);
    return 0;
}

VALUE
rb_gc_disable(void)
{
    print_for_debug(__func__);
    return 0;
}

VALUE
rb_objspace_gc_disable(rb_objspace_t *objspace)
{
    print_for_debug(__func__);
    return 0;
}

static VALUE
gc_disable(rb_execution_context_t *ec, VALUE _)
{
    print_for_debug(__func__);
    return 0;
}

#if GC_CAN_COMPILE_COMPACTION
/*
 *  call-seq:
 *     GC.auto_compact = flag
 *
 *  Updates automatic compaction mode.
 *
 *  When enabled, the compactor will execute on every major collection.
 *
 *  Enabling compaction will degrade performance on major collections.
 */
static VALUE
gc_set_auto_compact(VALUE _, VALUE v)
{
    print_for_debug(__func__);
    return 0;
}
#else
#  define gc_set_auto_compact rb_f_notimplement
#endif

#if GC_CAN_COMPILE_COMPACTION
/*
 *  call-seq:
 *     GC.auto_compact    -> true or false
 *
 *  Returns whether or not automatic compaction has been enabled.
 */
static VALUE
gc_get_auto_compact(VALUE _)
{
    print_for_debug(__func__);
    return 0;
}
#else
#  define gc_get_auto_compact rb_f_notimplement
#endif

/*
 * GC tuning environment variables
 *
 * * RUBY_GC_HEAP_FREE_SLOTS
 *   - Prepare at least this amount of slots after GC.
 *   - Allocate slots if there are not enough slots.
 * * RUBY_GC_HEAP_GROWTH_FACTOR (new from 2.1)
 *   - Allocate slots by this factor.
 *   - (next slots number) = (current slots number) * (this factor)
 * * RUBY_GC_HEAP_GROWTH_MAX_SLOTS (new from 2.1)
 *   - Allocation rate is limited to this number of slots.
 * * RUBY_GC_HEAP_FREE_SLOTS_MIN_RATIO (new from 2.4)
 *   - Allocate additional pages when the number of free slots is
 *     lower than the value (total_slots * (this ratio)).
 * * RUBY_GC_HEAP_FREE_SLOTS_GOAL_RATIO (new from 2.4)
 *   - Allocate slots to satisfy this formula:
 *       free_slots = total_slots * goal_ratio
 *   - In other words, prepare (total_slots * goal_ratio) free slots.
 *   - if this value is 0.0, then use RUBY_GC_HEAP_GROWTH_FACTOR directly.
 * * RUBY_GC_HEAP_FREE_SLOTS_MAX_RATIO (new from 2.4)
 *   - Allow to free pages when the number of free slots is
 *     greater than the value (total_slots * (this ratio)).
 * * RUBY_GC_HEAP_OLDOBJECT_LIMIT_FACTOR (new from 2.1.1)
 *   - Do full GC when the number of old objects is more than R * N
 *     where R is this factor and
 *           N is the number of old objects just after last full GC.
 *
 *  * obsolete
 *    * RUBY_FREE_MIN       -> RUBY_GC_HEAP_FREE_SLOTS (from 2.1)
 *    * RUBY_HEAP_MIN_SLOTS -> RUBY_GC_HEAP_INIT_SLOTS (from 2.1)
 *
 * * RUBY_GC_MALLOC_LIMIT
 * * RUBY_GC_MALLOC_LIMIT_MAX (new from 2.1)
 * * RUBY_GC_MALLOC_LIMIT_GROWTH_FACTOR (new from 2.1)
 *
 * * RUBY_GC_OLDMALLOC_LIMIT (new from 2.1)
 * * RUBY_GC_OLDMALLOC_LIMIT_MAX (new from 2.1)
 * * RUBY_GC_OLDMALLOC_LIMIT_GROWTH_FACTOR (new from 2.1)
 */

void
ruby_gc_set_params(void)
{
    print_for_debug(__func__);
}

static void
reachable_objects_from_callback(VALUE obj)
{
    print_for_debug(__func__);
}

void
rb_objspace_reachable_objects_from(VALUE obj, void (func)(VALUE, void *), void *data)
{
    print_for_debug(__func__);
}

struct root_objects_data {
    const char *category;
    void (*func)(const char *category, VALUE, void *);
    void *data;
};

void
rb_objspace_reachable_objects_from_root(void (func)(const char *category, VALUE, void *), void *passing_data)
{
    print_for_debug(__func__);
}

/*
  ------------------------ Extended allocator ------------------------
*/

struct gc_raise_tag {
    VALUE exc;
    const char *fmt;
    va_list *ap;
};

static void
gc_raise(VALUE exc, const char *fmt, ...)
{
    print_for_debug(__func__);
    UNREACHABLE_RETURN(NULL);
}

static void objspace_xfree(rb_objspace_t *objspace, void *ptr, size_t size);

static void *
ruby_memerror_body(void *dummy)
{
    print_for_debug(__func__);
    return 0;
}

NORETURN(static void ruby_memerror(void));
RBIMPL_ATTR_MAYBE_UNUSED()
static void
ruby_memerror(void)
{
    if (ruby_thread_has_gvl_p()) {
        rb_memerror();
    }
    else {
        if (ruby_native_thread_p()) {
            rb_thread_call_with_gvl(ruby_memerror_body, 0);
        }
        else {
            /* no ruby thread */
            fprintf(stderr, "[FATAL] failed to allocate memory\n");
        }
    }
    exit(EXIT_FAILURE);
}

void
rb_memerror(void)
{
    rb_execution_context_t *ec = GET_EC();
    rb_objspace_t *objspace = rb_objspace_of(rb_ec_vm_ptr(ec));
    VALUE exc;

    if (0) {
        // Print out pid, sleep, so you can attach debugger to see what went wrong:
        fprintf(stderr, "rb_memerror pid=%"PRI_PIDT_PREFIX"d\n", getpid());
        sleep(60);
    }

    if (during_gc) {
        // TODO: OMG!! How to implement it?
        gc_exit(objspace, gc_enter_event_rb_memerror, NULL);
    }

    exc = nomem_error;
    if (!exc ||
        rb_ec_raised_p(ec, RAISED_NOMEMORY)) {
        fprintf(stderr, "[FATAL] failed to allocate memory\n");
        exit(EXIT_FAILURE);
    }
    if (rb_ec_raised_p(ec, RAISED_NOMEMORY)) {
        rb_ec_raised_clear(ec);
    }
    else {
        rb_ec_raised_set(ec, RAISED_NOMEMORY);
        exc = ruby_vm_special_exception_copy(exc);
    }
    ec->errinfo = exc;
    EC_JUMP_TAG(ec, TAG_RAISE);
}

static void
rb_aligned_free(void *ptr, size_t size)
{
#if defined __MINGW32__
    __mingw_aligned_free(ptr);
#elif defined _WIN32
    _aligned_free(ptr);
#elif defined(HAVE_POSIX_MEMALIGN) || defined(HAVE_MEMALIGN)
    free(ptr);
#else
    free(((void**)ptr)[-1]);
#endif
}

static inline size_t
objspace_malloc_size(rb_objspace_t *objspace, void *ptr, size_t hint)
{
#ifdef HAVE_MALLOC_USABLE_SIZE
    return malloc_usable_size(ptr);
#else
    return hint;
#endif
}

enum memop_type {
    MEMOP_TYPE_MALLOC  = 0,
    MEMOP_TYPE_FREE,
    MEMOP_TYPE_REALLOC
};

static inline void
atomic_sub_nounderflow(size_t *var, size_t sub)
{
    print_for_debug(__func__);
}

static void
objspace_malloc_gc_stress(rb_objspace_t *objspace)
{
    if (ruby_gc_stressful && ruby_native_thread_p()) {
        unsigned int reason = (GPR_FLAG_IMMEDIATE_MARK | GPR_FLAG_IMMEDIATE_SWEEP |
                               GPR_FLAG_STRESS | GPR_FLAG_MALLOC);

        if (gc_stress_full_mark_after_malloc_p()) {
            reason |= GPR_FLAG_FULL_MARK;
        }
        garbage_collect_with_gvl(objspace, reason);
    }
}

static inline bool
objspace_malloc_increase_report(rb_objspace_t *objspace, void *mem, size_t new_size, size_t old_size, enum memop_type type)
{
    if (0) fprintf(stderr, "increase - ptr: %p, type: %s, new_size: %"PRIdSIZE", old_size: %"PRIdSIZE"\n",
                   mem,
                   type == MEMOP_TYPE_MALLOC  ? "malloc" :
                   type == MEMOP_TYPE_FREE    ? "free  " :
                   type == MEMOP_TYPE_REALLOC ? "realloc": "error",
                   new_size, old_size);
    return false;
}

static bool
objspace_malloc_increase_body(rb_objspace_t *objspace, void *mem, size_t new_size, size_t old_size, enum memop_type type)
{
    if (new_size > old_size) {
        ATOMIC_SIZE_ADD(malloc_increase, new_size - old_size);
#if RGENGC_ESTIMATE_OLDMALLOC
        ATOMIC_SIZE_ADD(objspace->rgengc.oldmalloc_increase, new_size - old_size);
#endif
    }
    else {
        atomic_sub_nounderflow(&malloc_increase, old_size - new_size);
#if RGENGC_ESTIMATE_OLDMALLOC
        atomic_sub_nounderflow(&objspace->rgengc.oldmalloc_increase, old_size - new_size);
#endif
    }

    if (type == MEMOP_TYPE_MALLOC) {
      retry:
        if (malloc_increase > malloc_limit && ruby_native_thread_p() && !dont_gc_val()) {
            if (ruby_thread_has_gvl_p() && is_lazy_sweeping(objspace)) {
                gc_rest(objspace); /* gc_rest can reduce malloc_increase */
                goto retry;
            }
            garbage_collect_with_gvl(objspace, GPR_FLAG_MALLOC);
        }
    }

#if MALLOC_ALLOCATED_SIZE
    if (new_size >= old_size) {
        ATOMIC_SIZE_ADD(objspace->malloc_params.allocated_size, new_size - old_size);
    }
    else {
        size_t dec_size = old_size - new_size;
        size_t allocated_size = objspace->malloc_params.allocated_size;

#if MALLOC_ALLOCATED_SIZE_CHECK
        if (allocated_size < dec_size) {
            rb_bug("objspace_malloc_increase: underflow malloc_params.allocated_size.");
        }
#endif
        atomic_sub_nounderflow(&objspace->malloc_params.allocated_size, dec_size);
    }

    switch (type) {
      case MEMOP_TYPE_MALLOC:
        ATOMIC_SIZE_INC(objspace->malloc_params.allocations);
        break;
      case MEMOP_TYPE_FREE:
        {
            size_t allocations = objspace->malloc_params.allocations;
            if (allocations > 0) {
                atomic_sub_nounderflow(&objspace->malloc_params.allocations, 1);
            }
#if MALLOC_ALLOCATED_SIZE_CHECK
            else {
                GC_ASSERT(objspace->malloc_params.allocations > 0);
            }
#endif
        }
        break;
      case MEMOP_TYPE_REALLOC: /* ignore */ break;
    }
#endif
    return true;
}

#define objspace_malloc_increase(...) \
    for (bool malloc_increase_done = objspace_malloc_increase_report(__VA_ARGS__); \
         !malloc_increase_done; \
         malloc_increase_done = objspace_malloc_increase_body(__VA_ARGS__))

struct malloc_obj_info { /* 4 words */
    size_t size;
#if USE_GC_MALLOC_OBJ_INFO_DETAILS
    size_t gen;
    const char *file;
    size_t line;
#endif
};

#if USE_GC_MALLOC_OBJ_INFO_DETAILS
const char *ruby_malloc_info_file;
int ruby_malloc_info_line;
#endif

static inline size_t
objspace_malloc_prepare(rb_objspace_t *objspace, size_t size)
{
    if (size == 0) size = 1;

#if CALC_EXACT_MALLOC_SIZE
    size += sizeof(struct malloc_obj_info);
#endif

    return size;
}

static bool
malloc_during_gc_p(rb_objspace_t *objspace)
{
    /* malloc is not allowed during GC when we're not using multiple ractors
     * (since ractors can run while another thread is sweeping) and when we
     * have the GVL (since if we don't have the GVL, we'll try to acquire the
     * GVL which will block and ensure the other thread finishes GC). */
    return during_gc && !dont_gc_val() && !rb_multi_ractor_p() && ruby_thread_has_gvl_p();
}

static inline void *
objspace_malloc_fixup(rb_objspace_t *objspace, void *mem, size_t size)
{
    size = objspace_malloc_size(objspace, mem, size);
    objspace_malloc_increase(objspace, mem, size, 0, MEMOP_TYPE_MALLOC);

#if CALC_EXACT_MALLOC_SIZE
    {
        struct malloc_obj_info *info = mem;
        info->size = size;
#if USE_GC_MALLOC_OBJ_INFO_DETAILS
        info->gen = objspace->profile.count;
        info->file = ruby_malloc_info_file;
        info->line = info->file ? ruby_malloc_info_line : 0;
#endif
        mem = info + 1;
    }
#endif

    return mem;
}

#if defined(__GNUC__) && RUBY_DEBUG
#define RB_BUG_INSTEAD_OF_RB_MEMERROR 1
#endif

#ifndef RB_BUG_INSTEAD_OF_RB_MEMERROR
# define RB_BUG_INSTEAD_OF_RB_MEMERROR 0
#endif

#define GC_MEMERROR(...) \
    ((RB_BUG_INSTEAD_OF_RB_MEMERROR+0) ? rb_bug("" __VA_ARGS__) : rb_memerror())

#define TRY_WITH_GC(siz, expr) do {                          \
        const gc_profile_record_flag gpr =                   \
            GPR_FLAG_FULL_MARK           |                   \
            GPR_FLAG_IMMEDIATE_MARK      |                   \
            GPR_FLAG_IMMEDIATE_SWEEP     |                   \
            GPR_FLAG_MALLOC;                                 \
        objspace_malloc_gc_stress(objspace);                 \
                                                             \
        if (LIKELY((expr))) {                                \
            /* Success on 1st try */                         \
        }                                                    \
        else if (!garbage_collect_with_gvl(objspace, gpr)) { \
            /* @shyouhei thinks this doesn't happen */       \
            GC_MEMERROR("TRY_WITH_GC: could not GC");        \
        }                                                    \
        else if ((expr)) {                                   \
            /* Success on 2nd try */                         \
        }                                                    \
        else {                                               \
            GC_MEMERROR("TRY_WITH_GC: could not allocate:"   \
                        "%"PRIdSIZE" bytes for %s",          \
                        siz, # expr);                        \
        }                                                    \
    } while (0)

static void
check_malloc_not_in_gc(rb_objspace_t *objspace, const char *msg)
{
    if (UNLIKELY(malloc_during_gc_p(objspace))) {
        dont_gc_on();
        during_gc = false;
        rb_bug("Cannot %s during GC", msg);
    }
}

/* these shouldn't be called directly.
 * objspace_* functions do not check allocation size.
 */
static void *
objspace_xmalloc0(rb_objspace_t *objspace, size_t size)
{
    check_malloc_not_in_gc(objspace, "malloc");

    void *mem;

    size = objspace_malloc_prepare(objspace, size);
    TRY_WITH_GC(size, mem = malloc(size));
    RB_DEBUG_COUNTER_INC(heap_xmalloc);
    return objspace_malloc_fixup(objspace, mem, size);
}

static inline size_t
xmalloc2_size(const size_t count, const size_t elsize)
{
    return size_mul_or_raise(count, elsize, rb_eArgError);
}

static void *
objspace_xrealloc(rb_objspace_t *objspace, void *ptr, size_t new_size, size_t old_size)
{
    check_malloc_not_in_gc(objspace, "realloc");

    void *mem;

    if (!ptr) return objspace_xmalloc0(objspace, new_size);

    /*
     * The behavior of realloc(ptr, 0) is implementation defined.
     * Therefore we don't use realloc(ptr, 0) for portability reason.
     * see http://www.open-std.org/jtc1/sc22/wg14/www/docs/dr_400.htm
     */
    if (new_size == 0) {
        if ((mem = objspace_xmalloc0(objspace, 0)) != NULL) {
            /*
             * - OpenBSD's malloc(3) man page says that when 0 is passed, it
             *   returns a non-NULL pointer to an access-protected memory page.
             *   The returned pointer cannot be read / written at all, but
             *   still be a valid argument of free().
             *
             *   https://man.openbsd.org/malloc.3
             *
             * - Linux's malloc(3) man page says that it _might_ perhaps return
             *   a non-NULL pointer when its argument is 0.  That return value
             *   is safe (and is expected) to be passed to free().
             *
             *   https://man7.org/linux/man-pages/man3/malloc.3.html
             *
             * - As I read the implementation jemalloc's malloc() returns fully
             *   normal 16 bytes memory region when its argument is 0.
             *
             * - As I read the implementation musl libc's malloc() returns
             *   fully normal 32 bytes memory region when its argument is 0.
             *
             * - Other malloc implementations can also return non-NULL.
             */
            objspace_xfree(objspace, ptr, old_size);
            return mem;
        }
        else {
            /*
             * It is dangerous to return NULL here, because that could lead to
             * RCE.  Fallback to 1 byte instead of zero.
             *
             * https://cve.mitre.org/cgi-bin/cvename.cgi?name=CVE-2019-11932
             */
            new_size = 1;
        }
    }

#if CALC_EXACT_MALLOC_SIZE
    {
        struct malloc_obj_info *info = (struct malloc_obj_info *)ptr - 1;
        new_size += sizeof(struct malloc_obj_info);
        ptr = info;
        old_size = info->size;
    }
#endif

    old_size = objspace_malloc_size(objspace, ptr, old_size);
    TRY_WITH_GC(new_size, mem = RB_GNUC_EXTENSION_BLOCK(realloc(ptr, new_size)));
    new_size = objspace_malloc_size(objspace, mem, new_size);

#if CALC_EXACT_MALLOC_SIZE
    {
        struct malloc_obj_info *info = mem;
        info->size = new_size;
        mem = info + 1;
    }
#endif

    objspace_malloc_increase(objspace, mem, new_size, old_size, MEMOP_TYPE_REALLOC);

    RB_DEBUG_COUNTER_INC(heap_xrealloc);
    return mem;
}

#if CALC_EXACT_MALLOC_SIZE && USE_GC_MALLOC_OBJ_INFO_DETAILS

#define MALLOC_INFO_GEN_SIZE 100
#define MALLOC_INFO_SIZE_SIZE 10
static size_t malloc_info_gen_cnt[MALLOC_INFO_GEN_SIZE];
static size_t malloc_info_gen_size[MALLOC_INFO_GEN_SIZE];
static size_t malloc_info_size[MALLOC_INFO_SIZE_SIZE+1];
static st_table *malloc_info_file_table;

static int
mmalloc_info_file_i(st_data_t key, st_data_t val, st_data_t dmy)
{
    const char *file = (void *)key;
    const size_t *data = (void *)val;

    fprintf(stderr, "%s\t%"PRIdSIZE"\t%"PRIdSIZE"\n", file, data[0], data[1]);

    return ST_CONTINUE;
}

__attribute__((destructor))
void
rb_malloc_info_show_results(void)
{
    int i;

    fprintf(stderr, "* malloc_info gen statistics\n");
    for (i=0; i<MALLOC_INFO_GEN_SIZE; i++) {
        if (i == MALLOC_INFO_GEN_SIZE-1) {
            fprintf(stderr, "more\t%"PRIdSIZE"\t%"PRIdSIZE"\n", malloc_info_gen_cnt[i], malloc_info_gen_size[i]);
        }
        else {
            fprintf(stderr, "%d\t%"PRIdSIZE"\t%"PRIdSIZE"\n", i, malloc_info_gen_cnt[i], malloc_info_gen_size[i]);
        }
    }

    fprintf(stderr, "* malloc_info size statistics\n");
    for (i=0; i<MALLOC_INFO_SIZE_SIZE; i++) {
        int s = 16 << i;
        fprintf(stderr, "%d\t%"PRIdSIZE"\n", s, malloc_info_size[i]);
    }
    fprintf(stderr, "more\t%"PRIdSIZE"\n", malloc_info_size[i]);

    if (malloc_info_file_table) {
        fprintf(stderr, "* malloc_info file statistics\n");
        st_foreach(malloc_info_file_table, mmalloc_info_file_i, 0);
    }
}
#else
void
rb_malloc_info_show_results(void)
{
}
#endif

static void
objspace_xfree(rb_objspace_t *objspace, void *ptr, size_t old_size)
{
    if (!ptr) {
        /*
         * ISO/IEC 9899 says "If ptr is a null pointer, no action occurs" since
         * its first version.  We would better follow.
         */
        return;
    }
#if CALC_EXACT_MALLOC_SIZE
    struct malloc_obj_info *info = (struct malloc_obj_info *)ptr - 1;
    ptr = info;
    old_size = info->size;

#if USE_GC_MALLOC_OBJ_INFO_DETAILS
    {
        int gen = (int)(objspace->profile.count - info->gen);
        int gen_index = gen >= MALLOC_INFO_GEN_SIZE ? MALLOC_INFO_GEN_SIZE-1 : gen;
        int i;

        malloc_info_gen_cnt[gen_index]++;
        malloc_info_gen_size[gen_index] += info->size;

        for (i=0; i<MALLOC_INFO_SIZE_SIZE; i++) {
            size_t s = 16 << i;
            if (info->size <= s) {
                malloc_info_size[i]++;
                goto found;
            }
        }
        malloc_info_size[i]++;
      found:;

        {
            st_data_t key = (st_data_t)info->file, d;
            size_t *data;

            if (malloc_info_file_table == NULL) {
                malloc_info_file_table = st_init_numtable_with_size(1024);
            }
            if (st_lookup(malloc_info_file_table, key, &d)) {
                /* hit */
                data = (size_t *)d;
            }
            else {
                data = malloc(xmalloc2_size(2, sizeof(size_t)));
                if (data == NULL) rb_bug("objspace_xfree: can not allocate memory");
                data[0] = data[1] = 0;
                st_insert(malloc_info_file_table, key, (st_data_t)data);
            }
            data[0] ++;
            data[1] += info->size;
        };
        if (0 && gen >= 2) {         /* verbose output */
            if (info->file) {
                fprintf(stderr, "free - size:%"PRIdSIZE", gen:%d, pos: %s:%"PRIdSIZE"\n",
                        info->size, gen, info->file, info->line);
            }
            else {
                fprintf(stderr, "free - size:%"PRIdSIZE", gen:%d\n",
                        info->size, gen);
            }
        }
    }
#endif
#endif
    old_size = objspace_malloc_size(objspace, ptr, old_size);

    objspace_malloc_increase(objspace, ptr, 0, old_size, MEMOP_TYPE_FREE) {
        free(ptr);
        ptr = NULL;
        RB_DEBUG_COUNTER_INC(heap_xfree);
    }
}

void
ruby_malloc_size_overflow(size_t count, size_t elsize)
{
    rb_raise(rb_eArgError,
             "malloc: possible integer overflow (%"PRIuSIZE"*%"PRIuSIZE")",
             count, elsize);
}

#ifdef ruby_sized_xfree
#undef ruby_sized_xfree
#endif
void
ruby_sized_xfree(void *x, size_t size)
{
    if (LIKELY(x)) {
        /* It's possible for a C extension's pthread destructor function set by pthread_key_create
         * to be called after ruby_vm_destruct and attempt to free memory. Fall back to mimfree in
         * that case. */
        if (LIKELY(GET_VM())) {
            objspace_xfree(&rb_objspace, x, size);
        }
        else {
            ruby_mimfree(x);
        }
    }
}

void
ruby_xfree(void *x)
{
    ruby_sized_xfree(x, 0);
}

void *
rb_xmalloc_mul_add(size_t x, size_t y, size_t z) /* x * y + z */
{
    size_t w = size_mul_add_or_raise(x, y, z, rb_eArgError);
    return ruby_xmalloc(w);
}

void *
rb_xcalloc_mul_add(size_t x, size_t y, size_t z) /* x * y + z */
{
    size_t w = size_mul_add_or_raise(x, y, z, rb_eArgError);
    return ruby_xcalloc(w, 1);
}

void *
rb_xrealloc_mul_add(const void *p, size_t x, size_t y, size_t z) /* x * y + z */
{
    size_t w = size_mul_add_or_raise(x, y, z, rb_eArgError);
    return ruby_xrealloc((void *)p, w);
}

void *
rb_xmalloc_mul_add_mul(size_t x, size_t y, size_t z, size_t w) /* x * y + z * w */
{
    size_t u = size_mul_add_mul_or_raise(x, y, z, w, rb_eArgError);
    return ruby_xmalloc(u);
}

void *
rb_xcalloc_mul_add_mul(size_t x, size_t y, size_t z, size_t w) /* x * y + z * w */
{
    size_t u = size_mul_add_mul_or_raise(x, y, z, w, rb_eArgError);
    return ruby_xcalloc(u, 1);
}

/* Mimic ruby_xmalloc, but need not rb_objspace.
 * should return pointer suitable for ruby_xfree
 */
void *
ruby_mimmalloc(size_t size)
{
    void *mem;
#if CALC_EXACT_MALLOC_SIZE
    size += sizeof(struct malloc_obj_info);
#endif
    mem = malloc(size);
#if CALC_EXACT_MALLOC_SIZE
    if (!mem) {
        return NULL;
    }
    else
    /* set 0 for consistency of allocated_size/allocations */
    {
        struct malloc_obj_info *info = mem;
        info->size = 0;
#if USE_GC_MALLOC_OBJ_INFO_DETAILS
        info->gen = 0;
        info->file = NULL;
        info->line = 0;
#endif
        mem = info + 1;
    }
#endif
    return mem;
}

void
ruby_mimfree(void *ptr)
{
#if CALC_EXACT_MALLOC_SIZE
    struct malloc_obj_info *info = (struct malloc_obj_info *)ptr - 1;
    ptr = info;
#endif
    free(ptr);
}

#if MALLOC_ALLOCATED_SIZE
/*
 *  call-seq:
 *     GC.malloc_allocated_size -> Integer
 *
 *  Returns the size of memory allocated by malloc().
 *
 *  Only available if ruby was built with +CALC_EXACT_MALLOC_SIZE+.
 */

static VALUE
gc_malloc_allocated_size(VALUE self)
{
    print_for_debug("gc_malloc_allocated_size");
    return 0;
}

/*
 *  call-seq:
 *     GC.malloc_allocations -> Integer
 *
 *  Returns the number of malloc() allocations.
 *
 *  Only available if ruby was built with +CALC_EXACT_MALLOC_SIZE+.
 */

static VALUE
gc_malloc_allocations(VALUE self)
{
    print_for_debug("gc_malloc_allocations");
    return 0;
}
#endif

void
rb_gc_adjust_memory_usage(ssize_t diff)
{
    print_for_debug("rb_gc_adjust_memory_usage");
}

/*
  ------------------------------ GC profiler ------------------------------
*/

#define GC_PROFILE_RECORD_DEFAULT_SIZE 100

static double
getrusage_time(void)
{
    print_for_debug(__func__);
    return 0;
}


static inline void
gc_prof_setup_new_record(rb_objspace_t *objspace, unsigned int reason)
{
    print_for_debug("gc_prof_setup_new_record");
}

static inline void
gc_prof_timer_start(rb_objspace_t *objspace)
{
    print_for_debug("gc_prof_timer_start");
}

static inline void
gc_prof_timer_stop(rb_objspace_t *objspace)
{
    print_for_debug("gc_prof_timer_stop");
}

#define RUBY_DTRACE_GC_HOOK(name) \
    do {if (RUBY_DTRACE_GC_##name##_ENABLED()) RUBY_DTRACE_GC_##name();} while (0)
static inline void
gc_prof_mark_timer_start(rb_objspace_t *objspace)
{
    print_for_debug("gc_prof_mark_timer_start");
}

static inline void
gc_prof_mark_timer_stop(rb_objspace_t *objspace)
{
    print_for_debug("gc_prof_mark_timer_stop");
}

static inline void
gc_prof_sweep_timer_start(rb_objspace_t *objspace)
{
    print_for_debug("gc_prof_sweep_timer_start");
}

static inline void
gc_prof_sweep_timer_stop(rb_objspace_t *objspace)
{
    print_for_debug("gc_prof_sweep_timer_stop");
}

static inline void
gc_prof_set_malloc_info(rb_objspace_t *objspace)
{
    print_for_debug("gc_prof_set_malloc_info");
}

static inline void
gc_prof_set_heap_info(rb_objspace_t *objspace)
{
    print_for_debug("gc_prof_set_heap_info");
}

/*
 *  call-seq:
 *    GC::Profiler.clear          -> nil
 *
 *  Clears the \GC profiler data.
 *
 */

static VALUE
gc_profile_clear(VALUE _)
{
    print_for_debug("gc_profile_clear");
    return 0;
}

/*
 *  call-seq:
 *     GC::Profiler.raw_data	-> [Hash, ...]
 *
 *  Returns an Array of individual raw profile data Hashes ordered
 *  from earliest to latest by +:GC_INVOKE_TIME+.
 *
 *  For example:
 *
 *    [
 *	{
 *	   :GC_TIME=>1.3000000000000858e-05,
 *	   :GC_INVOKE_TIME=>0.010634999999999999,
 *	   :HEAP_USE_SIZE=>289640,
 *	   :HEAP_TOTAL_SIZE=>588960,
 *	   :HEAP_TOTAL_OBJECTS=>14724,
 *	   :GC_IS_MARKED=>false
 *	},
 *      # ...
 *    ]
 *
 *  The keys mean:
 *
 *  +:GC_TIME+::
 *	Time elapsed in seconds for this GC run
 *  +:GC_INVOKE_TIME+::
 *	Time elapsed in seconds from startup to when the GC was invoked
 *  +:HEAP_USE_SIZE+::
 *	Total bytes of heap used
 *  +:HEAP_TOTAL_SIZE+::
 *	Total size of heap in bytes
 *  +:HEAP_TOTAL_OBJECTS+::
 *	Total number of objects
 *  +:GC_IS_MARKED+::
 *	Returns +true+ if the GC is in mark phase
 *
 *  If ruby was built with +GC_PROFILE_MORE_DETAIL+, you will also have access
 *  to the following hash keys:
 *
 *  +:GC_MARK_TIME+::
 *  +:GC_SWEEP_TIME+::
 *  +:ALLOCATE_INCREASE+::
 *  +:ALLOCATE_LIMIT+::
 *  +:HEAP_USE_PAGES+::
 *  +:HEAP_LIVE_OBJECTS+::
 *  +:HEAP_FREE_OBJECTS+::
 *  +:HAVE_FINALIZE+::
 *
 */

static VALUE
gc_profile_record_get(VALUE _)
{
    print_for_debug("gc_profile_record_get");
    return 0;
}

#if GC_PROFILE_MORE_DETAIL
#define MAJOR_REASON_MAX 0x10

static char *
gc_profile_dump_major_reason(unsigned int flags, char *buff)
{
    print_for_debug("gc_profile_dump_major_reason");
    return 0;
}
#endif

/*
 *  call-seq:
 *     GC::Profiler.result  -> String
 *
 *  Returns a profile data report such as:
 *
 *    GC 1 invokes.
 *    Index    Invoke Time(sec)       Use Size(byte)     Total Size(byte)         Total Object                    GC time(ms)
 *        1               0.012               159240               212940                10647         0.00000000000001530000
 */

static VALUE
gc_profile_result(VALUE _)
{
    print_for_debug("gc_profile_result");
    return 0;
}

/*
 *  call-seq:
 *     GC::Profiler.report
 *     GC::Profiler.report(io)
 *
 *  Writes the GC::Profiler.result to <tt>$stdout</tt> or the given IO object.
 *
 */

static VALUE
gc_profile_report(int argc, VALUE *argv, VALUE self)
{
    print_for_debug("gc_profile_report");
    return 0;
}

/*
 *  call-seq:
 *     GC::Profiler.total_time	-> float
 *
 *  The total time used for garbage collection in seconds
 */

static VALUE
gc_profile_total_time(VALUE self)
{
    print_for_debug("gc_profile_total_time");
    return 0;
}

/*
 *  call-seq:
 *    GC::Profiler.enabled?	-> true or false
 *
 *  The current status of \GC profile mode.
 */

static VALUE
gc_profile_enable_get(VALUE self)
{
    print_for_debug("gc_profile_enable_get");
    return 0;
}

/*
 *  call-seq:
 *    GC::Profiler.enable	-> nil
 *
 *  Starts the \GC profiler.
 *
 */

static VALUE
gc_profile_enable(VALUE _)
{
    print_for_debug("gc_profile_enable");
    return 0;
}

/*
 *  call-seq:
 *    GC::Profiler.disable	-> nil
 *
 *  Stops the \GC profiler.
 *
 */

static VALUE
gc_profile_disable(VALUE _)
{
    print_for_debug("gc_profile_disable");
    return 0;
}

/*
  ------------------------------ DEBUG ------------------------------
*/

const char *
rb_method_type_name(rb_method_type_t type)
{
    switch (type) {
      case VM_METHOD_TYPE_ISEQ:           return "iseq";
      case VM_METHOD_TYPE_ATTRSET:        return "attrest";
      case VM_METHOD_TYPE_IVAR:           return "ivar";
      case VM_METHOD_TYPE_BMETHOD:        return "bmethod";
      case VM_METHOD_TYPE_ALIAS:          return "alias";
      case VM_METHOD_TYPE_REFINED:        return "refined";
      case VM_METHOD_TYPE_CFUNC:          return "cfunc";
      case VM_METHOD_TYPE_ZSUPER:         return "zsuper";
      case VM_METHOD_TYPE_MISSING:        return "missing";
      case VM_METHOD_TYPE_OPTIMIZED:      return "optimized";
      case VM_METHOD_TYPE_UNDEF:          return "undef";
      case VM_METHOD_TYPE_NOTIMPLEMENTED: return "notimplemented";
    }
    rb_bug("rb_method_type_name: unreachable (type: %d)", type);
}

#define BUFF_ARGS buff + pos, buff_size - pos
#define APPEND_F(...) if ((pos += snprintf(BUFF_ARGS, "" __VA_ARGS__)) >= buff_size) goto end
#define APPEND_S(s) do { \
        if ((pos + (int)rb_strlen_lit(s)) >= buff_size) { \
            goto end; \
        } \
        else { \
            memcpy(buff + pos, (s), rb_strlen_lit(s) + 1); \
        } \
    } while (0)
#define C(c, s) ((c) != 0 ? (s) : " ")

#undef C

const char *
rb_raw_obj_info(char *const buff, const size_t buff_size, VALUE obj)
{
    print_for_debug("rb_raw_obj_info");
    return 0;
}

#undef APPEND_S
#undef APPEND_F
#undef BUFF_ARGS

static const char *
obj_info(VALUE obj)
{
    print_for_debug("obj_info");
    return 0;
}

static const char *
obj_info_basic(VALUE obj)
{
    print_for_debug("obj_info_basic");
    return 0;
}

const char *
rb_obj_info(VALUE obj)
{
    print_for_debug("rb_obj_info");
    return 0;
}

void
rb_obj_info_dump(VALUE obj)
{
    print_for_debug("rb_obj_info_dump");
}

void
rb_obj_info_dump_loc(VALUE obj, const char *file, int line, const char *func)
{
    print_for_debug("rb_obj_info_dump_loc");
}

#if GC_DEBUG

void
rb_gcdebug_print_obj_condition(VALUE obj)
{
    print_for_debug("rb_gcdebug_print_obj_condition");
    return 0;
}

static VALUE
gcdebug_sentinel(RB_BLOCK_CALL_FUNC_ARGLIST(obj, name))
{
    print_for_debug("gcdebug_sentinel");
    return 0;
}

void
rb_gcdebug_sentinel(VALUE obj, const char *name)
{
    print_for_debug("rb_gcdebug_sentinel");
    return 0;
}

#endif /* GC_DEBUG */

/*
 *  call-seq:
 *    GC.add_stress_to_class(class[, ...])
 *
 *  Raises NoMemoryError when allocating an instance of the given classes.
 *
 */
static VALUE
rb_gcdebug_add_stress_to_class(int argc, VALUE *argv, VALUE self)
{
    print_for_debug("rb_gcdebug_add_stress_to_class");
    return 0;
}

/*
 *  call-seq:
 *    GC.remove_stress_to_class(class[, ...])
 *
 *  No longer raises NoMemoryError when allocating an instance of the
 *  given classes.
 *
 */
static VALUE
rb_gcdebug_remove_stress_to_class(int argc, VALUE *argv, VALUE self)
{
    print_for_debug("rb_gcdebug_remove_stress_to_class");
    return 0;
}

/*
 * Document-module: ObjectSpace
 *
 *  The ObjectSpace module contains a number of routines
 *  that interact with the garbage collection facility and allow you to
 *  traverse all living objects with an iterator.
 *
 *  ObjectSpace also provides support for object finalizers, procs that will be
 *  called when a specific object is about to be destroyed by garbage
 *  collection. See the documentation for
 *  <code>ObjectSpace.define_finalizer</code> for important information on
 *  how to use this method correctly.
 *
 *     a = "A"
 *     b = "B"
 *
 *     ObjectSpace.define_finalizer(a, proc {|id| puts "Finalizer one on #{id}" })
 *     ObjectSpace.define_finalizer(b, proc {|id| puts "Finalizer two on #{id}" })
 *
 *     a = nil
 *     b = nil
 *
 *  _produces:_
 *
 *     Finalizer two on 537763470
 *     Finalizer one on 537763480
 */

/*  Document-class: GC::Profiler
 *
 *  The GC profiler provides access to information on GC runs including time,
 *  length and object space size.
 *
 *  Example:
 *
 *    GC::Profiler.enable
 *
 *    require 'rdoc/rdoc'
 *
 *    GC::Profiler.report
 *
 *    GC::Profiler.disable
 *
 *  See also GC.count, GC.malloc_allocated_size and GC.malloc_allocations
 */

#include "gc.rbinc"

void
Init_GC(void)
{
#undef rb_intern
    malloc_offset = gc_compute_malloc_offset();

    VALUE rb_mObjSpace;
    VALUE rb_mProfiler;
    VALUE gc_constants;

    rb_mGC = rb_define_module("GC");

    gc_constants = rb_hash_new();
    rb_hash_aset(gc_constants, ID2SYM(rb_intern("DEBUG")), RBOOL(GC_DEBUG));
    rb_hash_aset(gc_constants, ID2SYM(rb_intern("BASE_SLOT_SIZE")), SIZET2NUM(BASE_SLOT_SIZE - RVALUE_OVERHEAD));
    rb_hash_aset(gc_constants, ID2SYM(rb_intern("RVALUE_OVERHEAD")), SIZET2NUM(RVALUE_OVERHEAD));
    rb_hash_aset(gc_constants, ID2SYM(rb_intern("RVALUE_SIZE")), SIZET2NUM(sizeof(RVALUE)));
    rb_hash_aset(gc_constants, ID2SYM(rb_intern("HEAP_PAGE_OBJ_LIMIT")), SIZET2NUM(HEAP_PAGE_OBJ_LIMIT));
    rb_hash_aset(gc_constants, ID2SYM(rb_intern("HEAP_PAGE_BITMAP_SIZE")), SIZET2NUM(HEAP_PAGE_BITMAP_SIZE));
    rb_hash_aset(gc_constants, ID2SYM(rb_intern("HEAP_PAGE_SIZE")), SIZET2NUM(HEAP_PAGE_SIZE));
    rb_hash_aset(gc_constants, ID2SYM(rb_intern("SIZE_POOL_COUNT")), LONG2FIX(SIZE_POOL_COUNT));
    rb_hash_aset(gc_constants, ID2SYM(rb_intern("RVARGC_MAX_ALLOCATE_SIZE")), LONG2FIX(size_pool_slot_size(SIZE_POOL_COUNT - 1)));
    rb_hash_aset(gc_constants, ID2SYM(rb_intern("RVALUE_OLD_AGE")), LONG2FIX(RVALUE_OLD_AGE));
    if (RB_BUG_INSTEAD_OF_RB_MEMERROR+0) {
        rb_hash_aset(gc_constants, ID2SYM(rb_intern("RB_BUG_INSTEAD_OF_RB_MEMERROR")), Qtrue);
    }
    OBJ_FREEZE(gc_constants);
    /* Internal constants in the garbage collector. */
    rb_define_const(rb_mGC, "INTERNAL_CONSTANTS", gc_constants);

    rb_mProfiler = rb_define_module_under(rb_mGC, "Profiler");
    rb_define_singleton_method(rb_mProfiler, "enabled?", gc_profile_enable_get, 0);
    rb_define_singleton_method(rb_mProfiler, "enable", gc_profile_enable, 0);
    rb_define_singleton_method(rb_mProfiler, "raw_data", gc_profile_record_get, 0);
    rb_define_singleton_method(rb_mProfiler, "disable", gc_profile_disable, 0);
    rb_define_singleton_method(rb_mProfiler, "clear", gc_profile_clear, 0);
    rb_define_singleton_method(rb_mProfiler, "result", gc_profile_result, 0);
    rb_define_singleton_method(rb_mProfiler, "report", gc_profile_report, -1);
    rb_define_singleton_method(rb_mProfiler, "total_time", gc_profile_total_time, 0);

    rb_mObjSpace = rb_define_module("ObjectSpace");

    rb_define_module_function(rb_mObjSpace, "each_object", os_each_obj, -1);

    rb_define_module_function(rb_mObjSpace, "define_finalizer", define_final, -1);
    rb_define_module_function(rb_mObjSpace, "undefine_finalizer", undefine_final, 1);

    rb_define_module_function(rb_mObjSpace, "_id2ref", os_id2ref, 1);

    rb_vm_register_special_exception(ruby_error_nomemory, rb_eNoMemError, "failed to allocate memory");

    rb_define_method(rb_cBasicObject, "__id__", rb_obj_id, 0);
    rb_define_method(rb_mKernel, "object_id", rb_obj_id, 0);

    rb_define_module_function(rb_mObjSpace, "count_objects", count_objects, -1);

    /* internal methods */
    rb_define_singleton_method(rb_mGC, "verify_internal_consistency", gc_verify_internal_consistency_m, 0);
#if MALLOC_ALLOCATED_SIZE
    rb_define_singleton_method(rb_mGC, "malloc_allocated_size", gc_malloc_allocated_size, 0);
    rb_define_singleton_method(rb_mGC, "malloc_allocations", gc_malloc_allocations, 0);
#endif

    if (GC_COMPACTION_SUPPORTED) {
        rb_define_singleton_method(rb_mGC, "compact", gc_compact, 0);
        rb_define_singleton_method(rb_mGC, "auto_compact", gc_get_auto_compact, 0);
        rb_define_singleton_method(rb_mGC, "auto_compact=", gc_set_auto_compact, 1);
        rb_define_singleton_method(rb_mGC, "latest_compact_info", gc_compact_stats, 0);
    }
    else {
        rb_define_singleton_method(rb_mGC, "compact", rb_f_notimplement, 0);
        rb_define_singleton_method(rb_mGC, "auto_compact", rb_f_notimplement, 0);
        rb_define_singleton_method(rb_mGC, "auto_compact=", rb_f_notimplement, 1);
        rb_define_singleton_method(rb_mGC, "latest_compact_info", rb_f_notimplement, 0);
        /* When !GC_COMPACTION_SUPPORTED, this method is not defined in gc.rb */
        rb_define_singleton_method(rb_mGC, "verify_compaction_references", rb_f_notimplement, -1);
    }

    if (GC_DEBUG_STRESS_TO_CLASS) {
        rb_define_singleton_method(rb_mGC, "add_stress_to_class", rb_gcdebug_add_stress_to_class, -1);
        rb_define_singleton_method(rb_mGC, "remove_stress_to_class", rb_gcdebug_remove_stress_to_class, -1);
    }

    {
        VALUE opts;
        /* \GC build options */
        rb_define_const(rb_mGC, "OPTS", opts = rb_ary_new());
#define OPT(o) if (o) rb_ary_push(opts, rb_fstring_lit(#o))
        OPT(GC_DEBUG);
        OPT(USE_RGENGC);
        OPT(RGENGC_DEBUG);
        OPT(RGENGC_CHECK_MODE);
        OPT(RGENGC_PROFILE);
        OPT(RGENGC_ESTIMATE_OLDMALLOC);
        OPT(GC_PROFILE_MORE_DETAIL);
        OPT(GC_ENABLE_LAZY_SWEEP);
        OPT(CALC_EXACT_MALLOC_SIZE);
        OPT(MALLOC_ALLOCATED_SIZE);
        OPT(MALLOC_ALLOCATED_SIZE_CHECK);
        OPT(GC_PROFILE_DETAIL_MEMORY);
        OPT(GC_COMPACTION_SUPPORTED);
#undef OPT
        OBJ_FREEZE(opts);
    }
}

void *
ruby_xmalloc(size_t size)
{
    return objspace_xmalloc0(&rb_objspace, size);
}

void *
ruby_xmalloc2(size_t n, size_t size)
{
    return objspace_xmalloc0(&rb_objspace, xmalloc2_size(n, size));
}

void *
ruby_xcalloc(size_t n, size_t size)
{
    size = xmalloc2_size(n, size);
    rb_objspace_t *objspace = &rb_objspace;
    void *mem;

    size = objspace_malloc_prepare(objspace, size);
    TRY_WITH_GC(size, mem = calloc1(size));
    return objspace_malloc_fixup(objspace, mem, size);
}

void *
ruby_xrealloc(void *ptr, size_t new_size)
{
    return objspace_xrealloc(&rb_objspace, ptr, new_size, 0);
}

void *
ruby_xrealloc2(void *ptr, size_t n, size_t new_size)
{
    size_t len = size_mul_or_raise(n, new_size, rb_eArgError);
    return objspace_xrealloc(&rb_objspace, ptr, len, 0 * new_size);
}
