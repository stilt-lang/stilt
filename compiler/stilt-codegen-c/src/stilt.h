/* The runtime's fast paths as static inline C, which the C compiler inlines into each function
 * of a release build: allocating a data object from the thread's pool and giving its memory
 * back, counting a reference and releasing one, with the bit of objects that threads share,
 * building in the memory of an object taken apart, the uniqueness test before a write, and the
 * element reads, writes, pushes and pops of lists. Each is the fast path that `stilt-codegen-clif`'s
 * `inline.rs` and `lists.rs` compile inline in debug builds, and calls the Rust runtime on the
 * same slow paths. The layout constants come before this, from `stilt_runtime::layout`. The C
 * needs no system header. */

typedef __UINT8_TYPE__ u8;
typedef __UINT16_TYPE__ u16;
typedef __UINT32_TYPE__ u32;
typedef __UINT64_TYPE__ u64;
typedef __INT8_TYPE__ i8;
typedef __INT16_TYPE__ i16;
typedef __INT32_TYPE__ i32;
typedef __INT64_TYPE__ i64;

/* The two words that a compiled function of at most one word of result returns: its result
 * and the raised flag, or for a native, its result's words (`stilt_runtime::abi`). */
typedef struct {
    u64 a, b;
} lt_ret;

#define LT_LIKELY(x) __builtin_expect(!!(x), 1)
#define LT_UNLIKELY(x) __builtin_expect(!!(x), 0)
#define LT_INLINE static inline __attribute__((always_inline))
#define LT_COLD static __attribute__((cold, noinline, noreturn))

#define LT_OUT(i, l) LT_UNLIKELY((i) >= lt_list_len(l))

extern void stilt_rt_dup(u64);
extern void stilt_rt_drop(u64);
extern u64 stilt_rt_unique(u64);
extern void stilt_rt_panic(u64, u64, u64) __attribute__((noreturn));
extern u64 stilt_rt_list_index(u64, u64, u64);
extern u64 stilt_rt_list_get(u64, u64, u64);
extern u64 stilt_rt_list_slot(u64, u64, u64);
extern void stilt_rt_list_push(u64, u64);
extern void stilt_rt_list_append_value(u64, u64);
extern void stilt_rt_list_push_words(u64, u64);
extern void stilt_rt_list_append_words(u64, u64);
extern u64 stilt_rt_alloc_data(u64, u64);
extern u64 stilt_rt_alloc(u64);
extern void stilt_rt_free(u64, u64);
extern u64 stilt_rt_reclaim(u64, u64, u64, u64);
extern u64 stilt_rt_renew(u64, u64, u64);
extern void stilt_rt_discard(u64);
extern u64 stilt_rt_large_shape(u64, u64);
extern u64 stilt_rt_shape_parts(u64, u64);
extern u64 stilt_rt_constant_claim(u64);
extern void stilt_rt_constant_share(u64);
extern void stilt_rt_constant_done(u64);
extern double stilt_rt_fmod(double, double);
extern u64 stilt_rt_float_compare(double, double);
extern double stilt_rt_round(double);
extern u64 stilt_rt_start(u64, u64, u64, u64, u64);

/* WebAssembly's C stack lies first in memory, and each function checks at its entry that the
 * stack pointer is above the end the runtime gives the running stack, a margin above its real
 * end, so that a stack overflow is reported, and the module traps. */
#ifdef __wasm__
/* A word of WebAssembly's static data: a number, or an address, which the linker's 32-bit
 * relocations put in the word's low half, the high half zero. */
typedef union {
    u64 w;
    const void *a;
} lt_word;

extern __UINTPTR_TYPE__ stilt_rt_stack_limit;
extern void stilt_rt_stack_overflow(void) __attribute__((noreturn, cold));
#define LT_STACK_CHECK()                                                                      \
    do {                                                                                       \
        if (LT_UNLIKELY((__UINTPTR_TYPE__)__builtin_frame_address(0) < stilt_rt_stack_limit)) \
            stilt_rt_stack_overflow();                                                        \
    } while (0)
#endif

LT_INLINE double lt_f64(u64 w) { double d; __builtin_memcpy(&d, &w, 8); return d; }
LT_INLINE u64 lt_bits(double d) { u64 w; __builtin_memcpy(&w, &d, 8); return w; }
LT_INLINE float lt_f32(u64 w) { u32 b = (u32)w; float f; __builtin_memcpy(&f, &b, 4); return f; }
LT_INLINE u64 lt_bits32(float f) { u32 b; __builtin_memcpy(&b, &f, 4); return (u64)b; }
LT_INLINE u64 lt_load(u64 p) { return *(u64 *)p; }
LT_INLINE void lt_store(u64 p, u64 w) { *(u64 *)p = w; }

/* Failure paths, laid out cold: each calls a runtime function that doesn't return. */
LT_COLD void lt_panic(u64 loc, u64 kind) { stilt_rt_panic(loc, kind, 0); }
LT_COLD void lt_fail_index(u64 loc, u64 list, u64 i) {
    stilt_rt_list_index(loc, list, i);
    __builtin_trap();
}
LT_COLD void lt_fail_get(u64 loc, u64 list, u64 i) {
    stilt_rt_list_get(loc, list, i);
    __builtin_trap();
}
LT_COLD void lt_fail_slot(u64 loc, u64 slot, u64 i) {
    stilt_rt_list_slot(loc, slot, i);
    __builtin_trap();
}

/* The pool of small blocks of the thread that runs the program's entry (stilt_runtime's pool),
 * which a thread reaches inline only when its pointer is the pool's owner. */
typedef struct {
    u64 owner;
    i64 room, bytes, objects;
    u64 next, end;
    u64 heads[LT_POOL_LISTS];
} lt_pool;
extern lt_pool stilt_rt_pool;

/* The current thread's pointer, as the runtime reads it: unique among the threads that run. */
LT_INLINE u64 lt_thread(void) {
#if defined(__wasm__)
    return 1;
#elif defined(__aarch64__) && defined(__APPLE__)
    u64 t;
    __asm__("mrs %0, tpidrro_el0" : "=r"(t));
    return t & ~(u64)7;
#elif defined(__aarch64__)
    u64 t;
    __asm__("mrs %0, tpidr_el0" : "=r"(t));
    return t & ~(u64)7;
#elif defined(__x86_64__) && defined(__linux__)
    u64 t;
    __asm__("movq %%fs:0, %0" : "=r"(t));
    return t & ~(u64)7;
#else
#error "no thread pointer on this target: 0 would read as the pool's having no owner"
#endif
}

/* The runtime's pool holds pointers, which lt_pool reads as 64-bit words: on a target whose
 * pointers are narrower, as wasm32's, the fields lie elsewhere, and a block is always the
 * runtime's to give and take back. */
#if __SIZEOF_POINTER__ == 8
#define LT_POOL_INLINE 1
#else
#define LT_POOL_INLINE 0
#endif

/* A block of `size` bytes, a multiple of 8 of at most LT_POOL_LARGEST, counted as an object:
 * from the pool's list of its size or its chunk, or the runtime's. */
LT_INLINE u64 lt_alloc(u64 size) {
    if (!LT_POOL_INLINE) return stilt_rt_alloc(size);
    lt_pool *p = &stilt_rt_pool;
    if (LT_LIKELY(__atomic_load_n(&p->owner, __ATOMIC_RELAXED) == lt_thread())) {
        i64 bytes = p->bytes + (i64)size;
        if (LT_UNLIKELY(bytes > p->room)) return stilt_rt_alloc(size);
        u64 b = p->heads[size / 8 - 1];
        if (LT_LIKELY(b != 0)) {
            p->heads[size / 8 - 1] = *(u64 *)b;
        } else if (p->end - p->next >= size) {
            b = p->next;
            p->next = b + size;
        } else {
            return stilt_rt_alloc(size);
        }
        p->bytes = bytes;
        p->objects += 1;
        return b;
    }
    return stilt_rt_alloc(size);
}

/* Gives back a block that lt_alloc gave for `size` bytes. */
LT_INLINE void lt_free(u64 b, u64 size) {
    if (!LT_POOL_INLINE) {
        stilt_rt_free(b, size);
        return;
    }
    lt_pool *p = &stilt_rt_pool;
    if (LT_LIKELY(__atomic_load_n(&p->owner, __ATOMIC_RELAXED) == lt_thread())) {
        *(u64 *)b = p->heads[size / 8 - 1];
        p->heads[size / 8 - 1] = b;
        p->bytes -= (i64)size;
        p->objects -= 1;
    } else {
        stilt_rt_free(b, size);
    }
}

/* A data object of `n` fields, tag `tag` and layout word `layout`, its fields unset: from the
 * pool for a small object of the program's, from the runtime for a large one or a box, which
 * it counts. */
LT_INLINE u64 lt_alloc_data(u64 n, u64 tag, u64 layout) {
    if (n > LT_INLINE_FIELDS || tag >= LT_RUNTIME_TAGS) {
        u64 o = stilt_rt_alloc_data(n, tag);
        if (n <= LT_INLINE_FIELDS) *(u32 *)(o + LT_LAYOUT) = (u32)layout;
        return o;
    }
    u64 o = lt_alloc(LT_HEADER + 8 * n);
    *(u64 *)o = 1 | tag << (8 * LT_TAG);
    *(u64 *)(o + LT_LAYOUT) = (u32)layout;
    return o;
}

/* Whether a heap word is a pointer to an object, rather than an immediate. */
LT_INLINE int lt_is_pointer(u64 w) { return w != 0 && (w & LT_ALIGN_BITS) == 0; }

/* The header word of the object `o`, which another thread may change at the same time when the
 * object is shared, and which its count's atomic operations change: an atomic load, which costs
 * what a plain one does on every target. */
LT_INLINE u64 lt_header(u64 o) {
    return __atomic_load_n((u64 *)o, __ATOMIC_RELAXED);
}

/* One more reference: the count goes up unless the word is an immediate or its object is
 * immortal; an object that threads share is counted by the runtime, atomically. */
LT_INLINE void lt_dup(u64 w) {
    if (lt_is_pointer(w)) {
        u64 word = lt_header(w);
        if (LT_UNLIKELY(word & LT_SHARED_BIT)) {
            stilt_rt_dup(w);
            return;
        }
        u32 rc = (u32)word;
        if (rc != 0) *(u32 *)(w + LT_RC) = rc + 1;
    }
}

/* One reference less: the runtime frees the object after its last. */
LT_INLINE void lt_drop(u64 w) {
    if (lt_is_pointer(w)) {
        u64 word = lt_header(w);
        if (LT_UNLIKELY(word & LT_SHARED_BIT)) {
            stilt_rt_drop(w);
            return;
        }
        u32 rc = (u32)word;
        if (rc > 1) *(u32 *)(w + LT_RC) = rc - 1;
        else if (rc == 1) stilt_rt_drop(w);
    }
}

/* Whether nothing else references an object and threads don't share it. */
LT_INLINE int lt_is_unique(u64 o) {
    u64 word = lt_header(o);
    return !(word & LT_SHARED_BIT) && (u32)word == 1;
}

/* The object a slot holds, made unique: itself, or the runtime's copy. */
LT_INLINE u64 lt_unique(u64 slot) {
    u64 o = *(u64 *)slot;
    if (LT_LIKELY(lt_is_unique(o))) return o;
    return stilt_rt_unique(slot);
}

/* Releases the reference `o` holds, and gives the memory of its object for an object of `n`
 * fields built in its place when that was the last reference to a data object of `n` fields that
 * no thread shares and the runtime didn't make for itself; and 0 otherwise (stilt_runtime's
 * object::reuse). The caller takes a reference to each heap field that a bit of `taken` names:
 * the kept object's, or a new one. A kept object's other heap words are released. A small
 * object's layout word has the bit of its length above those of its heap words. */
LT_INLINE u64 lt_reclaim(u64 o, u64 n, u64 taken) {
    if (n > LT_INLINE_FIELDS) return stilt_rt_reclaim(o, n, taken, 0);
    if (!lt_is_pointer(o)) return 0;
    u64 word = lt_header(o);
    u64 layout = *(u32 *)(o + LT_LAYOUT);
    int kept = (word & 0xffffffffffffULL) == 1 && (u16)(word >> (8 * LT_TAG)) < LT_RUNTIME_TAGS &&
               layout >> n == 1;
    if (LT_UNLIKELY(!kept)) return stilt_rt_reclaim(o, n, taken, 0);
    for (u64 mask = layout & ~taken & ((1ULL << n) - 1); mask != 0; mask &= mask - 1)
        lt_drop(*(u64 *)(o + LT_HEADER + 8 * (u64)__builtin_ctzll(mask)));
    return o;
}

/* lt_reclaim of an object known to be a variant of the program's of `n` fields, at most
 * LT_INLINE_FIELDS, whose heap words are the bits of `heap`: only its count and whether threads
 * share it need testing. */
LT_INLINE u64 lt_reclaim_known(u64 o, u64 n, u64 taken, u64 heap) {
    if (LT_UNLIKELY((*(u64 *)o & 0xffffffffffffULL) != 1)) return stilt_rt_reclaim(o, n, taken, 0);
    for (u64 mask = heap & ~taken; mask != 0; mask &= mask - 1)
        lt_drop(*(u64 *)(o + LT_HEADER + 8 * (u64)__builtin_ctzll(mask)));
    return o;
}

/* A data object of `n` fields, tag `tag` and layout word `layout`, in memory that lt_reclaim
 * kept, whose count is still 1, or new when `m` is 0. */
LT_INLINE u64 lt_renew(u64 m, u64 n, u64 tag, u64 layout) {
    if (m == 0) return lt_alloc_data(n, tag, layout);
    if (n > LT_INLINE_FIELDS || tag >= LT_RUNTIME_TAGS) {
        m = stilt_rt_renew(m, n, tag);
        if (n <= LT_INLINE_FIELDS) *(u32 *)(m + LT_LAYOUT) = (u32)layout;
        return m;
    }
    *(u16 *)(m + LT_TAG) = (u16)tag;
    *(u32 *)(m + LT_LAYOUT) = (u32)layout;
    return m;
}

/* Gives back memory that lt_reclaim kept and nothing was built in. */
LT_INLINE void lt_discard(u64 m) {
    if (m == 0) return;
    u32 layout = *(u32 *)(m + LT_LAYOUT);
    if (layout & LT_LAYOUT_LARGE) stilt_rt_discard(m);
    else lt_free(m, LT_HEADER + 8 * (u64)(31 - __builtin_clz(layout)));
}

/* A variant's index: an immediate's own, or the tag in its object's header. */
LT_INLINE u64 lt_tag(u64 v) { return (v & 1) ? v >> 1 : (u64) * (u16 *)(v + LT_TAG); }

LT_INLINE u64 lt_list_len(u64 l) { return *(u64 *)(l + LT_LIST_LEN); }
LT_INLINE u64 lt_list_data(u64 l) { return *(u64 *)(l + LT_LIST_DATA); }
LT_INLINE int lt_has_room(u64 l) { return lt_list_len(l) < *(u64 *)(l + LT_LIST_CAP); }

/* The address of word `word` of element `i` of a list of elements of `size` bytes. */
LT_INLINE u64 lt_element(u64 l, u64 i, u64 size, u64 word) {
    return *(u64 *)(l + LT_LIST_DATA) + i * size + 8 * word;
}

/* The word at `a` of an element of `size` bytes: a narrow scalar widened as its kind is. */
LT_INLINE u64 lt_read(u64 a, u64 size, int sign) {
    switch (size) {
    case 1: return sign ? (u64)(i64) * (i8 *)a : (u64) * (u8 *)a;
    case 2: return sign ? (u64)(i64) * (i16 *)a : (u64) * (u16 *)a;
    case 4: return sign ? (u64)(i64) * (i32 *)a : (u64) * (u32 *)a;
    default: return *(u64 *)a;
    }
}

/* Stores the scalar `x` at `a` in the width of an element of `size` bytes. */
LT_INLINE void lt_write(u64 a, u64 x, u64 size) {
    switch (size) {
    case 1: *(u8 *)a = (u8)x; break;
    case 2: *(u16 *)a = (u16)x; break;
    case 4: *(u32 *)a = (u32)x; break;
    default: *(u64 *)a = x; break;
    }
}

LT_INLINE u64 lt_list_at(u64 l, u64 i, u64 size, int sign, u64 word) {
    return lt_read(lt_element(l, i, size, word), size, sign);
}

/* Word `word` of `xs[i]`, borrowed, or the runtime's panic when `i` is out of bounds. */
LT_INLINE u64 lt_list_index(u64 loc, u64 l, u64 i, u64 size, int sign, u64 word) {
    if (LT_OUT(i, l)) lt_fail_index(loc, l, i);
    return lt_list_at(l, i, size, sign, word);
}

/* The address of word `word` of `xs[i]`, or the runtime's panic. */
LT_INLINE u64 lt_checked_element(u64 loc, u64 l, u64 i, u64 size, u64 word) {
    if (LT_OUT(i, l)) lt_fail_index(loc, l, i);
    return lt_element(l, i, size, word);
}

/* A pointer to `xs[i]` of the list a slot holds, made unique, or the runtime's panic. */
LT_INLINE u64 lt_list_slot(u64 loc, u64 slot, u64 i, u64 size) {
    u64 l = *(u64 *)slot;
    if (LT_OUT(i, l)) lt_fail_slot(loc, slot, i);
    if (LT_LIKELY(lt_is_unique(l))) return lt_element(l, i, size, 0);
    return stilt_rt_list_slot(loc, slot, i);
}

/* A pointer to element `i`, in bounds, of the list a slot holds, made unique. */
LT_INLINE u64 lt_list_slot_at(u64 slot, u64 i, u64 size) {
    u64 l = *(u64 *)slot;
    if (LT_LIKELY(lt_is_unique(l))) return lt_element(l, i, size, 0);
    return lt_element(stilt_rt_unique(slot), i, size, 0);
}

/* A pointer to `xs[i]` of the list a slot holds, which nothing else references. */
LT_INLINE u64 lt_list_element(u64 loc, u64 slot, u64 i, u64 size) {
    u64 l = *(u64 *)slot;
    if (LT_OUT(i, l)) lt_fail_slot(loc, slot, i);
    return lt_element(l, i, size, 0);
}

LT_INLINE u64 lt_list_element_at(u64 slot, u64 i, u64 size) {
    return lt_element(*(u64 *)slot, i, size, 0);
}

/* Whether a witness says its values take one word in a list. */
LT_INLINE int lt_one_word(u64 shape) {
    return ((shape >> LT_SHAPE_SIZE_SHIFT) & LT_SHAPE_SIZE_BITS) == 8;
}

/* `xs[i]` of a list of values of a type parameter, in its one word, with references of its
 * own: an element of one word inline, any other from the runtime. */
LT_INLINE u64 lt_list_get(u64 loc, u64 l, u64 i, u64 shape) {
    if (LT_OUT(i, l)) lt_fail_get(loc, l, i);
    if (LT_LIKELY(lt_one_word(shape))) {
        u64 w = lt_list_at(l, i, 8, 0, 0);
        if (shape & 1) lt_dup(w);
        return w;
    }
    return stilt_rt_list_get(loc, l, i);
}

/* Appends a value of a type parameter, in its one word, to a list that nothing else
 * references, or to the list a slot holds when `slot` is set. */
LT_INLINE void lt_push_value(u64 l, u64 witness, u64 x) {
    if (LT_LIKELY(lt_has_room(l) && lt_one_word(witness))) {
        u64 n = lt_list_len(l);
        *(u64 *)lt_element(l, n, 8, 0) = x;
        *(u64 *)(l + LT_LIST_LEN) = n + 1;
    } else {
        stilt_rt_list_push(l, x);
    }
}

LT_INLINE void lt_append_value(u64 slot, u64 witness, u64 x) {
    u64 l = *(u64 *)slot;
    if (LT_LIKELY(lt_is_unique(l) && lt_has_room(l) && lt_one_word(witness))) {
        u64 n = lt_list_len(l);
        *(u64 *)lt_element(l, n, 8, 0) = x;
        *(u64 *)(l + LT_LIST_LEN) = n + 1;
    } else {
        stilt_rt_list_append_value(slot, x);
    }
}

/* `xs.pop()` on the list a slot holds, of elements of one word or narrower: `None`, or `Some`
 * of its last element, which moves out of the list once it is unique. */
LT_INLINE lt_ret lt_pop(u64 slot, u64 size, int sign) {
    u64 l = *(u64 *)slot;
    u64 n = lt_list_len(l);
    lt_ret r = {1, 0};
    if (n == 0) return r;
    if (LT_UNLIKELY(!lt_is_unique(l))) l = stilt_rt_unique(slot);
    *(u64 *)(l + LT_LIST_LEN) = n - 1;
    r.a = 3;
    r.b = lt_list_at(l, n - 1, size, sign, 0);
    return r;
}

/* The fields of data object `o`: field `i`'s address. */
LT_INLINE u64 lt_field(u64 o, u64 i) { return o + LT_HEADER + 8 * i; }

/* Saturating conversions of a float's truncation, which a range check guards (numbers.conversions): C's own conversion is undefined outside the range. */
LT_INLINE u64 lt_to_i64(double x) {
    if (x != x) return 0;
    if (x >= 9223372036854775808.0) return (u64)0x7fffffffffffffffULL;
    if (x < -9223372036854775808.0) return (u64)0x8000000000000000ULL;
    return (u64)(i64)x;
}

LT_INLINE u64 lt_to_u64(double x) {
    if (!(x > 0.0)) return 0;
    if (x >= 18446744073709551616.0) return ~(u64)0;
    return (u64)x;
}
