/* The reference interpreter's calls of C (c.linking, c.calls and c.both-implementations): its
   libraries loaded from the system's paths, its functions found by name and
   called through libffi with C's calling convention for the platform, and the
   memory that lent lists and strings copy into. An address is an int64, as
   Stilt holds a `c.Ptr`; so is every value that crosses, as its bits. */

#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#ifdef __APPLE__
#include <ffi/ffi.h>
#define LIBRARY_SUFFIX ".dylib"
#else
#include <ffi.h>
#define LIBRARY_SUFFIX ".so"
#endif

#include <caml/alloc.h>
#include <caml/fail.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>

/* The kinds of values that cross, as Foreign numbers them. */
enum kind {
  K_VOID, K_I8, K_U8, K_I16, K_U16, K_I32, K_U32, K_I64, K_U64,
  K_F32, K_F64, K_BOOL, K_POINTER
};

#define MAX_ARGS 32

static ffi_type *ffi_type_of(int kind) {
  switch (kind) {
  case K_I8: return &ffi_type_sint8;
  case K_U8: return &ffi_type_uint8;
  case K_I16: return &ffi_type_sint16;
  case K_U16: return &ffi_type_uint16;
  case K_I32: return &ffi_type_sint32;
  case K_U32: return &ffi_type_uint32;
  case K_I64: return &ffi_type_sint64;
  case K_U64: return &ffi_type_uint64;
  case K_F32: return &ffi_type_float;
  case K_F64: return &ffi_type_double;
  case K_BOOL: return &ffi_type_uint8;
  case K_POINTER: return &ffi_type_pointer;
  default: return &ffi_type_void;
  }
}

/* A value's room, large enough for any kind, which libffi reads and writes. */
union slot {
  int8_t i8; uint8_t u8; int16_t i16; uint16_t u16; int32_t i32;
  uint32_t u32; int64_t i64; uint64_t u64; float f32; double f64;
  void *pointer; ffi_arg widened; ffi_sarg swidened;
};

static void store(union slot *s, int kind, int64_t bits) {
  switch (kind) {
  case K_I8: s->i8 = (int8_t)bits; break;
  case K_U8: case K_BOOL: s->u8 = (uint8_t)bits; break;
  case K_I16: s->i16 = (int16_t)bits; break;
  case K_U16: s->u16 = (uint16_t)bits; break;
  case K_I32: s->i32 = (int32_t)bits; break;
  case K_U32: s->u32 = (uint32_t)bits; break;
  case K_F32: {
    uint32_t b = (uint32_t)bits;
    memcpy(&s->f32, &b, sizeof b);
    break;
  }
  case K_F64: memcpy(&s->f64, &bits, sizeof bits); break;
  case K_POINTER: s->pointer = (void *)(intptr_t)bits; break;
  default: s->i64 = bits; break;
  }
}

/* A result, which libffi widens to a whole register for the narrow integer
   kinds. */
static int64_t load(const union slot *s, int kind) {
  switch (kind) {
  case K_I8: return (int8_t)s->swidened;
  case K_U8: return (uint8_t)s->widened;
  case K_BOOL: return (uint8_t)s->widened != 0;
  case K_I16: return (int16_t)s->swidened;
  case K_U16: return (uint16_t)s->widened;
  case K_I32: return (int32_t)s->swidened;
  case K_U32: return (uint32_t)s->widened;
  case K_F32: {
    uint32_t b;
    memcpy(&b, &s->f32, sizeof b);
    return b;
  }
  case K_F64: {
    int64_t b;
    memcpy(&b, &s->f64, sizeof b);
    return b;
  }
  case K_POINTER: return (int64_t)(intptr_t)s->pointer;
  case K_VOID: return 0;
  default: return s->i64;
  }
}

/* Loads the library NAME, as the dynamic loader finds libNAME on the system's
   paths, its symbols visible to every later lookup. */
value stilt_c_load(value name) {
  CAMLparam1(name);
  size_t n = caml_string_length(name);
  char *file = malloc(n + 16);
  if (file == NULL) CAMLreturn(Val_false);
  memcpy(file, "lib", 3);
  memcpy(file + 3, String_val(name), n);
  strcpy(file + 3 + n, LIBRARY_SUFFIX);
  void *handle = dlopen(file, RTLD_NOW | RTLD_GLOBAL);
  free(file);
  CAMLreturn(Val_bool(handle != NULL));
}

/* The address of the C function NAME among everything loaded, or 0. */
value stilt_c_symbol(value name) {
  CAMLparam1(name);
  void *found = dlsym(RTLD_DEFAULT, String_val(name));
  CAMLreturn(caml_copy_int64((int64_t)(intptr_t)found));
}

/* Calls the function at ADDRESS with the arguments BITS, of kinds KINDS, and
   gives its result, of kind RESULT, as bits. */
value stilt_c_call(value address, value kinds, value bits, value result) {
  CAMLparam4(address, kinds, bits, result);
  size_t n = Wosize_val(kinds);
  ffi_type *types[MAX_ARGS];
  union slot args[MAX_ARGS];
  void *pointers[MAX_ARGS];
  ffi_cif cif;
  union slot out;
  if (n > MAX_ARGS) caml_failwith("a foreign call takes at most 32 arguments");
  for (size_t i = 0; i < n; i++) {
    int kind = Int_val(Field(kinds, i));
    types[i] = ffi_type_of(kind);
    store(&args[i], kind, Int64_val(Field(bits, i)));
    pointers[i] = &args[i];
  }
  int kind = Int_val(result);
  if (ffi_prep_cif(&cif, FFI_DEFAULT_ABI, (unsigned)n, ffi_type_of(kind), types)
      != FFI_OK)
    caml_failwith("libffi can't make this call");
  memset(&out, 0, sizeof out);
  void (*fn)(void) = (void (*)(void))(intptr_t)Int64_val(address);
  ffi_call(&cif, fn, &out, pointers);
  CAMLreturn(caml_copy_int64(load(&out, kind)));
}

/* SIZE bytes of zeros, never NULL, which the program frees. */
value stilt_c_alloc(value size) {
  CAMLparam1(size);
  size_t n = (size_t)Long_val(size);
  void *block = calloc(n == 0 ? 1 : n, 1);
  if (block == NULL) caml_raise_out_of_memory();
  CAMLreturn(caml_copy_int64((int64_t)(intptr_t)block));
}

value stilt_c_free(value address) {
  CAMLparam1(address);
  free((void *)(intptr_t)Int64_val(address));
  CAMLreturn(Val_unit);
}

/* The SIZE bytes at ADDRESS, as C holds an integer of that width, its sign
   extended when SIGNED. */
value stilt_c_peek(value address, value size, value is_signed) {
  CAMLparam3(address, size, is_signed);
  const void *at = (const void *)(intptr_t)Int64_val(address);
  int64_t v;
  switch (Int_val(size)) {
  case 1: v = Bool_val(is_signed) ? *(const int8_t *)at : *(const uint8_t *)at; break;
  case 2: v = Bool_val(is_signed) ? *(const int16_t *)at : *(const uint16_t *)at; break;
  case 4: v = Bool_val(is_signed) ? *(const int32_t *)at : *(const uint32_t *)at; break;
  default: v = *(const int64_t *)at; break;
  }
  CAMLreturn(caml_copy_int64(v));
}

/* Writes the low SIZE bytes of BITS at ADDRESS, as C holds an integer of that
   width. */
value stilt_c_poke(value address, value size, value bits) {
  CAMLparam3(address, size, bits);
  void *at = (void *)(intptr_t)Int64_val(address);
  int64_t v = Int64_val(bits);
  switch (Int_val(size)) {
  case 1: *(uint8_t *)at = (uint8_t)v; break;
  case 2: *(uint16_t *)at = (uint16_t)v; break;
  case 4: *(uint32_t *)at = (uint32_t)v; break;
  default: *(int64_t *)at = v; break;
  }
  CAMLreturn(Val_unit);
}

/* The bytes of the string at ADDRESS, up to its NUL. */
value stilt_c_string(value address) {
  CAMLparam1(address);
  const char *s = (const char *)(intptr_t)Int64_val(address);
  CAMLreturn(caml_copy_string(s));
}

/* Copies BYTES to ADDRESS. */
value stilt_c_write_bytes(value address, value bytes) {
  CAMLparam2(address, bytes);
  memcpy((void *)(intptr_t)Int64_val(address), String_val(bytes),
         caml_string_length(bytes));
  CAMLreturn(Val_unit);
}
