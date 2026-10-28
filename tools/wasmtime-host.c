/* For clock_gettime and CLOCK_MONOTONIC under -std=c11. */
#define _POSIX_C_SOURCE 199309L

#include <inttypes.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include <wasm.h>
#include <wasmtime.h>
#include <wasi.h>

typedef struct {
  wasm_engine_t *engine;
  wasmtime_module_t *module;
  wasmtime_store_t *store;
  wasmtime_context_t *context;
  wasmtime_instance_t instance;
  wasmtime_memory_t memory;
  wasmtime_func_t alloc;
  bool has_memory;
  bool has_alloc;
} Runtime;

typedef struct {
  bool wasi;
  bool command;
  bool control_records;
  const char *stdin_file;
  const char *stdout_file;
  const char *stderr_file;
  const char *control_file;
} HostOptions;

static HostOptions options;
static Runtime *active_runtime;
static FILE *control_output;
static bool owns_control_output;
static bool outcome_recorded;

typedef struct {
  uint64_t *items;
  size_t len;
} U64List;

static void dispose_runtime(Runtime *runtime) {
  if (runtime == NULL) {
    return;
  }
  if (runtime->store != NULL) {
    wasmtime_store_delete(runtime->store);
  }
  if (runtime->module != NULL) {
    wasmtime_module_delete(runtime->module);
  }
  if (runtime->engine != NULL) {
    wasm_engine_delete(runtime->engine);
  }
  memset(runtime, 0, sizeof(*runtime));
}

/* Exits with `status`.  In WASI mode with control records, a failure that `check_outcome` has
   not recorded as `wasi-exit` or `trap` ends the control output with `error`. */
static _Noreturn void finish_host(int status) {
  dispose_runtime(active_runtime);
  if (status != 0 && !outcome_recorded && options.wasi && options.control_records &&
      control_output != NULL) {
    fprintf(control_output, "error\n");
  }
  if (control_output != NULL) {
    bool failed = ferror(control_output) != 0;
    int result = owns_control_output ? fclose(control_output) : fflush(control_output);
    control_output = NULL;
    if (result != 0) {
      perror("cannot finish control output");
      status = 1;
    } else if (failed) {
      fprintf(stderr, "cannot write control output\n");
      status = 1;
    }
  }
  exit(status);
}

static _Noreturn void die(const char *message) {
  fprintf(stderr, "%s\n", message);
  finish_host(1);
}

static void print_error(wasmtime_error_t *error) {
  wasm_name_t message;
  wasmtime_error_message(error, &message);
  fprintf(stderr, "%.*s\n", (int)message.size, message.data);
  wasm_byte_vec_delete(&message);
  wasmtime_error_delete(error);
}

static void print_trap(wasm_trap_t *trap) {
  wasm_message_t message;
  wasm_trap_message(trap, &message);
  fprintf(stderr, "%.*s\n", (int)message.size, message.data);
  wasm_byte_vec_delete(&message);
  wasm_trap_delete(trap);
}

static void check_outcome(wasmtime_error_t *error, wasm_trap_t *trap, int trap_status) {
  if (error != NULL) {
    int status = 0;
    if (options.wasi && wasmtime_error_exit_status(error, &status)) {
      uint32_t raw_status = (uint32_t)status;
      wasmtime_error_delete(error);
      if (options.control_records) {
        fprintf(control_output, "wasi-exit %" PRIu32 "\n", raw_status);
      }
      outcome_recorded = true;
      finish_host((int)(raw_status & UINT32_C(255)));
    }
    print_error(error);
    if (trap != NULL) {
      print_trap(trap);
    }
    finish_host(1);
  }
  if (trap != NULL) {
    print_trap(trap);
    if (trap_status == 2 && options.wasi && options.control_records) {
      fprintf(control_output, "trap\n");
      outcome_recorded = true;
    }
    finish_host(trap_status);
  }
}

static void call_func(Runtime *runtime, wasmtime_func_t *func, const wasmtime_val_t *args,
                      size_t nargs, wasmtime_val_t *results, size_t nresults, int trap_status) {
  wasm_trap_t *trap = NULL;
  wasmtime_error_t *error =
      wasmtime_func_call(runtime->context, func, args, nargs, results, nresults, &trap);
  check_outcome(error, trap, trap_status);
}

static uint8_t *read_file(const char *path, size_t *len_out) {
  FILE *file = fopen(path, "rb");
  if (file == NULL) {
    perror(path);
    finish_host(1);
  }
  if (fseek(file, 0, SEEK_END) != 0) {
    perror("fseek");
    finish_host(1);
  }
  long size = ftell(file);
  if (size < 0) {
    perror("ftell");
    finish_host(1);
  }
  if (fseek(file, 0, SEEK_SET) != 0) {
    perror("fseek");
    finish_host(1);
  }
  uint8_t *bytes = malloc((size_t)size);
  if (bytes == NULL && size != 0) {
    die("out of memory");
  }
  if (size != 0 && fread(bytes, 1, (size_t)size, file) != (size_t)size) {
    if (ferror(file)) {
      perror("fread");
    } else {
      fprintf(stderr, "unexpected end of file: %s\n", path);
    }
    finish_host(1);
  }
  if (fclose(file) != 0) {
    perror("fclose");
    finish_host(1);
  }
  *len_out = (size_t)size;
  return bytes;
}

static uint8_t hex_nibble(char c) {
  if ('0' <= c && c <= '9') {
    return (uint8_t)(c - '0');
  }
  if ('a' <= c && c <= 'f') {
    return (uint8_t)(10 + c - 'a');
  }
  if ('A' <= c && c <= 'F') {
    return (uint8_t)(10 + c - 'A');
  }
  die("invalid hex byte");
  return 0;
}

static uint8_t *parse_hex(const char *text, size_t *len_out) {
  size_t text_len = strlen(text);
  if (text_len % 2 != 0) {
    die("hex input must have an even number of digits");
  }
  size_t len = text_len / 2;
  uint8_t *bytes = malloc(len == 0 ? 1 : len);
  if (bytes == NULL) {
    die("out of memory");
  }
  for (size_t i = 0; i < len; i++) {
    bytes[i] = (uint8_t)((hex_nibble(text[i * 2]) << 4) | hex_nibble(text[i * 2 + 1]));
  }
  *len_out = len;
  return bytes;
}

static uint64_t parse_u64(const char *text) {
  char *end = NULL;
  uint64_t value = strtoull(text, &end, 10);
  if (end == NULL || *end != 0) {
    die("invalid i64 argument");
  }
  return value;
}

static U64List parse_u64_list(const char *text) {
  U64List list;
  list.items = NULL;
  list.len = 0;
  if (*text == 0) {
    return list;
  }
  size_t count = 1;
  for (const char *cursor = text; *cursor != 0; cursor++) {
    if (*cursor == ',') {
      count++;
    }
  }
  list.items = calloc(count, sizeof(uint64_t));
  if (list.items == NULL) {
    die("out of memory");
  }
  const char *start = text;
  for (;;) {
    const char *comma = strchr(start, ',');
    size_t len = comma == NULL ? strlen(start) : (size_t)(comma - start);
    char *part = malloc(len + 1);
    if (part == NULL) {
      die("out of memory");
    }
    memcpy(part, start, len);
    part[len] = 0;
    list.items[list.len++] = parse_u64(part);
    free(part);
    if (comma == NULL) {
      break;
    }
    start = comma + 1;
  }
  return list;
}

static void free_u64_list(U64List list) {
  free(list.items);
}

static wasi_config_t *configure_wasi(void) {
  wasi_config_t *config = wasi_config_new();
  if (config == NULL) {
    die("failed to create WASI configuration");
  }
  const char *failed_path = NULL;
  if (options.stdin_file == NULL) {
    wasi_config_inherit_stdin(config);
  } else if (!wasi_config_set_stdin_file(config, options.stdin_file)) {
    failed_path = options.stdin_file;
  }
  if (failed_path == NULL) {
    if (options.stdout_file == NULL) {
      wasi_config_inherit_stdout(config);
    } else if (!wasi_config_set_stdout_file(config, options.stdout_file)) {
      failed_path = options.stdout_file;
    }
  }
  if (failed_path == NULL) {
    if (options.stderr_file == NULL) {
      wasi_config_inherit_stderr(config);
    } else if (!wasi_config_set_stderr_file(config, options.stderr_file)) {
      failed_path = options.stderr_file;
    }
  }
  if (failed_path != NULL) {
    fprintf(stderr, "cannot open WASI stream file: %s\n", failed_path);
    wasi_config_delete(config);
    finish_host(1);
  }
  return config;
}

static void init_runtime(Runtime *runtime, const char *wasm_path) {
  memset(runtime, 0, sizeof(*runtime));
  size_t wasm_len = 0;
  uint8_t *wasm_bytes = read_file(wasm_path, &wasm_len);

  wasm_config_t *config = wasm_config_new();
  if (config == NULL) {
    die("failed to create Wasmtime configuration");
  }
  wasmtime_config_strategy_set(config, WASMTIME_STRATEGY_CRANELIFT);
  wasmtime_config_cranelift_nan_canonicalization_set(config, true);
  runtime->engine = wasm_engine_new_with_config(config);
  if (runtime->engine == NULL) {
    die("failed to create Wasmtime engine");
  }

  wasmtime_error_t *error =
      wasmtime_module_new(runtime->engine, wasm_bytes, wasm_len, &runtime->module);
  free(wasm_bytes);
  check_outcome(error, NULL, 1);

  runtime->store = wasmtime_store_new(runtime->engine, NULL, NULL);
  if (runtime->store == NULL) {
    die("failed to create Wasmtime store");
  }
  runtime->context = wasmtime_store_context(runtime->store);

  wasm_trap_t *trap = NULL;
  if (options.wasi) {
    wasi_config_t *wasi = configure_wasi();
    error = wasmtime_context_set_wasi(runtime->context, wasi);
    check_outcome(error, NULL, 1);
    wasmtime_linker_t *linker = wasmtime_linker_new(runtime->engine);
    if (linker == NULL) {
      die("failed to create Wasmtime linker");
    }
    error = wasmtime_linker_define_wasi(linker);
    if (error == NULL) {
      error = wasmtime_linker_instantiate(linker, runtime->context, runtime->module,
                                         &runtime->instance, &trap);
    }
    wasmtime_linker_delete(linker);
  } else {
    error = wasmtime_instance_new(runtime->context, runtime->module, NULL, 0,
                                  &runtime->instance, &trap);
  }
  wasmtime_module_delete(runtime->module);
  runtime->module = NULL;
  check_outcome(error, trap, 1);

  wasmtime_extern_t item;
  if (wasmtime_instance_export_get(runtime->context, &runtime->instance, "memory", 6, &item)) {
    if (item.kind != WASMTIME_EXTERN_MEMORY) {
      die("export memory is not a memory");
    }
    runtime->memory = item.of.memory;
    runtime->has_memory = true;
  }
  if (wasmtime_instance_export_get(runtime->context, &runtime->instance, "alloc", 5, &item)) {
    if (item.kind != WASMTIME_EXTERN_FUNC) {
      die("export alloc is not a function");
    }
    runtime->alloc = item.of.func;
    runtime->has_alloc = true;
  }
  if (!options.command &&
      wasmtime_instance_export_get(runtime->context, &runtime->instance, "reset", 5, &item)) {
    if (item.kind != WASMTIME_EXTERN_FUNC) {
      die("export reset is not a function");
    }
    call_func(runtime, &item.of.func, NULL, 0, NULL, 0, 1);
  }
}

static wasmtime_func_t get_func(Runtime *runtime, const char *name) {
  wasmtime_extern_t item;
  if (!wasmtime_instance_export_get(runtime->context, &runtime->instance, name, strlen(name), &item)) {
    fprintf(stderr, "missing export: %s\n", name);
    finish_host(1);
  }
  if (item.kind != WASMTIME_EXTERN_FUNC) {
    fprintf(stderr, "export is not a function: %s\n", name);
    finish_host(1);
  }
  return item.of.func;
}

static uint64_t call_i64_func(Runtime *runtime, wasmtime_func_t *func, uint64_t arg) {
  wasmtime_val_t args[1];
  wasmtime_val_t results[1];
  memset(args, 0, sizeof(args));
  memset(results, 0, sizeof(results));
  args[0].kind = WASMTIME_I64;
  args[0].of.i64 = (int64_t)arg;
  results[0].kind = WASMTIME_I64;
  call_func(runtime, func, args, 1, results, 1, 1);
  if (results[0].kind != WASMTIME_I64) {
    die("expected i64 result");
  }
  return (uint64_t)results[0].of.i64;
}

static void call_void_i64_func(Runtime *runtime, wasmtime_func_t *func, uint64_t arg) {
  wasmtime_val_t args[1];
  wasmtime_val_t results[1];
  memset(args, 0, sizeof(args));
  memset(results, 0, sizeof(results));
  args[0].kind = WASMTIME_I64;
  args[0].of.i64 = (int64_t)arg;
  call_func(runtime, func, args, 1, results, 0, 1);
}

static void call_void_func(Runtime *runtime, wasmtime_func_t *func) {
  wasmtime_val_t args[1];
  wasmtime_val_t results[1];
  memset(args, 0, sizeof(args));
  memset(results, 0, sizeof(results));
  call_func(runtime, func, args, 0, results, 0, 1);
}

static uint64_t call_alloc(Runtime *runtime, uint64_t len) {
  if (!runtime->has_alloc) {
    die("missing alloc export");
  }
  return call_i64_func(runtime, &runtime->alloc, len);
}

static wasmtime_func_t required_runtime_func(Runtime *runtime, const char *name) {
  return get_func(runtime, name);
}

static void reset_runtime(Runtime *runtime) {
  wasmtime_func_t reset = required_runtime_func(runtime, "reset");
  call_void_func(runtime, &reset);
}

static void write_u64_at(Runtime *runtime, uint64_t ptr, uint64_t value) {
  if (!runtime->has_memory) {
    die("missing memory export");
  }
  size_t memory_len = wasmtime_memory_data_size(runtime->context, &runtime->memory);
  if (ptr > memory_len || 8 > memory_len - (size_t)ptr) {
    die("u64 write is outside memory");
  }
  uint8_t *memory = wasmtime_memory_data(runtime->context, &runtime->memory);
  for (size_t i = 0; i < 8; i++) {
    memory[ptr + i] = (uint8_t)(value >> (i * 8));
  }
}

static uint64_t read_u64_at(Runtime *runtime, uint64_t ptr) {
  if (!runtime->has_memory) {
    die("missing memory export");
  }
  size_t memory_len = wasmtime_memory_data_size(runtime->context, &runtime->memory);
  if (ptr > memory_len || 8 > memory_len - (size_t)ptr) {
    die("u64 read is outside memory");
  }
  uint8_t *memory = wasmtime_memory_data(runtime->context, &runtime->memory);
  uint64_t value = 0;
  for (size_t i = 0; i < 8; i++) {
    value |= (uint64_t)memory[ptr + i] << (i * 8);
  }
  return value;
}

static uint64_t alloc_bytes(Runtime *runtime, const uint8_t *bytes, size_t len) {
  if (!runtime->has_memory || !runtime->has_alloc) {
    die("ByteArray argument requires exported memory and alloc");
  }
  uint64_t ptr = call_i64_func(runtime, &runtime->alloc, (uint64_t)len);
  size_t memory_len = wasmtime_memory_data_size(runtime->context, &runtime->memory);
  if (ptr > memory_len || len > memory_len - (size_t)ptr) {
    die("allocation is outside memory");
  }
  uint8_t *memory = wasmtime_memory_data(runtime->context, &runtime->memory);
  memcpy(memory + ptr, bytes, len);
  return ptr;
}

static uint64_t alloc_u64_array(Runtime *runtime, U64List values) {
  uint64_t ptr = call_alloc(runtime, 8 + values.len * 8);
  write_u64_at(runtime, ptr, values.len);
  for (size_t i = 0; i < values.len; i++) {
    write_u64_at(runtime, ptr + 8 + i * 8, values.items[i]);
  }
  return ptr;
}

/* Allocates the list `values` as a chain of records of two slots, the element and the pointer
   to the rest, each with kind 1, width 2, and mask 2, and returns the pointer to the first
   record, or 0 for the empty list. */
static uint64_t alloc_u64_chain(Runtime *runtime, U64List values) {
  uint64_t ptr = 0;
  for (size_t i = values.len; i > 0; i--) {
    uint64_t cell = call_alloc(runtime, 16);
    write_u64_at(runtime, cell - 24, 1);
    write_u64_at(runtime, cell - 16, 2);
    write_u64_at(runtime, cell - 8, 2);
    write_u64_at(runtime, cell, values.items[i - 1]);
    write_u64_at(runtime, cell + 8, ptr);
    ptr = cell;
  }
  return ptr;
}

/* Copies the comma-separated token at `*text` into `token`, of `size` bytes, and advances
   `*text` past the token and its comma. */
static void read_token(const char **text, char *token, size_t size) {
  const char *start = *text;
  const char *comma = strchr(start, ',');
  size_t len = comma == NULL ? strlen(start) : (size_t)(comma - start);
  *text = comma == NULL ? start + len : comma + 1;
  if (len == 0 || len >= size) {
    die("bad tree description");
  }
  memcpy(token, start, len);
  token[len] = 0;
}

/* Allocates the tree whose preorder description starts at `*text`: `.` for a leaf, and for a
   node its key followed by its left and right subtrees, separated by commas.  A node is a
   record of three slots, the pointer to the left subtree, the key, and the pointer to the
   right subtree, with kind 1, width 3, and mask 5.  Returns the pointer, 0 for a leaf. */
static uint64_t alloc_u64_tree(Runtime *runtime, const char **text) {
  char token[32];
  read_token(text, token, sizeof token);
  if (strcmp(token, ".") == 0) {
    return 0;
  }
  uint64_t key = parse_u64(token);
  uint64_t left = alloc_u64_tree(runtime, text);
  uint64_t right = alloc_u64_tree(runtime, text);
  uint64_t cell = call_alloc(runtime, 24);
  write_u64_at(runtime, cell - 24, 1);
  write_u64_at(runtime, cell - 16, 3);
  write_u64_at(runtime, cell - 8, 5);
  write_u64_at(runtime, cell, left);
  write_u64_at(runtime, cell + 8, key);
  write_u64_at(runtime, cell + 16, right);
  return cell;
}

/* Whether `width` and `mask` describe a record: between 1 and 64 slots, and no mask bit at or
   above the width. */
static bool record_header_valid(uint64_t width, uint64_t mask) {
  return width >= 1 && width <= 64 && (width == 64 || mask >> width == 0);
}

/* Allocates the tree of records whose preorder description starts at `*text`: `.` for null,
   and for a record its width, its mask, and its slots, separated by commas, where a slot whose
   mask bit is set is a tree and any other slot is a word.  Each record has kind 1 and the
   width and mask of its description.  Returns the pointer, 0 for null. */
static uint64_t alloc_records(Runtime *runtime, const char **text) {
  char token[32];
  read_token(text, token, sizeof token);
  if (strcmp(token, ".") == 0) {
    return 0;
  }
  uint64_t width = parse_u64(token);
  read_token(text, token, sizeof token);
  uint64_t mask = parse_u64(token);
  if (!record_header_valid(width, mask)) {
    die("bad record header in tree description");
  }
  uint64_t slots[64];
  for (uint64_t i = 0; i < width; i++) {
    if ((mask >> i) & 1) {
      slots[i] = alloc_records(runtime, text);
    } else {
      read_token(text, token, sizeof token);
      slots[i] = parse_u64(token);
    }
  }
  uint64_t cell = call_alloc(runtime, 8 * width);
  write_u64_at(runtime, cell - 24, 1);
  write_u64_at(runtime, cell - 16, width);
  write_u64_at(runtime, cell - 8, mask);
  for (uint64_t i = 0; i < width; i++) {
    write_u64_at(runtime, cell + 8 * i, slots[i]);
  }
  return cell;
}

#define OBJECT_MAGIC UINT64_C(5501223100278326855)

/* Writes to `out` unless `out` is NULL.  The result printers walk a result once with NULL to
   check it and once with the control output to print it, so a malformed result prints nothing. */
static void emit(FILE *out, const char *format, ...) {
  if (out == NULL) {
    return;
  }
  va_list args;
  va_start(args, format);
  vfprintf(out, format, args);
  va_end(args);
}

/* Writes the chain of records at `ptr` as `[x, y, ...]`, after checking that each record's
   header holds the magic number, count 1, kind 1, width 2, and mask 2. */
static void walk_u64_chain(Runtime *runtime, uint64_t ptr, FILE *out) {
  size_t memory_len = wasmtime_memory_data_size(runtime->context, &runtime->memory);
  emit(out, "[");
  for (uint64_t k = 0; ptr != 0; k++) {
    if (k > memory_len / 16) {
      die("list result does not end");
    }
    if (ptr < 48 || read_u64_at(runtime, ptr - 48) != OBJECT_MAGIC ||
        read_u64_at(runtime, ptr - 40) != 1 || read_u64_at(runtime, ptr - 24) != 1 ||
        read_u64_at(runtime, ptr - 16) != 2 || read_u64_at(runtime, ptr - 8) != 2) {
      die("list result has a wrong record header");
    }
    if (k != 0) {
      emit(out, ", ");
    }
    emit(out, "%" PRIu64, read_u64_at(runtime, ptr));
    ptr = read_u64_at(runtime, ptr + 8);
  }
  emit(out, "]\n");
}

static void print_u64_chain(Runtime *runtime, uint64_t ptr) {
  walk_u64_chain(runtime, ptr, NULL);
  walk_u64_chain(runtime, ptr, control_output);
}

/* Writes the tree of records at `ptr` in preorder, `.` for a leaf and a node's key followed
   by its subtrees, separated by commas, after checking that each record's header holds the
   magic number, count 1, kind 1, width 3, and mask 5.  `count` bounds the records visited. */
static void walk_u64_tree(Runtime *runtime, uint64_t ptr, uint64_t *count, FILE *out) {
  if (ptr == 0) {
    emit(out, ".");
    return;
  }
  size_t memory_len = wasmtime_memory_data_size(runtime->context, &runtime->memory);
  if (++*count > memory_len / 72) {
    die("tree result does not end");
  }
  if (ptr < 48 || read_u64_at(runtime, ptr - 48) != OBJECT_MAGIC ||
      read_u64_at(runtime, ptr - 40) != 1 || read_u64_at(runtime, ptr - 24) != 1 ||
      read_u64_at(runtime, ptr - 16) != 3 || read_u64_at(runtime, ptr - 8) != 5) {
    die("tree result has a wrong record header");
  }
  emit(out, "%" PRIu64 ",", read_u64_at(runtime, ptr + 8));
  walk_u64_tree(runtime, read_u64_at(runtime, ptr), count, out);
  emit(out, ",");
  walk_u64_tree(runtime, read_u64_at(runtime, ptr + 16), count, out);
}

static void print_u64_tree(Runtime *runtime, uint64_t ptr) {
  uint64_t count = 0;
  walk_u64_tree(runtime, ptr, &count, NULL);
  count = 0;
  walk_u64_tree(runtime, ptr, &count, control_output);
  fprintf(control_output, "\n");
}

/* Writes the tree of records at `ptr` in the preorder description of `alloc_records`, after
   checking that each record's header holds the magic number, count 1, kind 1, and a valid
   width and mask.  `count` bounds the records visited. */
static void walk_records(Runtime *runtime, uint64_t ptr, uint64_t *count, FILE *out) {
  if (ptr == 0) {
    emit(out, ".");
    return;
  }
  size_t memory_len = wasmtime_memory_data_size(runtime->context, &runtime->memory);
  if (++*count > memory_len / 56) {
    die("tree result does not end");
  }
  if (ptr < 48 || read_u64_at(runtime, ptr - 48) != OBJECT_MAGIC ||
      read_u64_at(runtime, ptr - 40) != 1 || read_u64_at(runtime, ptr - 24) != 1) {
    die("tree result has a wrong record header");
  }
  uint64_t width = read_u64_at(runtime, ptr - 16);
  uint64_t mask = read_u64_at(runtime, ptr - 8);
  if (!record_header_valid(width, mask)) {
    die("tree result has a wrong record header");
  }
  emit(out, "%" PRIu64 ",%" PRIu64, width, mask);
  for (uint64_t i = 0; i < width; i++) {
    emit(out, ",");
    uint64_t slot = read_u64_at(runtime, ptr + 8 * i);
    if ((mask >> i) & 1) {
      walk_records(runtime, slot, count, out);
    } else {
      emit(out, "%" PRIu64, slot);
    }
  }
}

static void print_records(Runtime *runtime, uint64_t ptr) {
  uint64_t count = 0;
  walk_records(runtime, ptr, &count, NULL);
  count = 0;
  walk_records(runtime, ptr, &count, control_output);
  fprintf(control_output, "\n");
}

/* Writes the `len` bytes at `ptr` in hexadecimal on one line. */
static void print_bytes(Runtime *runtime, uint64_t ptr, uint64_t len) {
  if (!runtime->has_memory) {
    die("ByteArray result requires exported memory");
  }
  size_t memory_len = wasmtime_memory_data_size(runtime->context, &runtime->memory);
  if (ptr > memory_len || len > memory_len - (size_t)ptr) {
    die("ByteArray result is outside memory");
  }
  uint8_t *memory = wasmtime_memory_data(runtime->context, &runtime->memory);
  for (uint64_t i = 0; i < len; i++) {
    fprintf(control_output, "%02x", memory[ptr + i]);
  }
  fprintf(control_output, "\n");
}

/* Writes the elements of the array at `ptr`, as little-endian words, to the file at `path`,
   and returns the number of elements. */
static uint64_t save_u64_array(Runtime *runtime, uint64_t ptr, const char *path) {
  if (!runtime->has_memory) {
    die("Array UInt64 result requires exported memory");
  }
  uint64_t len = read_u64_at(runtime, ptr);
  size_t memory_len = wasmtime_memory_data_size(runtime->context, &runtime->memory);
  if (len > (SIZE_MAX - 8) / 8 || ptr > memory_len ||
      8 + (size_t)len * 8 > memory_len - (size_t)ptr) {
    die("Array UInt64 result is outside memory");
  }
  uint8_t *memory = wasmtime_memory_data(runtime->context, &runtime->memory);
  FILE *file = fopen(path, "wb");
  if (file == NULL) {
    perror(path);
    finish_host(1);
  }
  if (len != 0 && fwrite(memory + ptr + 8, 8, (size_t)len, file) != (size_t)len) {
    perror("fwrite");
    finish_host(1);
  }
  if (fclose(file) != 0) {
    perror("fclose");
    finish_host(1);
  }
  return len;
}

/* An array whose elements are the little-endian words of the file at `path`. */
static uint64_t alloc_u64_file(Runtime *runtime, const char *path) {
  size_t len = 0;
  uint8_t *bytes = read_file(path, &len);
  if (len % 8 != 0) {
    die("file-u64 file length is not a multiple of 8");
  }
  uint64_t ptr = call_alloc(runtime, 8 + (uint64_t)len);
  write_u64_at(runtime, ptr, len / 8);
  size_t memory_len = wasmtime_memory_data_size(runtime->context, &runtime->memory);
  if (ptr > memory_len || 8 + len > memory_len - (size_t)ptr) {
    die("allocation is outside memory");
  }
  uint8_t *memory = wasmtime_memory_data(runtime->context, &runtime->memory);
  memcpy(memory + ptr + 8, bytes, len);
  free(bytes);
  return ptr;
}

static bool parse_arg(Runtime *runtime, const char *spec, wasmtime_val_t *out, size_t *out_count) {
  if (strncmp(spec, "i64:", 4) == 0) {
    out[0].kind = WASMTIME_I64;
    out[0].of.i64 = (int64_t)parse_u64(spec + 4);
    *out_count = 1;
    return true;
  }
  if (strncmp(spec, "f64:", 4) == 0) {
    uint64_t bits = parse_u64(spec + 4);
    out[0].kind = WASMTIME_F64;
    memcpy(&out[0].of.f64, &bits, sizeof bits);
    *out_count = 1;
    return true;
  }
  if (strncmp(spec, "f32:", 4) == 0) {
    uint64_t wide = parse_u64(spec + 4);
    if (wide > UINT32_MAX) {
      die("f32 bits exceed 32 bits");
    }
    uint32_t bits = (uint32_t)wide;
    out[0].kind = WASMTIME_F32;
    memcpy(&out[0].of.f32, &bits, sizeof bits);
    *out_count = 1;
    return true;
  }
  if (strncmp(spec, "bytes:", 6) == 0) {
    size_t len = 0;
    uint8_t *bytes = parse_hex(spec + 6, &len);
    uint64_t ptr = alloc_bytes(runtime, bytes, len);
    free(bytes);
    out[0].kind = WASMTIME_I64;
    out[0].of.i64 = (int64_t)ptr;
    out[1].kind = WASMTIME_I64;
    out[1].of.i64 = (int64_t)len;
    *out_count = 2;
    return true;
  }
  if (strncmp(spec, "bytes-file:", 11) == 0) {
    size_t len = 0;
    uint8_t *bytes = read_file(spec + 11, &len);
    uint64_t ptr = alloc_bytes(runtime, bytes, len);
    free(bytes);
    out[0].kind = WASMTIME_I64;
    out[0].of.i64 = (int64_t)ptr;
    out[1].kind = WASMTIME_I64;
    out[1].of.i64 = (int64_t)len;
    *out_count = 2;
    return true;
  }
  if (strncmp(spec, "file-u64:", 9) == 0) {
    out[0].kind = WASMTIME_I64;
    out[0].of.i64 = (int64_t)alloc_u64_file(runtime, spec + 9);
    *out_count = 1;
    return true;
  }
  if (strncmp(spec, "array-u64:", 10) == 0) {
    U64List values = parse_u64_list(spec + 10);
    uint64_t ptr = alloc_u64_array(runtime, values);
    free_u64_list(values);
    out[0].kind = WASMTIME_I64;
    out[0].of.i64 = (int64_t)ptr;
    *out_count = 1;
    return true;
  }
  if (strncmp(spec, "tree-u64:", 9) == 0) {
    const char *text = spec + 9;
    uint64_t ptr = alloc_u64_tree(runtime, &text);
    if (*text != 0) {
      die("bad tree description");
    }
    out[0].kind = WASMTIME_I64;
    out[0].of.i64 = (int64_t)ptr;
    *out_count = 1;
    return true;
  }
  if (strncmp(spec, "records-u64:", 12) == 0) {
    const char *text = spec + 12;
    uint64_t ptr = alloc_records(runtime, &text);
    if (*text != 0) {
      die("bad tree description");
    }
    out[0].kind = WASMTIME_I64;
    out[0].of.i64 = (int64_t)ptr;
    *out_count = 1;
    return true;
  }
  if (strncmp(spec, "chain-u64:", 10) == 0) {
    U64List values = parse_u64_list(spec + 10);
    uint64_t ptr = alloc_u64_chain(runtime, values);
    free_u64_list(values);
    out[0].kind = WASMTIME_I64;
    out[0].of.i64 = (int64_t)ptr;
    *out_count = 1;
    return true;
  }
  return false;
}

/* The kind of result `index` in a `list:K1,K2,...` result spec, copied into `out`. */
static void list_result_kind(const char *kind, size_t index, char *out, size_t out_len) {
  const char *start = kind + 5;
  for (size_t i = 0; i < index; i++) {
    start = strchr(start, ',');
    if (start == NULL) {
      die("result list is too short");
    }
    start++;
  }
  const char *end = strchr(start, ',');
  size_t len = end == NULL ? strlen(start) : (size_t)(end - start);
  if (len + 1 > out_len) {
    die("result kind is too long");
  }
  memcpy(out, start, len);
  out[len] = 0;
}

static size_t result_count_from_kind(const char *kind) {
  if (strcmp(kind, "i64") == 0 || strcmp(kind, "f64") == 0 || strcmp(kind, "f32") == 0) {
    return 1;
  }
  if (strncmp(kind, "list:", 5) == 0) {
    size_t items = 1;
    for (const char *c = kind + 5; *c != 0; c++) {
      if (*c == ',') {
        items++;
      }
    }
    if (items > 128) {
      die("too many results");
    }
    /* A `bytes` item is two results, the root and the length. */
    size_t count = 0;
    for (size_t i = 0; i < items; i++) {
      char item[32];
      list_result_kind(kind, i, item, sizeof item);
      count += strcmp(item, "bytes") == 0 ? 2 : 1;
    }
    if (count > 128) {
      die("too many results");
    }
    return count;
  }
  if (strcmp(kind, "bytes") == 0) {
    return 2;
  }
  if (strcmp(kind, "array-u64") == 0 || strcmp(kind, "chain-u64") == 0 ||
      strcmp(kind, "tree-u64") == 0 || strcmp(kind, "records-u64") == 0 ||
      strncmp(kind, "file-u64:", 9) == 0) {
    return 1;
  }
  if (strncmp(kind, "slots:", 6) == 0) {
    uint64_t count = parse_u64(kind + 6);
    if (count > 128) {
      die("too many result slots");
    }
    return (size_t)count;
  }
  die("unknown result kind");
  return 0;
}

/* Places the arguments `argv` of a call into `args` and returns their number. */
static size_t place_args(Runtime *runtime, int argc, char **argv, wasmtime_val_t *args) {
  size_t nargs = 0;
  for (int i = 0; i < argc; i++) {
    if (nargs == 256) {
      die("too many arguments");
    }
    wasmtime_val_t parsed[2];
    size_t count = 0;
    if (!parse_arg(runtime, argv[i], parsed, &count)) {
      fprintf(stderr, "unknown argument spec: %s\n", argv[i]);
      finish_host(1);
    }
    if (count > 256 - nargs) {
      die("too many arguments");
    }
    memcpy(args + nargs, parsed, count * sizeof(*parsed));
    nargs += count;
  }
  return nargs;
}

/* Sets the kinds of the results that `result_kind` describes and returns their number. */
static size_t result_slots(const char *result_kind, wasmtime_val_t *results) {
  size_t nresults = result_count_from_kind(result_kind);
  bool list = strncmp(result_kind, "list:", 5) == 0;
  /* Result `i` belongs to item `item` of a list; a `bytes` item covers two results. */
  for (size_t i = 0, item = 0; i < nresults; item++) {
    const char *kind = result_kind;
    char text[32];
    if (list) {
      list_result_kind(result_kind, item, text, sizeof text);
      kind = text;
    }
    size_t width = list && strcmp(kind, "bytes") == 0 ? 2 : 1;
    for (size_t j = 0; j < width; j++, i++) {
      results[i].kind = strcmp(kind, "f64") == 0   ? WASMTIME_F64
                        : strcmp(kind, "f32") == 0 ? WASMTIME_F32
                                                   : WASMTIME_I64;
    }
  }
  return nresults;
}

/* Prints the results of a call as `result_kind` describes them. */
static void print_call_results(Runtime *runtime, const char *result_kind, wasmtime_val_t *results,
                               size_t nresults) {
  bool list = strncmp(result_kind, "list:", 5) == 0;

  if (list) {
    /* One line per item: an i64 or f64 as a decimal word, bytes in hexadecimal, an array as its
       elements, a tree in the notation of its argument. */
    for (size_t i = 0, item = 0; i < nresults; i++, item++) {
      char kind[32];
      list_result_kind(result_kind, item, kind, sizeof kind);
      if (strcmp(kind, "bytes") == 0) {
        print_bytes(runtime, (uint64_t)results[i].of.i64, (uint64_t)results[i + 1].of.i64);
        i++;
      } else if (strcmp(kind, "f64") == 0) {
        uint64_t bits = 0;
        memcpy(&bits, &results[i].of.f64, sizeof bits);
        fprintf(control_output, "%" PRIu64 "\n", bits);
      } else if (strcmp(kind, "f32") == 0) {
        uint32_t bits = 0;
        memcpy(&bits, &results[i].of.f32, sizeof bits);
        fprintf(control_output, "%" PRIu32 "\n", bits);
      } else if (strcmp(kind, "i64") == 0) {
        fprintf(control_output, "%" PRIu64 "\n", (uint64_t)results[i].of.i64);
      } else if (strcmp(kind, "array-u64") == 0) {
        if (!runtime->has_memory) {
          die("Array UInt64 result requires exported memory");
        }
        uint64_t ptr = (uint64_t)results[i].of.i64;
        uint64_t len = read_u64_at(runtime, ptr);
        size_t memory_len = wasmtime_memory_data_size(runtime->context, &runtime->memory);
        if (len > (SIZE_MAX - 8) / 8 || ptr > memory_len ||
            8 + (size_t)len * 8 > memory_len - (size_t)ptr) {
          die("Array UInt64 result is outside memory");
        }
        fprintf(control_output, "[");
        for (uint64_t j = 0; j < len; j++) {
          if (j != 0) {
            fprintf(control_output, ", ");
          }
          fprintf(control_output, "%" PRIu64, read_u64_at(runtime, ptr + 8 + j * 8));
        }
        fprintf(control_output, "]\n");
      } else if (strcmp(kind, "chain-u64") == 0) {
        if (!runtime->has_memory) {
          die("List UInt64 result requires exported memory");
        }
        print_u64_chain(runtime, (uint64_t)results[i].of.i64);
      } else if (strcmp(kind, "tree-u64") == 0) {
        if (!runtime->has_memory) {
          die("tree result requires exported memory");
        }
        print_u64_tree(runtime, (uint64_t)results[i].of.i64);
      } else if (strcmp(kind, "records-u64") == 0) {
        if (!runtime->has_memory) {
          die("tree result requires exported memory");
        }
        print_records(runtime, (uint64_t)results[i].of.i64);
      } else {
        die("unknown result kind in list");
      }
    }
    return;
  }

  if (strcmp(result_kind, "f64") == 0) {
    if (results[0].kind != WASMTIME_F64) {
      die("expected f64 result");
    }
    uint64_t bits = 0;
    memcpy(&bits, &results[0].of.f64, sizeof bits);
    fprintf(control_output, "%" PRIu64 "\n", bits);
    return;
  }

  if (strcmp(result_kind, "f32") == 0) {
    if (results[0].kind != WASMTIME_F32) {
      die("expected f32 result");
    }
    uint32_t bits = 0;
    memcpy(&bits, &results[0].of.f32, sizeof bits);
    fprintf(control_output, "%" PRIu32 "\n", bits);
    return;
  }

  if (strcmp(result_kind, "bytes") == 0) {
    print_bytes(runtime, (uint64_t)results[0].of.i64, (uint64_t)results[1].of.i64);
    return;
  }

  if (strcmp(result_kind, "array-u64") == 0) {
    if (!runtime->has_memory) {
      die("Array UInt64 result requires exported memory");
    }
    uint64_t ptr = (uint64_t)results[0].of.i64;
    uint64_t len = read_u64_at(runtime, ptr);
    if (len > (SIZE_MAX - 8) / 8) {
      die("Array UInt64 result length is too large");
    }
    size_t byte_len = 8 + (size_t)len * 8;
    size_t memory_len = wasmtime_memory_data_size(runtime->context, &runtime->memory);
    if (ptr > memory_len || byte_len > memory_len - (size_t)ptr) {
      die("Array UInt64 result is outside memory");
    }
    fprintf(control_output, "[");
    for (uint64_t i = 0; i < len; i++) {
      if (i != 0) {
        fprintf(control_output, ", ");
      }
      fprintf(control_output, "%" PRIu64, read_u64_at(runtime, ptr + 8 + i * 8));
    }
    fprintf(control_output, "]\n");
    return;
  }

  if (strcmp(result_kind, "chain-u64") == 0) {
    if (!runtime->has_memory) {
      die("List UInt64 result requires exported memory");
    }
    print_u64_chain(runtime, (uint64_t)results[0].of.i64);
    return;
  }

  if (strcmp(result_kind, "tree-u64") == 0) {
    if (!runtime->has_memory) {
      die("tree result requires exported memory");
    }
    print_u64_tree(runtime, (uint64_t)results[0].of.i64);
    return;
  }

  if (strcmp(result_kind, "records-u64") == 0) {
    if (!runtime->has_memory) {
      die("tree result requires exported memory");
    }
    print_records(runtime, (uint64_t)results[0].of.i64);
    return;
  }

  if (strncmp(result_kind, "file-u64:", 9) == 0) {
    save_u64_array(runtime, (uint64_t)results[0].of.i64, result_kind + 9);
    return;
  }

  for (size_t i = 0; i < nresults; i++) {
    if (results[i].kind != WASMTIME_I64) {
      die("expected i64 result");
    }
    if (i != 0) {
      fprintf(control_output, " ");
    }
    fprintf(control_output, "%" PRIu64, (uint64_t)results[i].of.i64);
  }
  fprintf(control_output, "\n");
}

static void call_export(Runtime *runtime, const char *func_name, const char *result_kind,
                        int argc, char **argv) {
  wasmtime_func_t func = get_func(runtime, func_name);
  wasmtime_val_t args[256];
  wasmtime_val_t results[128];
  size_t nargs = place_args(runtime, argc, argv, args);
  size_t nresults = result_slots(result_kind, results);
  call_func(runtime, &func, args, nargs, results, nresults, 2);
  print_call_results(runtime, result_kind, results, nresults);
}

static uint64_t now_ns(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return (uint64_t)t.tv_sec * 1000000000u + (uint64_t)t.tv_nsec;
}

/* Calls the export once to warm up, and then repeatedly until `seconds` have passed or `max`
   timed calls have run, placing the arguments again before each call and timing only the
   call.  Prints the results of the last call, then `bench N NS`. */
static void bench_export(Runtime *runtime, const char *seconds, const char *max,
                         const char *func_name, const char *result_kind, int argc, char **argv) {
  wasmtime_func_t func = get_func(runtime, func_name);
  wasmtime_val_t args[256];
  wasmtime_val_t results[128];
  uint64_t limit = (uint64_t)(atof(seconds) * 1e9), most = parse_u64(max);
  uint64_t count = 0, total = 0;
  size_t nargs = place_args(runtime, argc, argv, args);
  size_t nresults = result_slots(result_kind, results);
  call_func(runtime, &func, args, nargs, results, nresults, 2);
  uint64_t start = now_ns();
  while (count < most && now_ns() - start < limit) {
    place_args(runtime, argc, argv, args);
    result_slots(result_kind, results);
    uint64_t before = now_ns();
    call_func(runtime, &func, args, nargs, results, nresults, 2);
    total += now_ns() - before;
    count++;
  }
  print_call_results(runtime, result_kind, results, nresults);
  fprintf(control_output, "bench %" PRIu64 " %" PRIu64 "\n", count, total);
}

static uint64_t read_global_u64(Runtime *runtime, const char *name) {
  wasmtime_extern_t item;
  if (!wasmtime_instance_export_get(runtime->context, &runtime->instance, name, strlen(name), &item)) {
    fprintf(stderr, "missing export: %s\n", name);
    finish_host(1);
  }
  if (item.kind != WASMTIME_EXTERN_GLOBAL) {
    fprintf(stderr, "export is not a global: %s\n", name);
    finish_host(1);
  }
  wasmtime_val_t value;
  wasmtime_global_get(runtime->context, &item.of.global, &value);
  if (value.kind != WASMTIME_I64) {
    die("expected i64 global");
  }
  return (uint64_t)value.of.i64;
}

static void print_stats(Runtime *runtime) {
  fprintf(control_output, "stats %" PRIu64 " %" PRIu64 "\n", read_global_u64(runtime, "allocCount"),
          read_global_u64(runtime, "freeCount"));
}

static void invoke_func(Runtime *runtime, wasmtime_func_t *func, wasmtime_val_t *args,
                        size_t nargs, wasmtime_val_t *results, size_t nresults) {
  for (size_t i = 0; i < nresults; i++) {
    results[i].kind = WASMTIME_I64;
  }
  call_func(runtime, func, args, nargs, results, nresults, 2);
  for (size_t i = 0; i < nresults; i++) {
    if (results[i].kind != WASMTIME_I64) {
      die("expected i64 result");
    }
  }
}

static void invoke_noarg(Runtime *runtime, const char *func_name, wasmtime_val_t *results,
                         size_t nresults) {
  wasmtime_func_t func = get_func(runtime, func_name);
  invoke_func(runtime, &func, NULL, 0, results, nresults);
}

static void expect_eq_u64(const char *label, uint64_t expected, uint64_t actual) {
  if (expected != actual) {
    fprintf(stderr, "%s: expected %" PRIu64 ", got %" PRIu64 "\n", label, expected, actual);
    finish_host(1);
  }
}

static int compare_u64(const void *left, const void *right) {
  uint64_t a = *(const uint64_t *)left;
  uint64_t b = *(const uint64_t *)right;
  return (a > b) - (a < b);
}

static void expect_same_multiset(const char *label, uint64_t *expected, uint64_t *actual,
                                 size_t len) {
  qsort(expected, len, sizeof(uint64_t), compare_u64);
  qsort(actual, len, sizeof(uint64_t), compare_u64);
  for (size_t i = 0; i < len; i++) {
    if (expected[i] != actual[i]) {
      fprintf(stderr, "%s: pointer set differs\n", label);
      finish_host(1);
    }
  }
}

static void command_release_reuse(Runtime *runtime, int argc, char **argv) {
  if (argc != 4) {
    die("usage: release-reuse <module.wasm> <function> <nresults> <ptr-index> <alloc-size>");
  }
  size_t nresults = (size_t)parse_u64(argv[1]);
  size_t ptr_index = (size_t)parse_u64(argv[2]);
  uint64_t alloc_size = parse_u64(argv[3]);
  if (nresults > 128 || ptr_index >= nresults) {
    die("invalid result index");
  }
  wasmtime_val_t results[128];
  invoke_noarg(runtime, argv[0], results, nresults);
  uint64_t ptr = (uint64_t)results[ptr_index].of.i64;
  wasmtime_func_t release = required_runtime_func(runtime, "release");
  call_void_i64_func(runtime, &release, ptr);
  uint64_t reused = call_alloc(runtime, alloc_size);
  expect_eq_u64("release reuse", ptr, reused);
}

static void command_free_alias(Runtime *runtime, int argc, char **argv) {
  if (argc != 2) {
    die("usage: free-alias <module.wasm> <function> <expected-hex>");
  }
  size_t expected_len = 0;
  uint8_t *expected = parse_hex(argv[1], &expected_len);
  wasmtime_val_t results[2];
  invoke_noarg(runtime, argv[0], results, 2);
  uint64_t ptr = (uint64_t)results[0].of.i64;
  uint64_t len = (uint64_t)results[1].of.i64;
  if (len != expected_len) {
    die("unexpected byte length");
  }
  size_t memory_len = wasmtime_memory_data_size(runtime->context, &runtime->memory);
  if (ptr > memory_len || len > memory_len - (size_t)ptr) {
    die("ByteArray result is outside memory");
  }
  uint8_t *memory = wasmtime_memory_data(runtime->context, &runtime->memory);
  if (memcmp(memory + ptr, expected, expected_len) != 0) {
    die("unexpected byte result");
  }
  free(expected);
  wasmtime_func_t free_func = required_runtime_func(runtime, "free");
  call_void_i64_func(runtime, &free_func, ptr);
  uint64_t reused = call_alloc(runtime, len);
  expect_eq_u64("free alias reuse", ptr, reused);
}

static void command_temp_byte_call(Runtime *runtime, int argc, char **argv) {
  if (argc != 4) {
    die("usage: temp-byte-call <module.wasm> <function> <input-hex> <expected-result> <temp-size>");
  }
  size_t input_len = 0;
  uint8_t *input = parse_hex(argv[1], &input_len);
  uint64_t expected_result = parse_u64(argv[2]);
  uint64_t temp_size = parse_u64(argv[3]);
  reset_runtime(runtime);
  uint64_t probe_input = call_alloc(runtime, input_len);
  uint64_t expected_temp = call_alloc(runtime, temp_size);
  reset_runtime(runtime);
  uint64_t input_ptr = alloc_bytes(runtime, input, input_len);
  free(input);
  expect_eq_u64("reset input pointer", probe_input, input_ptr);
  wasmtime_func_t func = get_func(runtime, argv[0]);
  wasmtime_val_t args[2];
  wasmtime_val_t results[1];
  args[0].kind = WASMTIME_I64;
  args[0].of.i64 = (int64_t)input_ptr;
  args[1].kind = WASMTIME_I64;
  args[1].of.i64 = (int64_t)input_len;
  invoke_func(runtime, &func, args, 2, results, 1);
  expect_eq_u64("function result", expected_result, (uint64_t)results[0].of.i64);
  uint64_t reused = call_alloc(runtime, temp_size);
  expect_eq_u64("temporary reuse", expected_temp, reused);
}

static void command_temp_array_call(Runtime *runtime, int argc, char **argv) {
  if (argc != 4) {
    die("usage: temp-array-call <module.wasm> <function> <u64-list> <expected-result> <temp-size>");
  }
  U64List values = parse_u64_list(argv[1]);
  uint64_t expected_result = parse_u64(argv[2]);
  uint64_t temp_size = parse_u64(argv[3]);
  reset_runtime(runtime);
  uint64_t probe_input = alloc_u64_array(runtime, values);
  uint64_t expected_temp = call_alloc(runtime, temp_size);
  reset_runtime(runtime);
  uint64_t input_ptr = alloc_u64_array(runtime, values);
  free_u64_list(values);
  expect_eq_u64("reset array pointer", probe_input, input_ptr);
  wasmtime_func_t func = get_func(runtime, argv[0]);
  wasmtime_val_t args[1];
  wasmtime_val_t results[1];
  args[0].kind = WASMTIME_I64;
  args[0].of.i64 = (int64_t)input_ptr;
  invoke_func(runtime, &func, args, 1, results, 1);
  expect_eq_u64("function result", expected_result, (uint64_t)results[0].of.i64);
  uint64_t reused = call_alloc(runtime, temp_size);
  expect_eq_u64("temporary reuse", expected_temp, reused);
}

static void command_noarg_temp_reuse(Runtime *runtime, int argc, char **argv) {
  if (argc != 3) {
    die("usage: noarg-temp-reuse <module.wasm> <function> <expected-result> <alloc-sizes>");
  }
  uint64_t expected_result = parse_u64(argv[1]);
  U64List sizes = parse_u64_list(argv[2]);
  uint64_t *expected = calloc(sizes.len, sizeof(uint64_t));
  uint64_t *actual = calloc(sizes.len, sizeof(uint64_t));
  if ((expected == NULL || actual == NULL) && sizes.len != 0) {
    die("out of memory");
  }
  reset_runtime(runtime);
  for (size_t i = 0; i < sizes.len; i++) {
    expected[i] = call_alloc(runtime, sizes.items[i]);
  }
  reset_runtime(runtime);
  wasmtime_val_t result[1];
  invoke_noarg(runtime, argv[0], result, 1);
  expect_eq_u64("function result", expected_result, (uint64_t)result[0].of.i64);
  for (size_t i = 0; i < sizes.len; i++) {
    actual[i] = call_alloc(runtime, sizes.items[i]);
  }
  expect_same_multiset("temporary reuse", expected, actual, sizes.len);
  free(expected);
  free(actual);
  free_u64_list(sizes);
}

static void command_allocator_grows(Runtime *runtime, int argc, char **argv) {
  if (argc != 0) {
    die("usage: allocator-grows <module.wasm>");
  }
  (void)argv;
  reset_runtime(runtime);
  size_t before = wasmtime_memory_data_size(runtime->context, &runtime->memory);
  uint64_t ptr = call_alloc(runtime, before);
  size_t after = wasmtime_memory_data_size(runtime->context, &runtime->memory);
  if (after <= before) {
    die("alloc did not grow memory");
  }
  if (ptr > after || before > after - (size_t)ptr) {
    die("grown allocation exceeds memory");
  }
  uint8_t *memory = wasmtime_memory_data(runtime->context, &runtime->memory);
  memory[ptr + before - 1] = 123;
}

static void write_bytes_at(Runtime *runtime, uint64_t ptr, const uint8_t *bytes, size_t len) {
  if (!runtime->has_memory) {
    die("missing memory export");
  }
  size_t memory_len = wasmtime_memory_data_size(runtime->context, &runtime->memory);
  if (ptr > memory_len || len > memory_len - (size_t)ptr) {
    die("byte write is outside memory");
  }
  uint8_t *memory = wasmtime_memory_data(runtime->context, &runtime->memory);
  memcpy(memory + ptr, bytes, len);
}

static uint64_t checked_add_u64(uint64_t left, uint64_t right) {
  if (right > UINT64_MAX - left) {
    die("u64 addition overflow");
  }
  return left + right;
}

static uint64_t resolve_script_value(const char *text, const wasmtime_val_t *results,
                                     size_t nresults, const uint64_t *vars) {
  if (strncmp(text, "result:", 7) == 0) {
    uint64_t index = parse_u64(text + 7);
    if (index >= nresults) {
      die("result index is outside result slots");
    }
    return (uint64_t)results[index].of.i64;
  }
  if (strncmp(text, "u64:", 4) == 0) {
    uint64_t index = parse_u64(text + 4);
    if (index >= 4096) {
      die("u64 variable id is too large");
    }
    return vars[index];
  }
  return parse_u64(text);
}

static void print_memory_range(Runtime *runtime, uint64_t ptr, uint64_t len) {
  if (!runtime->has_memory) {
    die("missing memory export");
  }
  size_t memory_len = wasmtime_memory_data_size(runtime->context, &runtime->memory);
  if (ptr > memory_len || len > memory_len - (size_t)ptr) {
    die("memory read is outside memory");
  }
  uint8_t *memory = wasmtime_memory_data(runtime->context, &runtime->memory);
  fprintf(control_output, "memory %" PRIu64 " %" PRIu64 " ", ptr, len);
  for (uint64_t i = 0; i < len; i++) {
    fprintf(control_output, "%02x", memory[ptr + i]);
  }
  fprintf(control_output, "\n");
}

static void command_script(Runtime *runtime, int argc, char **argv, bool session) {
  if (argc != 0) {
    die("usage: script|session <module.wasm>");
  }
  (void)argv;
  uint64_t ids[4096];
  uint64_t vars[4096];
  wasmtime_val_t args[256];
  wasmtime_val_t results[128];
  size_t nargs = 0;
  size_t nresults = 0;
  bool called = false;
  memset(ids, 0, sizeof(ids));
  memset(vars, 0, sizeof(vars));
  memset(results, 0, sizeof(results));
  char line[16384];
  while (fgets(line, sizeof(line), stdin) != NULL) {
    size_t len = strlen(line);
    if (len == sizeof(line) - 1 && line[len - 1] != '\n') {
      die("script command is too long");
    }
    while (len > 0 && (line[len - 1] == '\n' || line[len - 1] == '\r')) {
      line[--len] = 0;
    }
    if (len == 0) {
      continue;
    }
    char *command = strtok(line, " ");
    if (command == NULL) {
      continue;
    }
    if (strcmp(command, "alloc") == 0) {
      char *id_text = strtok(NULL, " ");
      char *size_text = strtok(NULL, " ");
      if (id_text == NULL || size_text == NULL) {
        die("alloc requires id and size");
      }
      uint64_t id = parse_u64(id_text);
      if (id >= 4096) {
        die("allocation id is too large");
      }
      ids[id] = call_alloc(runtime, parse_u64(size_text));
    } else if (strcmp(command, "bytes-file") == 0) {
      char *id_text = strtok(NULL, " ");
      char *path = strtok(NULL, "");
      if (id_text == NULL || path == NULL) {
        die("bytes-file requires id and path");
      }
      uint64_t id = parse_u64(id_text);
      if (id >= 4096) {
        die("allocation id is too large");
      }
      size_t byte_len = 0;
      uint8_t *bytes = read_file(path, &byte_len);
      ids[id] = alloc_bytes(runtime, bytes, byte_len);
      free(bytes);
    } else if (strcmp(command, "file-u64") == 0) {
      char *id_text = strtok(NULL, " ");
      char *path = strtok(NULL, "");
      if (id_text == NULL || path == NULL) {
        die("file-u64 requires id and path");
      }
      uint64_t id = parse_u64(id_text);
      if (id >= 4096) {
        die("allocation id is too large");
      }
      ids[id] = alloc_u64_file(runtime, path);
    } else if (strcmp(command, "keep") == 0) {
      char *id_text = strtok(NULL, " ");
      char *value_text = strtok(NULL, " ");
      if (id_text == NULL || value_text == NULL) {
        die("keep requires id and value");
      }
      uint64_t id = parse_u64(id_text);
      if (id >= 4096) {
        die("allocation id is too large");
      }
      ids[id] = resolve_script_value(value_text, results, nresults, vars);
    } else if (strcmp(command, "save-u64") == 0) {
      char *value_text = strtok(NULL, " ");
      char *path = strtok(NULL, "");
      if (value_text == NULL || path == NULL) {
        die("save-u64 requires a pointer and a path");
      }
      uint64_t ptr = resolve_script_value(value_text, results, nresults, vars);
      fprintf(control_output, "saved %" PRIu64 "\n", save_u64_array(runtime, ptr, path));
    } else if (strcmp(command, "bytes") == 0) {
      char *id_text = strtok(NULL, " ");
      char *hex = strtok(NULL, " ");
      if (id_text == NULL || hex == NULL) {
        die("bytes requires id and hex");
      }
      uint64_t id = parse_u64(id_text);
      if (id >= 4096) {
        die("allocation id is too large");
      }
      size_t byte_len = 0;
      uint8_t *bytes = parse_hex(hex, &byte_len);
      ids[id] = alloc_bytes(runtime, bytes, byte_len);
      free(bytes);
    } else if (strcmp(command, "write-u64") == 0 || strcmp(command, "write-ptr") == 0) {
      char *id_text = strtok(NULL, " ");
      char *offset_text = strtok(NULL, " ");
      char *value_text = strtok(NULL, " ");
      if (id_text == NULL || offset_text == NULL || value_text == NULL) {
        die("write requires id, offset, and value");
      }
      uint64_t id = parse_u64(id_text);
      if (id >= 4096) {
        die("allocation id is too large");
      }
      uint64_t value = 0;
      if (strcmp(command, "write-ptr") == 0) {
        uint64_t value_id = parse_u64(value_text);
        if (value_id >= 4096) {
          die("pointer id is too large");
        }
        value = ids[value_id];
      } else {
        value = parse_u64(value_text);
      }
      write_u64_at(runtime, checked_add_u64(ids[id], parse_u64(offset_text)), value);
    } else if (strcmp(command, "write-bytes") == 0) {
      char *id_text = strtok(NULL, " ");
      char *offset_text = strtok(NULL, " ");
      char *hex = strtok(NULL, " ");
      if (id_text == NULL || offset_text == NULL || hex == NULL) {
        die("write-bytes requires id, offset, and hex");
      }
      uint64_t id = parse_u64(id_text);
      if (id >= 4096) {
        die("allocation id is too large");
      }
      size_t byte_len = 0;
      uint8_t *bytes = parse_hex(hex, &byte_len);
      write_bytes_at(runtime, checked_add_u64(ids[id], parse_u64(offset_text)), bytes, byte_len);
      free(bytes);
    } else if (strcmp(command, "arg-u64") == 0 || strcmp(command, "arg-ptr") == 0) {
      char *value_text = strtok(NULL, " ");
      if (value_text == NULL) {
        die("arg requires value");
      }
      if (nargs >= 256) {
        die("too many arguments");
      }
      uint64_t value = 0;
      if (strcmp(command, "arg-ptr") == 0) {
        uint64_t id = parse_u64(value_text);
        if (id >= 4096) {
          die("pointer id is too large");
        }
        value = ids[id];
      } else {
        value = resolve_script_value(value_text, results, nresults, vars);
      }
      args[nargs].kind = WASMTIME_I64;
      args[nargs].of.i64 = (int64_t)value;
      nargs++;
    } else if (strcmp(command, "arg-f64") == 0) {
      char *bits_text = strtok(NULL, " ");
      if (bits_text == NULL) {
        die("arg-f64 requires bits");
      }
      if (nargs >= 256) {
        die("too many arguments");
      }
      uint64_t bits = parse_u64(bits_text);
      args[nargs].kind = WASMTIME_F64;
      memcpy(&args[nargs].of.f64, &bits, sizeof bits);
      nargs++;
    } else if (strcmp(command, "call") == 0) {
      char *func_name = strtok(NULL, " ");
      char *nresults_text = strtok(NULL, " ");
      char *dump_text = strtok(NULL, " ");
      if (func_name == NULL || nresults_text == NULL) {
        die("call requires function and result count");
      }
      if (dump_text != NULL && parse_u64(dump_text) != 0) {
        die("full memory dump is unsupported; use read-memory");
      }
      if (called && !session) {
        die("script may call only one export");
      }
      nresults = (size_t)parse_u64(nresults_text);
      if (nresults > 128) {
        die("too many result slots");
      }
      wasmtime_func_t func = get_func(runtime, func_name);
      invoke_func(runtime, &func, args, nargs, results, nresults);
      nargs = 0;
      called = true;
      fprintf(control_output, "results");
      for (size_t i = 0; i < nresults; i++) {
        fprintf(control_output, " %" PRIu64, (uint64_t)results[i].of.i64);
      }
      fprintf(control_output, "\n");
    } else if (strcmp(command, "read-u64") == 0) {
      char *id_text = strtok(NULL, " ");
      char *ptr_text = strtok(NULL, " ");
      char *offset_text = strtok(NULL, " ");
      if (id_text == NULL || ptr_text == NULL || offset_text == NULL) {
        die("read-u64 requires id, pointer, and offset");
      }
      if (!called) {
        die("read-u64 requires a prior call");
      }
      uint64_t id = parse_u64(id_text);
      if (id >= 4096) {
        die("u64 variable id is too large");
      }
      uint64_t ptr = resolve_script_value(ptr_text, results, nresults, vars);
      uint64_t offset = resolve_script_value(offset_text, results, nresults, vars);
      vars[id] = read_u64_at(runtime, checked_add_u64(ptr, offset));
      fprintf(control_output, "u64 %" PRIu64 " %" PRIu64 "\n", id, vars[id]);
    } else if (strcmp(command, "read-memory") == 0) {
      char *ptr_text = strtok(NULL, " ");
      char *len_text = strtok(NULL, " ");
      if (ptr_text == NULL || len_text == NULL) {
        die("read-memory requires pointer and length");
      }
      if (!called) {
        die("read-memory requires a prior call");
      }
      uint64_t ptr = resolve_script_value(ptr_text, results, nresults, vars);
      uint64_t len = resolve_script_value(len_text, results, nresults, vars);
      print_memory_range(runtime, ptr, len);
    } else if (strcmp(command, "stats") == 0) {
      print_stats(runtime);
    } else if (strcmp(command, "memory-size") == 0) {
      if (!runtime->has_memory) {
        die("missing memory export");
      }
      fprintf(control_output, "memory-size %zu\n",
              wasmtime_memory_data_size(runtime->context, &runtime->memory));
    } else if (strcmp(command, "done") == 0) {
      if (!called) {
        die("done requires a prior call");
      }
      return;
    } else {
      die("unknown script command");
    }
    if (session && fflush(control_output) != 0) {
      die("cannot flush session output");
    }
  }
  if (ferror(stdin)) {
    die("cannot read script input");
  }
  if (!called) {
    die("script ended before call");
  }
}

static _Noreturn void usage(void) {
  fprintf(stderr,
          "usage: wasmtime-host [--wasi] [--stdin-file PATH] [--stdout-file PATH] "
          "[--stderr-file PATH] [--control-file PATH] <mode> <module.wasm> [arguments]\n"
          "       wasmtime-host [options] run <module.wasm>\n"
          "       wasmtime-host [options] call|call-stats <module.wasm> <function> "
          "<i64|f64|f32|bytes|array-u64|chain-u64|tree-u64|records-u64|file-u64:PATH|slots:N|"
          "list:K1,K2,...> "
          "[i64:N|f64:BITS|f32:BITS|bytes:HEX|bytes-file:PATH|array-u64:N,N|chain-u64:N,N|tree-u64:K,.,.|"
          "records-u64:W,M,S,...|file-u64:PATH ...]\n"
          "       wasmtime-host bench <module.wasm> SECONDS MAX <function> <result> [arguments]\n"
          "       wasmtime-host [options] script|session <module.wasm> < commands\n"
          "       wasmtime-host release-reuse|free-alias|temp-byte-call|temp-array-call|"
          "noarg-temp-reuse|allocator-grows <module.wasm> [arguments]\n");
  finish_host(1);
}

static int parse_options(int argc, char **argv) {
  int i = 1;
  while (i < argc && strncmp(argv[i], "--", 2) == 0) {
    const char *option = argv[i++];
    if (strcmp(option, "--") == 0) {
      break;
    }
    if (strcmp(option, "--wasi") == 0) {
      options.wasi = true;
      continue;
    }
    const char **path = NULL;
    if (strcmp(option, "--stdin-file") == 0) {
      path = &options.stdin_file;
    } else if (strcmp(option, "--stdout-file") == 0) {
      path = &options.stdout_file;
    } else if (strcmp(option, "--stderr-file") == 0) {
      path = &options.stderr_file;
    } else if (strcmp(option, "--control-file") == 0) {
      path = &options.control_file;
    } else {
      fprintf(stderr, "unknown host option: %s\n", option);
      usage();
    }
    if (i == argc) {
      fprintf(stderr, "missing path for %s\n", option);
      usage();
    }
    *path = argv[i++];
  }
  if (i >= argc) {
    usage();
  }
  options.command = strcmp(argv[i], "run") == 0;
  if (options.command) {
    options.wasi = true;
  }
  if (!options.wasi &&
      (options.stdin_file != NULL || options.stdout_file != NULL || options.stderr_file != NULL)) {
    die("guest stream options require --wasi or run");
  }
  if (options.wasi && !options.command && options.control_file == NULL &&
      options.stdout_file == NULL) {
    die("WASI callable modes require --control-file or --stdout-file");
  }
  if (options.wasi && options.stdin_file == NULL &&
      (strcmp(argv[i], "script") == 0 || strcmp(argv[i], "session") == 0)) {
    die("WASI script/session requires --stdin-file for guest input");
  }
  options.control_records = !options.command || options.control_file != NULL;
  if (options.control_file != NULL) {
    control_output = fopen(options.control_file, "wb");
    if (control_output == NULL) {
      perror(options.control_file);
      finish_host(1);
    }
    owns_control_output = true;
  }
  return i;
}

int main(int argc, char **argv) {
  control_output = stdout;
  int first = parse_options(argc, argv);
  argc -= first - 1;
  argv += first - 1;
  if (argc < 3) {
    usage();
  }
  Runtime runtime = {0};
  active_runtime = &runtime;
  if (options.command) {
    if (argc != 3) {
      usage();
    }
    init_runtime(&runtime, argv[2]);
    wasmtime_func_t start = get_func(&runtime, "_start");
    call_func(&runtime, &start, NULL, 0, NULL, 0, 2);
    if (options.control_records) {
      fprintf(control_output, "return\n");
    }
  } else if (strcmp(argv[1], "call") == 0) {
    if (argc < 5) {
      usage();
    }
    init_runtime(&runtime, argv[2]);
    call_export(&runtime, argv[3], argv[4], argc - 5, argv + 5);
  } else if (strcmp(argv[1], "call-stats") == 0) {
    if (argc < 5) {
      usage();
    }
    init_runtime(&runtime, argv[2]);
    call_export(&runtime, argv[3], argv[4], argc - 5, argv + 5);
    print_stats(&runtime);
  } else if (strcmp(argv[1], "bench") == 0) {
    if (argc < 7) {
      usage();
    }
    uint64_t before = now_ns();
    init_runtime(&runtime, argv[2]);
    uint64_t init = now_ns() - before;
    bench_export(&runtime, argv[3], argv[4], argv[5], argv[6], argc - 7, argv + 7);
    fprintf(control_output, "init %" PRIu64 "\n", init);
  } else if (strcmp(argv[1], "release-reuse") == 0) {
    init_runtime(&runtime, argv[2]);
    command_release_reuse(&runtime, argc - 3, argv + 3);
  } else if (strcmp(argv[1], "free-alias") == 0) {
    init_runtime(&runtime, argv[2]);
    command_free_alias(&runtime, argc - 3, argv + 3);
  } else if (strcmp(argv[1], "temp-byte-call") == 0) {
    init_runtime(&runtime, argv[2]);
    command_temp_byte_call(&runtime, argc - 3, argv + 3);
  } else if (strcmp(argv[1], "temp-array-call") == 0) {
    init_runtime(&runtime, argv[2]);
    command_temp_array_call(&runtime, argc - 3, argv + 3);
  } else if (strcmp(argv[1], "noarg-temp-reuse") == 0) {
    init_runtime(&runtime, argv[2]);
    command_noarg_temp_reuse(&runtime, argc - 3, argv + 3);
  } else if (strcmp(argv[1], "allocator-grows") == 0) {
    init_runtime(&runtime, argv[2]);
    command_allocator_grows(&runtime, argc - 3, argv + 3);
  } else if (strcmp(argv[1], "script") == 0 || strcmp(argv[1], "session") == 0) {
    init_runtime(&runtime, argv[2]);
    command_script(&runtime, argc - 3, argv + 3, strcmp(argv[1], "session") == 0);
  } else {
    usage();
  }
  finish_host(0);
}
