#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <wasm.h>
#include <wasmtime.h>

typedef struct {
  wasm_engine_t *engine;
  wasmtime_store_t *store;
  wasmtime_context_t *context;
  wasmtime_instance_t instance;
  wasmtime_memory_t memory;
  wasmtime_func_t alloc;
  bool has_memory;
  bool has_alloc;
} Runtime;

typedef struct {
  uint64_t *items;
  size_t len;
} U64List;

static void die(const char *message) {
  fprintf(stderr, "%s\n", message);
  exit(1);
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

static uint8_t *read_file(const char *path, size_t *len_out) {
  FILE *file = fopen(path, "rb");
  if (file == NULL) {
    perror(path);
    exit(1);
  }
  if (fseek(file, 0, SEEK_END) != 0) {
    perror("fseek");
    exit(1);
  }
  long size = ftell(file);
  if (size < 0) {
    perror("ftell");
    exit(1);
  }
  if (fseek(file, 0, SEEK_SET) != 0) {
    perror("fseek");
    exit(1);
  }
  uint8_t *bytes = malloc((size_t)size);
  if (bytes == NULL && size != 0) {
    die("out of memory");
  }
  if (size != 0 && fread(bytes, 1, (size_t)size, file) != (size_t)size) {
    perror("fread");
    exit(1);
  }
  fclose(file);
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

static void init_runtime(Runtime *runtime, const char *wasm_path) {
  memset(runtime, 0, sizeof(*runtime));
  size_t wasm_len = 0;
  uint8_t *wasm_bytes = read_file(wasm_path, &wasm_len);

  runtime->engine = wasm_engine_new();
  if (runtime->engine == NULL) {
    die("failed to create Wasmtime engine");
  }

  wasmtime_module_t *module = NULL;
  wasmtime_error_t *error = wasmtime_module_new(runtime->engine, wasm_bytes, wasm_len, &module);
  free(wasm_bytes);
  if (error != NULL) {
    print_error(error);
    exit(1);
  }

  runtime->store = wasmtime_store_new(runtime->engine, NULL, NULL);
  if (runtime->store == NULL) {
    die("failed to create Wasmtime store");
  }
  runtime->context = wasmtime_store_context(runtime->store);

  wasm_trap_t *trap = NULL;
  error = wasmtime_instance_new(runtime->context, module, NULL, 0, &runtime->instance, &trap);
  wasmtime_module_delete(module);
  if (error != NULL) {
    print_error(error);
    exit(1);
  }
  if (trap != NULL) {
    print_trap(trap);
    exit(1);
  }

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
  if (wasmtime_instance_export_get(runtime->context, &runtime->instance, "reset", 5, &item)) {
    if (item.kind != WASMTIME_EXTERN_FUNC) {
      die("export reset is not a function");
    }
    wasmtime_val_t args[1];
    wasmtime_val_t results[1];
    trap = NULL;
    error = wasmtime_func_call(runtime->context, &item.of.func, args, 0, results, 0, &trap);
    if (error != NULL) {
      print_error(error);
      exit(1);
    }
    if (trap != NULL) {
      print_trap(trap);
      exit(1);
    }
  }
}

static wasmtime_func_t get_func(Runtime *runtime, const char *name) {
  wasmtime_extern_t item;
  if (!wasmtime_instance_export_get(runtime->context, &runtime->instance, name, strlen(name), &item)) {
    fprintf(stderr, "missing export: %s\n", name);
    exit(1);
  }
  if (item.kind != WASMTIME_EXTERN_FUNC) {
    fprintf(stderr, "export is not a function: %s\n", name);
    exit(1);
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
  wasm_trap_t *trap = NULL;
  wasmtime_error_t *error = wasmtime_func_call(runtime->context, func, args, 1, results, 1, &trap);
  if (error != NULL) {
    print_error(error);
    exit(1);
  }
  if (trap != NULL) {
    print_trap(trap);
    exit(1);
  }
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
  wasm_trap_t *trap = NULL;
  wasmtime_error_t *error = wasmtime_func_call(runtime->context, func, args, 1, results, 0, &trap);
  if (error != NULL) {
    print_error(error);
    exit(1);
  }
  if (trap != NULL) {
    print_trap(trap);
    exit(1);
  }
}

static void call_void_func(Runtime *runtime, wasmtime_func_t *func) {
  wasmtime_val_t args[1];
  wasmtime_val_t results[1];
  memset(args, 0, sizeof(args));
  memset(results, 0, sizeof(results));
  wasm_trap_t *trap = NULL;
  wasmtime_error_t *error = wasmtime_func_call(runtime->context, func, args, 0, results, 0, &trap);
  if (error != NULL) {
    print_error(error);
    exit(1);
  }
  if (trap != NULL) {
    print_trap(trap);
    exit(1);
  }
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

static bool parse_arg(Runtime *runtime, const char *spec, wasmtime_val_t *out, size_t *out_count) {
  if (strncmp(spec, "i64:", 4) == 0) {
    out[0].kind = WASMTIME_I64;
    out[0].of.i64 = (int64_t)parse_u64(spec + 4);
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
  if (strncmp(spec, "array-u64:", 10) == 0) {
    U64List values = parse_u64_list(spec + 10);
    uint64_t ptr = alloc_u64_array(runtime, values);
    free_u64_list(values);
    out[0].kind = WASMTIME_I64;
    out[0].of.i64 = (int64_t)ptr;
    *out_count = 1;
    return true;
  }
  return false;
}

static size_t result_count_from_kind(const char *kind) {
  if (strcmp(kind, "i64") == 0) {
    return 1;
  }
  if (strcmp(kind, "bytes") == 0) {
    return 2;
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

static void call_export(Runtime *runtime, const char *func_name, const char *result_kind,
                        int argc, char **argv) {
  wasmtime_func_t func = get_func(runtime, func_name);
  wasmtime_val_t args[256];
  size_t nargs = 0;
  for (int i = 0; i < argc; i++) {
    size_t count = 0;
    if (!parse_arg(runtime, argv[i], &args[nargs], &count)) {
      fprintf(stderr, "unknown argument spec: %s\n", argv[i]);
      exit(1);
    }
    nargs += count;
    if (nargs > 256) {
      die("too many arguments");
    }
  }

  size_t nresults = result_count_from_kind(result_kind);
  wasmtime_val_t results[128];
  for (size_t i = 0; i < nresults; i++) {
    results[i].kind = WASMTIME_I64;
  }
  wasm_trap_t *trap = NULL;
  wasmtime_error_t *error =
      wasmtime_func_call(runtime->context, &func, args, nargs, results, nresults, &trap);
  if (error != NULL) {
    print_error(error);
    exit(1);
  }
  if (trap != NULL) {
    print_trap(trap);
    exit(2);
  }

  if (strcmp(result_kind, "bytes") == 0) {
    if (!runtime->has_memory) {
      die("ByteArray result requires exported memory");
    }
    uint64_t ptr = (uint64_t)results[0].of.i64;
    uint64_t len = (uint64_t)results[1].of.i64;
    size_t memory_len = wasmtime_memory_data_size(runtime->context, &runtime->memory);
    if (ptr > memory_len || len > memory_len - (size_t)ptr) {
      die("ByteArray result is outside memory");
    }
    uint8_t *memory = wasmtime_memory_data(runtime->context, &runtime->memory);
    for (uint64_t i = 0; i < len; i++) {
      printf("%02x", memory[ptr + i]);
    }
    printf("\n");
    return;
  }

  for (size_t i = 0; i < nresults; i++) {
    if (results[i].kind != WASMTIME_I64) {
      die("expected i64 result");
    }
    if (i != 0) {
      printf(" ");
    }
    printf("%" PRIu64, (uint64_t)results[i].of.i64);
  }
  printf("\n");
}

static void invoke_func(Runtime *runtime, wasmtime_func_t *func, wasmtime_val_t *args,
                        size_t nargs, wasmtime_val_t *results, size_t nresults) {
  for (size_t i = 0; i < nresults; i++) {
    results[i].kind = WASMTIME_I64;
  }
  wasm_trap_t *trap = NULL;
  wasmtime_error_t *error =
      wasmtime_func_call(runtime->context, func, args, nargs, results, nresults, &trap);
  if (error != NULL) {
    print_error(error);
    exit(1);
  }
  if (trap != NULL) {
    print_trap(trap);
    exit(2);
  }
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
    exit(1);
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
      exit(1);
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

static void command_retain_delay(Runtime *runtime, int argc, char **argv) {
  if (argc != 4) {
    die("usage: retain-delay <module.wasm> <function> <nresults> <ptr-index> <alloc-size>");
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
  wasmtime_func_t retain = required_runtime_func(runtime, "retain");
  wasmtime_func_t release = required_runtime_func(runtime, "release");
  (void)call_i64_func(runtime, &retain, ptr);
  call_void_i64_func(runtime, &release, ptr);
  uint64_t after_one = call_alloc(runtime, alloc_size);
  if (after_one == ptr) {
    die("retain did not preserve the block after one release");
  }
  call_void_i64_func(runtime, &release, ptr);
  uint64_t after_two = call_alloc(runtime, alloc_size);
  expect_eq_u64("second release reuse", ptr, after_two);
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

static void usage(void) {
  fprintf(stderr,
          "usage: wasmtime-host call <module.wasm> <function> <i64|bytes|slots:N> "
          "[i64:N|bytes:HEX|array-u64:N,N ...]\n");
  exit(1);
}

int main(int argc, char **argv) {
  if (argc < 3) {
    usage();
  }
  Runtime runtime;
  if (strcmp(argv[1], "call") == 0) {
    if (argc < 5) {
      usage();
    }
    init_runtime(&runtime, argv[2]);
    call_export(&runtime, argv[3], argv[4], argc - 5, argv + 5);
  } else if (strcmp(argv[1], "release-reuse") == 0) {
    init_runtime(&runtime, argv[2]);
    command_release_reuse(&runtime, argc - 3, argv + 3);
  } else if (strcmp(argv[1], "retain-delay") == 0) {
    init_runtime(&runtime, argv[2]);
    command_retain_delay(&runtime, argc - 3, argv + 3);
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
  } else {
    usage();
  }
  wasmtime_store_delete(runtime.store);
  wasm_engine_delete(runtime.engine);
  return 0;
}
