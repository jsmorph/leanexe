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
  wasmtime_store_t *store;
  wasmtime_context_t *context;
  wasmtime_instance_t instance;
  wasmtime_memory_t memory;
  wasmtime_func_t alloc;
  bool has_memory;
  bool has_alloc;
} Runtime;

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

static void init_runtime(Runtime *runtime, const char *wasm_path) {
  memset(runtime, 0, sizeof(*runtime));
  size_t wasm_len = 0;
  uint8_t *wasm_bytes = read_file(wasm_path, &wasm_len);

  wasm_engine_t *engine = wasm_engine_new();
  if (engine == NULL) {
    die("failed to create Wasmtime engine");
  }

  wasmtime_module_t *module = NULL;
  wasmtime_error_t *error = wasmtime_module_new(engine, wasm_bytes, wasm_len, &module);
  free(wasm_bytes);
  if (error != NULL) {
    print_error(error);
    exit(1);
  }

  runtime->store = wasmtime_store_new(engine, NULL, NULL);
  if (runtime->store == NULL) {
    die("failed to create Wasmtime store");
  }
  runtime->context = wasmtime_store_context(runtime->store);

  wasm_trap_t *trap = NULL;
  error = wasmtime_instance_new(runtime->context, module, NULL, 0, &runtime->instance, &trap);
  wasmtime_module_delete(module);
  wasm_engine_delete(engine);
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

static void usage(void) {
  fprintf(stderr,
          "usage: wasmtime-host call <module.wasm> <function> <i64|bytes|slots:N> "
          "[i64:N|bytes:HEX ...]\n");
  exit(1);
}

int main(int argc, char **argv) {
  if (argc < 5 || strcmp(argv[1], "call") != 0) {
    usage();
  }
  Runtime runtime;
  init_runtime(&runtime, argv[2]);
  call_export(&runtime, argv[3], argv[4], argc - 5, argv + 5);
  wasmtime_store_delete(runtime.store);
  return 0;
}
