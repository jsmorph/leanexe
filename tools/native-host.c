/* The host of a module translated to C, for tests/native/verified.sh.  It takes the commands
   `call` and `call-stats` of tools/wasmtime-host.c, with the same argument specs and result
   kinds, and prints the same lines, so that the corpus of tests/verified runs unchanged.  It is
   compiled with ccomp together with the module's C text and its glue (tools/native-host.h).

   `bench SECONDS MAX FUNC RESULT [ARG...]`, which tools/wasmtime-host.c also takes, calls the
   export once to warm up, and then repeatedly until SECONDS have passed or MAX timed calls have
   run.  Before each call it places the arguments again, since a call may consume them, and it
   times only the call, with CLOCK_MONOTONIC.  It prints the results of the last call as `call`
   does, then `bench N NS`, the number of timed calls and their total time in nanoseconds.

   The host calls lx_init, then the export `reset` when the module has it.  Each call of an
   export is followed by a test of lx_status: a nonzero code is a trap, which the host reports
   on standard error with Wasmtime's message for the trap and exit status 2. */

/* For clock_gettime and CLOCK_MONOTONIC. */
#define _POSIX_C_SOURCE 199309L

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "native-host.h"

typedef unsigned long long u64;

typedef struct {
  u64 *items;
  size_t len;
} U64List;

static void die(const char *message) {
  fprintf(stderr, "%s\n", message);
  exit(1);
}

static const char *trap_message(unsigned int code) {
  switch (code) {
  case 1:
    return "wasm `unreachable` instruction executed";
  case 2:
    return "wasm trap: out of bounds memory access";
  case 3:
    return "wasm trap: integer divide by zero";
  default:
    return "wasm trap: unknown code";
  }
}

static const lx_export *find_export(const char *name) {
  int i;
  for (i = 0; i < lx_export_count; i++) {
    if (strcmp(lx_exports[i].name, name) == 0) {
      return &lx_exports[i];
    }
  }
  return NULL;
}

static const lx_export *get_export(const char *name) {
  const lx_export *e = find_export(name);
  if (e == NULL) {
    fprintf(stderr, "missing export: %s\n", name);
    exit(1);
  }
  return e;
}

/* Calls `e` and exits with status 2 after a trap. */
static void invoke(const lx_export *e, const u64 *args, u64 *results) {
  lx_status = 0;
  e->call(args, results);
  if (lx_status != 0) {
    fprintf(stderr, "%s\n", trap_message(lx_status));
    exit(2);
  }
}

static size_t memory_len(void) {
  return (size_t)lx_pages * 65536;
}

static unsigned char *memory(void) {
  return (unsigned char *)lx_mem;
}

static unsigned char *read_file(const char *path, size_t *len_out) {
  FILE *file = fopen(path, "rb");
  long size;
  unsigned char *bytes;
  if (file == NULL) {
    perror(path);
    exit(1);
  }
  if (fseek(file, 0, SEEK_END) != 0) {
    perror("fseek");
    exit(1);
  }
  size = ftell(file);
  if (size < 0) {
    perror("ftell");
    exit(1);
  }
  if (fseek(file, 0, SEEK_SET) != 0) {
    perror("fseek");
    exit(1);
  }
  bytes = malloc(size == 0 ? 1 : (size_t)size);
  if (bytes == NULL) {
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

static unsigned char hex_nibble(char c) {
  if ('0' <= c && c <= '9') {
    return (unsigned char)(c - '0');
  }
  if ('a' <= c && c <= 'f') {
    return (unsigned char)(10 + c - 'a');
  }
  if ('A' <= c && c <= 'F') {
    return (unsigned char)(10 + c - 'A');
  }
  die("invalid hex byte");
  return 0;
}

static unsigned char *parse_hex(const char *text, size_t *len_out) {
  size_t text_len = strlen(text);
  size_t len, i;
  unsigned char *bytes;
  if (text_len % 2 != 0) {
    die("hex input must have an even number of digits");
  }
  len = text_len / 2;
  bytes = malloc(len == 0 ? 1 : len);
  if (bytes == NULL) {
    die("out of memory");
  }
  for (i = 0; i < len; i++) {
    bytes[i] = (unsigned char)((hex_nibble(text[i * 2]) << 4) | hex_nibble(text[i * 2 + 1]));
  }
  *len_out = len;
  return bytes;
}

static u64 parse_u64(const char *text) {
  char *end = NULL;
  u64 value = strtoull(text, &end, 10);
  if (end == NULL || end == text || *end != 0) {
    die("invalid i64 argument");
  }
  return value;
}

/* CompCert passes no structure by value, so the list is an out-parameter. */
static void parse_u64_list(const char *text, U64List *list) {
  size_t count = 1;
  const char *cursor;
  const char *start = text;
  list->items = NULL;
  list->len = 0;
  if (*text == 0) {
    return;
  }
  for (cursor = text; *cursor != 0; cursor++) {
    if (*cursor == ',') {
      count++;
    }
  }
  list->items = calloc(count, sizeof(u64));
  if (list->items == NULL) {
    die("out of memory");
  }
  for (;;) {
    const char *comma = strchr(start, ',');
    size_t len = comma == NULL ? strlen(start) : (size_t)(comma - start);
    char *part = malloc(len + 1);
    if (part == NULL) {
      die("out of memory");
    }
    memcpy(part, start, len);
    part[len] = 0;
    list->items[list->len++] = parse_u64(part);
    free(part);
    if (comma == NULL) {
      break;
    }
    start = comma + 1;
  }
}

static void check_range(u64 ptr, u64 len, const char *message) {
  size_t mlen = memory_len();
  if (ptr > mlen || len > mlen - (size_t)ptr) {
    die(message);
  }
}

static void write_u64_at(u64 ptr, u64 value) {
  size_t i;
  check_range(ptr, 8, "u64 write is outside memory");
  for (i = 0; i < 8; i++) {
    memory()[ptr + i] = (unsigned char)(value >> (i * 8));
  }
}

static u64 read_u64_at(u64 ptr) {
  u64 value = 0;
  size_t i;
  check_range(ptr, 8, "u64 read is outside memory");
  for (i = 0; i < 8; i++) {
    value |= (u64)memory()[ptr + i] << (i * 8);
  }
  return value;
}

static u64 call_alloc(u64 len) {
  const lx_export *alloc = find_export("alloc");
  u64 args[1];
  u64 results[1];
  if (alloc == NULL) {
    die("missing alloc export");
  }
  args[0] = len;
  invoke(alloc, args, results);
  return results[0];
}

static u64 alloc_bytes(const unsigned char *bytes, size_t len) {
  u64 ptr = call_alloc((u64)len);
  check_range(ptr, len, "allocation is outside memory");
  memcpy(memory() + ptr, bytes, len);
  return ptr;
}

static u64 alloc_u64_array(const U64List *values) {
  u64 ptr = call_alloc(8 + values->len * 8);
  size_t i;
  write_u64_at(ptr, values->len);
  for (i = 0; i < values->len; i++) {
    write_u64_at(ptr + 8 + i * 8, values->items[i]);
  }
  return ptr;
}

/* The list `values` as a chain of records of two slots, as tools/wasmtime-host.c allocates it. */
static u64 alloc_u64_chain(const U64List *values) {
  u64 ptr = 0;
  size_t i;
  for (i = values->len; i > 0; i--) {
    u64 cell = call_alloc(16);
    write_u64_at(cell - 24, 1);
    write_u64_at(cell - 16, 2);
    write_u64_at(cell - 8, 2);
    write_u64_at(cell, values->items[i - 1]);
    write_u64_at(cell + 8, ptr);
    ptr = cell;
  }
  return ptr;
}

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

/* The tree of the preorder description at `*text`, as tools/wasmtime-host.c allocates it. */
static u64 alloc_u64_tree(const char **text) {
  char token[32];
  u64 key, left, right, cell;
  read_token(text, token, sizeof token);
  if (strcmp(token, ".") == 0) {
    return 0;
  }
  key = parse_u64(token);
  left = alloc_u64_tree(text);
  right = alloc_u64_tree(text);
  cell = call_alloc(24);
  write_u64_at(cell - 24, 1);
  write_u64_at(cell - 16, 3);
  write_u64_at(cell - 8, 5);
  write_u64_at(cell, left);
  write_u64_at(cell + 8, key);
  write_u64_at(cell + 16, right);
  return cell;
}

static int record_header_valid(u64 width, u64 mask) {
  return width >= 1 && width <= 64 && (width == 64 || mask >> width == 0);
}

/* The tree of records of the preorder description at `*text`, as tools/wasmtime-host.c
   allocates it. */
static u64 alloc_records(const char **text) {
  char token[32];
  u64 width, mask, i, cell;
  u64 slots[64];
  read_token(text, token, sizeof token);
  if (strcmp(token, ".") == 0) {
    return 0;
  }
  width = parse_u64(token);
  read_token(text, token, sizeof token);
  mask = parse_u64(token);
  if (!record_header_valid(width, mask)) {
    die("bad record header in tree description");
  }
  for (i = 0; i < width; i++) {
    if ((mask >> i) & 1) {
      slots[i] = alloc_records(text);
    } else {
      read_token(text, token, sizeof token);
      slots[i] = parse_u64(token);
    }
  }
  cell = call_alloc(8 * width);
  write_u64_at(cell - 24, 1);
  write_u64_at(cell - 16, width);
  write_u64_at(cell - 8, mask);
  for (i = 0; i < width; i++) {
    write_u64_at(cell + 8 * i, slots[i]);
  }
  return cell;
}

#define OBJECT_MAGIC 5501223100278326855ULL

static void print_u64_chain(u64 ptr) {
  u64 k;
  printf("[");
  for (k = 0; ptr != 0; k++) {
    if (k > memory_len() / 16) {
      die("list result does not end");
    }
    if (ptr < 48 || read_u64_at(ptr - 48) != OBJECT_MAGIC || read_u64_at(ptr - 40) != 1 ||
        read_u64_at(ptr - 24) != 1 || read_u64_at(ptr - 16) != 2 || read_u64_at(ptr - 8) != 2) {
      die("list result has a wrong record header");
    }
    if (k != 0) {
      printf(", ");
    }
    printf("%llu", read_u64_at(ptr));
    ptr = read_u64_at(ptr + 8);
  }
  printf("]\n");
}

static void print_u64_tree_at(u64 ptr, u64 *count) {
  if (ptr == 0) {
    printf(".");
    return;
  }
  if (++*count > memory_len() / 72) {
    die("tree result does not end");
  }
  if (ptr < 48 || read_u64_at(ptr - 48) != OBJECT_MAGIC || read_u64_at(ptr - 40) != 1 ||
      read_u64_at(ptr - 24) != 1 || read_u64_at(ptr - 16) != 3 || read_u64_at(ptr - 8) != 5) {
    die("tree result has a wrong record header");
  }
  printf("%llu,", read_u64_at(ptr + 8));
  print_u64_tree_at(read_u64_at(ptr), count);
  printf(",");
  print_u64_tree_at(read_u64_at(ptr + 16), count);
}

static void print_u64_tree(u64 ptr) {
  u64 count = 0;
  print_u64_tree_at(ptr, &count);
  printf("\n");
}

static void print_records_at(u64 ptr, u64 *count) {
  u64 width, mask, i;
  if (ptr == 0) {
    printf(".");
    return;
  }
  if (++*count > memory_len() / 56) {
    die("tree result does not end");
  }
  if (ptr < 48 || read_u64_at(ptr - 48) != OBJECT_MAGIC || read_u64_at(ptr - 40) != 1 ||
      read_u64_at(ptr - 24) != 1) {
    die("tree result has a wrong record header");
  }
  width = read_u64_at(ptr - 16);
  mask = read_u64_at(ptr - 8);
  if (!record_header_valid(width, mask)) {
    die("tree result has a wrong record header");
  }
  printf("%llu,%llu", width, mask);
  for (i = 0; i < width; i++) {
    u64 slot = read_u64_at(ptr + 8 * i);
    printf(",");
    if ((mask >> i) & 1) {
      print_records_at(slot, count);
    } else {
      printf("%llu", slot);
    }
  }
}

static void print_records(u64 ptr) {
  u64 count = 0;
  print_records_at(ptr, &count);
  printf("\n");
}

static void print_u64_array(u64 ptr) {
  u64 len = read_u64_at(ptr);
  u64 i;
  if (len > ((u64)-1 - 8) / 8) {
    die("Array UInt64 result length is too large");
  }
  check_range(ptr, 8 + len * 8, "Array UInt64 result is outside memory");
  printf("[");
  for (i = 0; i < len; i++) {
    if (i != 0) {
      printf(", ");
    }
    printf("%llu", read_u64_at(ptr + 8 + i * 8));
  }
  printf("]\n");
}

/* Writes the elements of the array at `ptr`, as little-endian words, to the file at `path`. */
static void save_u64_array(u64 ptr, const char *path) {
  u64 len = read_u64_at(ptr);
  FILE *file;
  if (len > ((u64)-1 - 8) / 8) {
    die("Array UInt64 result length is too large");
  }
  check_range(ptr, 8 + len * 8, "Array UInt64 result is outside memory");
  file = fopen(path, "wb");
  if (file == NULL) {
    perror(path);
    exit(1);
  }
  if (len != 0 && fwrite(memory() + ptr + 8, 8, (size_t)len, file) != (size_t)len) {
    perror("fwrite");
    exit(1);
  }
  if (fclose(file) != 0) {
    perror("fclose");
    exit(1);
  }
}

static u64 alloc_u64_file(const char *path) {
  size_t len = 0;
  unsigned char *bytes = read_file(path, &len);
  u64 ptr;
  if (len % 8 != 0) {
    die("file-u64 file length is not a multiple of 8");
  }
  ptr = call_alloc(8 + (u64)len);
  write_u64_at(ptr, len / 8);
  check_range(ptr + 8, len, "allocation is outside memory");
  memcpy(memory() + ptr + 8, bytes, len);
  free(bytes);
  return ptr;
}

/* Parses the argument spec `spec` into `out`, the bits of each value, and returns the number
   of values, or 0 for an unknown spec. */
static size_t parse_arg(const char *spec, u64 *out) {
  if (strncmp(spec, "i64:", 4) == 0 || strncmp(spec, "f64:", 4) == 0) {
    out[0] = parse_u64(spec + 4);
    return 1;
  }
  if (strncmp(spec, "f32:", 4) == 0) {
    out[0] = parse_u64(spec + 4);
    if (out[0] > 0xFFFFFFFFULL) {
      die("f32 bits exceed 32 bits");
    }
    return 1;
  }
  if (strncmp(spec, "bytes:", 6) == 0 || strncmp(spec, "bytes-file:", 11) == 0) {
    size_t len = 0;
    unsigned char *bytes =
        spec[5] == ':' ? parse_hex(spec + 6, &len) : read_file(spec + 11, &len);
    out[0] = alloc_bytes(bytes, len);
    out[1] = (u64)len;
    free(bytes);
    return 2;
  }
  if (strncmp(spec, "file-u64:", 9) == 0) {
    out[0] = alloc_u64_file(spec + 9);
    return 1;
  }
  if (strncmp(spec, "array-u64:", 10) == 0) {
    U64List values;
    parse_u64_list(spec + 10, &values);
    out[0] = alloc_u64_array(&values);
    free(values.items);
    return 1;
  }
  if (strncmp(spec, "tree-u64:", 9) == 0) {
    const char *text = spec + 9;
    out[0] = alloc_u64_tree(&text);
    if (*text != 0) {
      die("bad tree description");
    }
    return 1;
  }
  if (strncmp(spec, "records-u64:", 12) == 0) {
    const char *text = spec + 12;
    out[0] = alloc_records(&text);
    if (*text != 0) {
      die("bad tree description");
    }
    return 1;
  }
  if (strncmp(spec, "chain-u64:", 10) == 0) {
    U64List values;
    parse_u64_list(spec + 10, &values);
    out[0] = alloc_u64_chain(&values);
    free(values.items);
    return 1;
  }
  return 0;
}

/* The kind of result `index` in a `list:K1,K2,...` result spec, copied into `out`. */
static void list_result_kind(const char *kind, size_t index, char *out, size_t out_len) {
  const char *start = kind + 5;
  const char *end;
  size_t i, len;
  for (i = 0; i < index; i++) {
    start = strchr(start, ',');
    if (start == NULL) {
      die("result list is too short");
    }
    start++;
  }
  end = strchr(start, ',');
  len = end == NULL ? strlen(start) : (size_t)(end - start);
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
    size_t items = 1, count = 0, i;
    const char *c;
    for (c = kind + 5; *c != 0; c++) {
      if (*c == ',') {
        items++;
      }
    }
    if (items > 128) {
      die("too many results");
    }
    /* A `bytes` item is two results, the address and the length. */
    for (i = 0; i < items; i++) {
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
    u64 count = parse_u64(kind + 6);
    if (count > 128) {
      die("too many result slots");
    }
    return (size_t)count;
  }
  die("unknown result kind");
  return 0;
}

static void print_bytes(u64 ptr, u64 len) {
  u64 i;
  check_range(ptr, len, "ByteArray result is outside memory");
  for (i = 0; i < len; i++) {
    printf("%02x", memory()[ptr + i]);
  }
  printf("\n");
}

static void print_result(const char *kind, u64 value) {
  if (strcmp(kind, "f64") == 0 || strcmp(kind, "i64") == 0 || strcmp(kind, "f32") == 0) {
    printf("%llu\n", value);
  } else if (strcmp(kind, "array-u64") == 0) {
    print_u64_array(value);
  } else if (strcmp(kind, "chain-u64") == 0) {
    print_u64_chain(value);
  } else if (strcmp(kind, "tree-u64") == 0) {
    print_u64_tree(value);
  } else if (strcmp(kind, "records-u64") == 0) {
    print_records(value);
  } else {
    die("unknown result kind in list");
  }
}

/* Places the arguments `argv` of a call of `e` into `args` and returns the number of results
   that `result_kind` describes, after checking both against the type of `e`. */
static size_t place_args(const lx_export *e, const char *func_name, const char *result_kind,
                         int argc, char **argv, u64 *args) {
  size_t nargs = 0, nresults;
  int j;
  for (j = 0; j < argc; j++) {
    size_t count;
    if (nargs + 2 > 256) {
      die("too many arguments");
    }
    count = parse_arg(argv[j], &args[nargs]);
    if (count == 0) {
      fprintf(stderr, "unknown argument spec: %s\n", argv[j]);
      exit(1);
    }
    nargs += count;
  }
  nresults = result_count_from_kind(result_kind);
  if (nargs != strlen(e->params) || nresults != strlen(e->results)) {
    fprintf(stderr, "the call of %s does not match its type\n", func_name);
    exit(1);
  }
  return nresults;
}

/* Prints the results of a call as `result_kind` describes them. */
static void print_results(const char *result_kind, const u64 *results, size_t nresults) {
  size_t i;
  if (strncmp(result_kind, "list:", 5) == 0) {
    size_t item = 0;
    for (i = 0; i < nresults; i++, item++) {
      char kind[32];
      list_result_kind(result_kind, item, kind, sizeof kind);
      if (strcmp(kind, "bytes") == 0) {
        print_bytes(results[i], results[i + 1]);
        i++;
      } else {
        print_result(kind, results[i]);
      }
    }
    return;
  }
  if (strcmp(result_kind, "bytes") == 0) {
    print_bytes(results[0], results[1]);
    return;
  }
  if (strcmp(result_kind, "array-u64") == 0 || strcmp(result_kind, "chain-u64") == 0 ||
      strcmp(result_kind, "tree-u64") == 0 || strcmp(result_kind, "records-u64") == 0 ||
      strcmp(result_kind, "f64") == 0 || strcmp(result_kind, "f32") == 0) {
    print_result(result_kind, results[0]);
    return;
  }
  if (strncmp(result_kind, "file-u64:", 9) == 0) {
    save_u64_array(results[0], result_kind + 9);
    return;
  }
  for (i = 0; i < nresults; i++) {
    if (i != 0) {
      printf(" ");
    }
    printf("%llu", results[i]);
  }
  printf("\n");
}

static void call_export(const char *func_name, const char *result_kind, int argc, char **argv) {
  const lx_export *e = get_export(func_name);
  u64 args[256];
  u64 results[128];
  size_t nresults = place_args(e, func_name, result_kind, argc, argv, args);
  invoke(e, args, results);
  print_results(result_kind, results, nresults);
}

static u64 now_ns(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return (u64)t.tv_sec * 1000000000ULL + (u64)t.tv_nsec;
}

static void bench_export(const char *seconds, const char *max, const char *func_name,
                         const char *result_kind, int argc, char **argv) {
  const lx_export *e = get_export(func_name);
  u64 args[256];
  u64 results[128];
  u64 limit = (u64)(atof(seconds) * 1e9), most = parse_u64(max);
  u64 start, count = 0, total = 0, before, after;
  size_t nresults = place_args(e, func_name, result_kind, argc, argv, args);
  invoke(e, args, results);
  start = now_ns();
  while (count < most && now_ns() - start < limit) {
    place_args(e, func_name, result_kind, argc, argv, args);
    before = now_ns();
    invoke(e, args, results);
    after = now_ns();
    total += after - before;
    count++;
  }
  print_results(result_kind, results, nresults);
  printf("bench %llu %llu\n", count, total);
}

static u64 read_global(const char *name) {
  int i;
  for (i = 0; i < lx_global_export_count; i++) {
    if (strcmp(lx_global_exports[i].name, name) == 0) {
      return *lx_global_exports[i].value;
    }
  }
  fprintf(stderr, "missing export: %s\n", name);
  exit(1);
  return 0;
}

static void usage(void) {
  fprintf(stderr, "usage: HOST call|call-stats FUNC RESULT [ARG...]\n"
                  "       HOST bench SECONDS MAX FUNC RESULT [ARG...]\n");
  exit(2);
}

int main(int argc, char **argv) {
  const lx_export *reset;
  int bench = argc >= 2 && strcmp(argv[1], "bench") == 0;
  if (bench ? argc < 6
            : argc < 4 || (strcmp(argv[1], "call") != 0 && strcmp(argv[1], "call-stats") != 0)) {
    usage();
  }
  lx_status = 0;
  lx_init();
  if (lx_status != 0) {
    die("lx_init failed");
  }
  reset = find_export("reset");
  if (reset != NULL) {
    invoke(reset, NULL, NULL);
  }
  if (bench) {
    bench_export(argv[2], argv[3], argv[4], argv[5], argc - 6, argv + 6);
    return 0;
  }
  call_export(argv[2], argv[3], argc - 4, argv + 4);
  if (strcmp(argv[1], "call-stats") == 0) {
    printf("stats %llu %llu\n", read_global("allocCount"), read_global("freeCount"));
  }
  return 0;
}
