#define _POSIX_C_SOURCE 200809L
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <poll.h>
#include <signal.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <wasm.h>
#include <wasmtime.h>
#include <wasi.h>

enum { AGAIN = 6, BADF = 8, FAULT = 21, INTR = 27, INVAL = 28, IOERR = 29,
       NOTSUP = 58, PIPE = 64 };
enum Operation { READ, WRITE, FLAGS, CLOCK, POLL };
static int original_flags[2] = {-1, -1};
static bool changed_flags[2] = {false, false};

static uint64_t load_le(const uint8_t *p, unsigned n) {
  uint64_t value = 0;
  for (unsigned i = 0; i < n; ++i) value |= (uint64_t)p[i] << (8 * i);
  return value;
}

static void store_le(uint8_t *p, uint64_t value, unsigned n) {
  for (unsigned i = 0; i < n; ++i) p[i] = (uint8_t)(value >> (8 * i));
}

static bool in_bounds(size_t size, uint64_t ptr, uint64_t len) {
  return ptr <= size && len <= size - ptr;
}

static uint32_t io_error(void) {
  switch (errno) {
    case EAGAIN: return AGAIN;
    case EBADF: return BADF;
    case EINTR: return INTR;
    case EINVAL: return INVAL;
    case EPIPE: return PIPE;
    default: return IOERR;
  }
}

static uint64_t monotonic_ns(void) {
  struct timespec now;
  if (clock_gettime(CLOCK_MONOTONIC, &now) != 0) { perror("clock_gettime"); exit(1); }
  return (uint64_t)now.tv_sec * UINT64_C(1000000000) + (uint64_t)now.tv_nsec;
}

static uint32_t poll_events(uint8_t *mem, size_t size, uint32_t input,
                            uint32_t output, uint32_t count, uint32_t result) {
  if (count == 0 || count > 2) return INVAL;
  if (!in_bounds(size, input, 48 * count) || !in_bounds(size, output, 32 * count) ||
      !in_bounds(size, result, 4)) return FAULT;
  struct pollfd fds[2] = {{.fd = -1}, {.fd = -1}};
  uint8_t subscriptions[96];
  memcpy(subscriptions, mem + input, 48 * count);
  uint64_t deadlines[2] = {UINT64_MAX, UINT64_MAX};
  uint64_t now = monotonic_ns();
  bool have_clock = false;
  for (uint32_t i = 0; i < count; ++i) {
    const uint8_t *sub = subscriptions + 48 * i;
    if (sub[8] == 0) {
      uint64_t flags = load_le(sub + 40, 2);
      if (load_le(sub + 16, 4) != 1 || flags > 1) return INVAL;
      uint64_t timeout = load_le(sub + 24, 8);
      deadlines[i] = flags == 1 ? timeout :
        (timeout > UINT64_MAX - now ? UINT64_MAX : now + timeout);
      have_clock = true;
    } else if (sub[8] == 1 || sub[8] == 2) {
      uint32_t fd = (uint32_t)load_le(sub + 16, 4);
      if (fd != (uint32_t)(sub[8] - 1)) return BADF;
      fds[i].fd = (int)fd;
      fds[i].events = sub[8] == 1 ? POLLIN : POLLOUT;
    } else return INVAL;
  }
  for (;;) {
    now = monotonic_ns();
    uint64_t deadline = deadlines[0] < deadlines[1] ? deadlines[0] : deadlines[1];
    uint64_t remaining = deadline > now ? deadline - now : 0;
    uint64_t millis = remaining / 1000000 + (remaining % 1000000 != 0);
    int wait_ms = have_clock ? (millis > INT_MAX ? INT_MAX : (int)millis) : -1;
    int ready = poll(fds, count, wait_ms);
    if (ready < 0) {
      if (errno == EINTR) continue;
      return io_error();
    }
    now = monotonic_ns();
    uint32_t emitted = 0;
    for (uint32_t i = 0; i < count; ++i) {
      const uint8_t *sub = subscriptions + 48 * i;
      bool clock_ready = sub[8] == 0 && now >= deadlines[i];
      if (!clock_ready && fds[i].revents == 0) continue;
      uint8_t *event = mem + output + 32 * emitted++;
      memset(event, 0, 32);
      memcpy(event, sub, 8);
      store_le(event + 8, (fds[i].revents & POLLNVAL) ? BADF : 0, 2);
      event[10] = sub[8];
      if (sub[8] != 0) {
        store_le(event + 16, 1, 8);
        store_le(event + 24, (fds[i].revents & POLLHUP) ? 1 : 0, 2);
      }
    }
    if (emitted != 0) { store_le(mem + result, emitted, 4); return 0; }
  }
}

static wasm_trap_t *hostcall(void *data, wasmtime_caller_t *caller,
                            const wasmtime_val_t *args, size_t nargs,
                            wasmtime_val_t *results, size_t nresults) {
  (void)nargs; (void)nresults;
  enum Operation op = (enum Operation)(uintptr_t)data;
  uint32_t error = 0;
  wasmtime_extern_t memory;
  wasmtime_context_t *context = wasmtime_caller_context(caller);
  if (!wasmtime_caller_export_get(caller, "memory", 6, &memory) ||
      memory.kind != WASMTIME_EXTERN_MEMORY) {
    error = FAULT;
    goto done;
  }
  uint8_t *mem = wasmtime_memory_data(context, &memory.of.memory);
  size_t size = wasmtime_memory_data_size(context, &memory.of.memory);
  uint32_t a = (uint32_t)args[0].of.i32;
  uint32_t b = op == CLOCK ? 0 : (uint32_t)args[1].of.i32;
  if (op == FLAGS) {
    if (a > 1 || original_flags[a] < 0) error = BADF;
    else if (b != 4) error = NOTSUP;
    else {
      int flags = fcntl((int)a, F_GETFL);
      if (flags < 0) error = io_error();
      else if (fcntl((int)a, F_SETFL, flags | O_NONBLOCK) < 0) error = io_error();
      else changed_flags[a] = true;
    }
  } else if (op == CLOCK) {
    uint32_t out = (uint32_t)args[2].of.i32;
    if (a != 1) error = INVAL;
    else if (!in_bounds(size, out, 8)) error = FAULT;
    else store_le(mem + out, monotonic_ns(), 8);
  } else if (op == POLL) {
    error = poll_events(mem, size, a, b, (uint32_t)args[2].of.i32,
                        (uint32_t)args[3].of.i32);
  } else {
    uint32_t count = (uint32_t)args[2].of.i32;
    uint32_t out = (uint32_t)args[3].of.i32;
    if (a != (op == READ ? 0u : 1u)) error = BADF;
    else if (count != 1) error = INVAL;
    else if (!in_bounds(size, b, 8) || !in_bounds(size, out, 4)) error = FAULT;
    else {
      uint32_t ptr = (uint32_t)load_le(mem + b, 4);
      uint32_t len = (uint32_t)load_le(mem + b + 4, 4);
      if (!in_bounds(size, ptr, len)) error = FAULT;
      else {
        ssize_t n = op == READ ? read((int)a, mem + ptr, len) : write((int)a, mem + ptr, len);
        if (n < 0) error = io_error();
        else store_le(mem + out, (uint64_t)n, 4);
      }
    }
  }
done:
  results[0].kind = WASMTIME_I32;
  results[0].of.i32 = (int32_t)error;
  return NULL;
}

static void check(wasmtime_error_t *error) {
  if (error == NULL) return;
  wasm_name_t message;
  wasmtime_error_message(error, &message);
  fprintf(stderr, "%.*s\n", (int)message.size, message.data);
  wasm_byte_vec_delete(&message);
  wasmtime_error_delete(error);
  exit(1);
}

static void restore_flags(void) {
  for (int fd = 0; fd < 2; ++fd)
    if (changed_flags[fd] && fcntl(fd, F_SETFL, original_flags[fd]) < 0) {
      perror("restore descriptor flags");
      _Exit(1);
    }
}

static void define(wasmtime_linker_t *linker, const char *name, enum Operation op,
                   size_t arity) {
  wasm_valtype_vec_t params, results;
  wasm_valtype_vec_new_uninitialized(&params, arity);
  for (size_t i = 0; i < arity; ++i)
    params.data[i] = op == CLOCK && i == 1 ? wasm_valtype_new_i64() : wasm_valtype_new_i32();
  wasm_valtype_vec_new_uninitialized(&results, 1);
  results.data[0] = wasm_valtype_new_i32();
  wasm_functype_t *type = wasm_functype_new(&params, &results);
  check(wasmtime_linker_define_func(linker, "wasi_snapshot_preview1", 22,
    name, strlen(name), type, hostcall, (void *)(uintptr_t)op, NULL));
  wasm_functype_delete(type);
}

int main(int argc, char **argv) {
  if (argc != 2) { fprintf(stderr, "usage: leanexe-wasi-io-host program.wasm\n"); return 2; }
  /* Snapshot both streams before changing either: dup'd descriptors share
     status flags, so a later per-descriptor snapshot can already be altered. */
  for (int fd = 0; fd < 2; ++fd) original_flags[fd] = fcntl(fd, F_GETFL);
  signal(SIGPIPE, SIG_IGN);
  atexit(restore_flags);
  FILE *file = fopen(argv[1], "rb");
  if (!file) { perror(argv[1]); return 1; }
  if (fseek(file, 0, SEEK_END) != 0) return 1;
  long length = ftell(file);
  if (length < 0 || fseek(file, 0, SEEK_SET) != 0) return 1;
  uint8_t *bytes = malloc(length == 0 ? 1 : (size_t)length);
  if (!bytes || fread(bytes, 1, (size_t)length, file) != (size_t)length) return 1;
  fclose(file);
  wasm_config_t *config = wasm_config_new();
  if (!config) { fprintf(stderr, "failed to create Wasmtime configuration\n"); return 1; }
  wasmtime_config_strategy_set(config, WASMTIME_STRATEGY_CRANELIFT);
  wasmtime_config_cranelift_nan_canonicalization_set(config, true);
  wasm_engine_t *engine = wasm_engine_new_with_config(config);
  if (!engine) { fprintf(stderr, "failed to create Wasmtime engine\n"); return 1; }
  wasmtime_store_t *store = wasmtime_store_new(engine, NULL, NULL);
  wasmtime_context_t *context = wasmtime_store_context(store);
  wasi_config_t *wasi = wasi_config_new();
  check(wasmtime_context_set_wasi(context, wasi));
  wasmtime_linker_t *linker = wasmtime_linker_new(engine);
  check(wasmtime_linker_define_wasi(linker));
  wasmtime_linker_allow_shadowing(linker, true);
  define(linker, "fd_read", READ, 4);
  define(linker, "fd_write", WRITE, 4);
  define(linker, "fd_fdstat_set_flags", FLAGS, 2);
  define(linker, "clock_time_get", CLOCK, 3);
  define(linker, "poll_oneoff", POLL, 4);
  wasmtime_module_t *module = NULL;
  check(wasmtime_module_new(engine, bytes, (size_t)length, &module));
  free(bytes);
  wasmtime_instance_t instance;
  wasm_trap_t *trap = NULL;
  check(wasmtime_linker_instantiate(linker, context, module, &instance, &trap));
  wasmtime_extern_t start;
  if (!trap && (!wasmtime_instance_export_get(context, &instance, "_start", 6, &start) ||
      start.kind != WASMTIME_EXTERN_FUNC)) { fprintf(stderr, "missing _start\n"); return 1; }
  wasmtime_error_t *error = trap ? NULL :
    wasmtime_func_call(context, &start.of.func, NULL, 0, NULL, 0, &trap);
  int32_t status = 0;
  if (error && wasmtime_error_exit_status(error, &status)) wasmtime_error_delete(error);
  else check(error);
  if (trap) {
    wasm_message_t message;
    wasm_trap_message(trap, &message);
    fprintf(stderr, "%.*s\n", (int)message.size, message.data);
    wasm_byte_vec_delete(&message);
    wasm_trap_delete(trap);
    status = 1;
  }
  wasmtime_module_delete(module);
  wasmtime_linker_delete(linker);
  wasmtime_store_delete(store);
  wasm_engine_delete(engine);
  return status;
}
