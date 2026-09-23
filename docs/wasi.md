# WASI Preview 1

`LeanExe.Wasi` provides the 46 functions in [`wasi_snapshot_preview1`](https://github.com/WebAssembly/WASI/blob/wasi-0.1/preview1/witx/wasi_snapshot_preview1.witx).  The compiler emits calls to the standard WASI imports.  Programs run on a WASI host such as Wasmtime, which supplies descriptors, preopened directories, arguments, environment variables, and other process resources.

## Use

```lean
import LeanExe.Wasi

open LeanExe.Wasi

def main : Action UInt32 := do
  let result ← fd_read 0 4096
  match result with
  | .error e => return e
  | .ok bytes =>
    let result ← fd_write 1 bytes
    match result with
    | .error e => return e
    | .ok n => return if n.toNat == bytes.size then 0 else 1
```

The entry has type `Action UInt32` and takes no arguments.  Its result becomes the process exit code.  Build the source module before compiling its entry:

```sh
tools/leanrun --timeout 5m lake build lean-wasm MyProgram
tools/leanrun --timeout 2m .lake/build/bin/lean-wasm compile-wasi-api \
  --module MyProgram --entry main --out build/program.wasm
build/tools/wasmtime/current/wasmtime run build/program.wasm
```

`Action` is an abbreviation for `BaseIO`.  Binding an action executes it once, including when the program discards its result.  Reusing a stored action executes it again at each bind.  Pure compilation and evaluation commands reject these declarations.

## Values and errors

Operations that return data use `Except UInt32 α`.  Operations with no data result return the numeric WASI errno, with zero indicating success.  `proc_exit` terminates execution.  The `Errno` namespace names every Preview 1 error code.

Descriptors, enum tags, flags, and buffer capacities use `UInt32`.  Rights, timestamps, sizes of files, and offsets use `UInt64`.  `fd_seek` interprets its offset as the signed 64-bit WASI bit pattern, so `0 - 2` seeks backwards by two bytes.  The API defines constants for clocks, rights, file types, whence, advice, flags, events, and signals.

Enum tags and flags must use values permitted by WASI.  A host can trap when decoding an invalid enum tag before calling the operation.  Unsupported operations retain the host's result; Wasmtime 44 returns `notsup` for `fd_allocate` and `proc_raise`.  Its default host returns `badf` for rights reduction through `fd_fdstat_set_rights`, while its legacy Preview 1 host returns `notsup`.

ByteArray arguments remain values.  Reads and other buffer-producing operations allocate an owned result, and a later host call cannot change an earlier result.  The compiler releases temporary buffers after an error or after their last use.  Allocation follows the compiler runtime's existing trap-on-exhaustion behavior.

`fd_read`, `fd_pread`, and `sock_recv` take a maximum byte count and use one WASI iovec.  `fd_write`, `fd_pwrite`, and `sock_send` take one ByteArray and return the transferred byte count.  Calls preserve partial transfers, EOF, `again`, and `intr`.  They do not retry, fill a buffer, or finish a partial write.  A zero-capacity read still calls the host, and a successful empty result is an empty ByteArray.  Wasmtime 44 returns `intr` for that read through its default host and an empty success through its legacy host.

## Operations

| Area | Functions and result values |
| --- | --- |
| Arguments and environment | `args_sizes_get`, `environ_sizes_get`: count and encoded byte size. `args_get`, `environ_get`: `Array ByteArray`, without terminating NUL bytes. Arguments include `argv[0]`; environment entries retain `NAME=value`. |
| Clocks | `clock_res_get`, `clock_time_get`: nanosecond timestamps or resolution. |
| Descriptor data | `fd_read`, `fd_pread`: ByteArray. `fd_write`, `fd_pwrite`: byte count. `fd_seek`, `fd_tell`: offset. |
| Descriptor metadata | `fd_fdstat_get`: `FdStat`. `fd_filestat_get`: `FileStat`. `fd_prestat_get`: `Prestat`. `fd_prestat_dir_name`: ByteArray. |
| Descriptor changes | `fd_close`, `fd_advise`, `fd_allocate`, `fd_datasync`, `fd_sync`, `fd_renumber`, `fd_fdstat_set_flags`, `fd_fdstat_set_rights`, `fd_filestat_set_size`, `fd_filestat_set_times`. |
| Paths | `path_open`: descriptor. `path_filestat_get`: `FileStat`. `path_readlink`: ByteArray. `path_create_directory`, `path_filestat_set_times`, `path_link`, `path_remove_directory`, `path_rename`, `path_symlink`, `path_unlink_file`: errno. |
| Directory entries | `fd_readdir`: packed ByteArray, including any truncated final record. |
| Polling | `poll_oneoff`: `Array Event`, from an `Array Subscription`. |
| Process and random data | `proc_exit`, `proc_raise`, `sched_yield`, `random_get`. |
| Inherited sockets | `sock_accept`: descriptor. `sock_recv`: ByteArray and receive flags. `sock_send`: byte count. `sock_shutdown`: errno. |

Paths are length-delimited ByteArrays.  The WASI host applies its path encoding and capability rules.  File descriptors remain explicit resources, and programs close them with `fd_close`.  `fd_prestat_dir_name` queries the preopen's name length before allocating its result, as `args_get` and `environ_get` query their sizes before fetching data.

`fd_readdir` retains the [native directory format](https://github.com/WebAssembly/WASI/blob/wasi-0.1/preview1/docs.md#dirent): a 24-byte header followed by name bytes.  The header contains the next cookie at offset 0, inode at 8, name length at 16, and file type at 20, in little-endian order.  The caller must check that the header and name fit before decoding a record.  The initial cookie is zero.

`Subscription.clock userdata clock timeout precision flags` constructs a timer subscription.  `Subscription.read userdata fd` and `Subscription.write userdata fd` construct descriptor subscriptions.  Clock timeouts are relative nanoseconds unless `Subclockflags.subscription_clock_abstime` is set.  Each returned event contains its userdata, error, event type, byte count, and flags.  A successful poll may contain events with nonzero errors, and an empty subscription array returns `inval`.

`poll_oneoff` supplies the native waiting mechanism.  It does not place a deadline on a later read or write.  Programs can set `Fdflags.nonblock` where the host supports it, poll for readiness, and handle `again` explicitly.  Socket operations use inherited sockets, since Preview 1 has no socket creation, bind, listen, or connect calls.

## Tests

`test/wasi_api.js` builds Lean examples, validates the emitted modules with `wasm-tools`, and executes them on Wasmtime.  The 38 cases cover all operation families, binary data and EOF, a four-megabyte stream, relative and absolute timers, descriptor errors, filesystem changes, inherited TCP sockets, and allocation/free counters.  Socket tests use Wasmtime 44's legacy Preview 1 host and poll its inherited listener before accepting a connection.  The test driver invokes `tools/leanrun` for Lean and compiler commands.

```sh
node test/wasi_api.js
```
