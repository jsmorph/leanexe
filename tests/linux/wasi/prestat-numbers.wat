;; The prestat functions of WASI Preview 1 on a list of descriptor numbers, for the AArch64 Linux
;; executable of tests/linux/a64-wasi-preopen.sh and the Wasmtime host.
;;
;; For each number `$probe` writes to standard output, with `fd_write` of one iovec at address 0
;; and the count at address 8 as the stream stub of the executable requires: the errno of
;; `fd_prestat_get` as 4 bytes and the 8 bytes of its record at address 64, which holds zeros before
;; the call, since Wasmtime 44 writes the record's tag and name length and leaves its three bytes of
;; padding while the shim's specification writes all 8 bytes; and for buffers of 0, 1, and 4 bytes at address 128, which holds 0xBB bytes
;; before each call, the errno of `fd_prestat_dir_name` as 4 bytes and the 8 bytes from 128.  The
;; numbers are 0 to 5, 1023, 1024, 2^31 - 1, 2^31, and 2^32 - 1.  The status is 0.
(module
  (import "wasi_snapshot_preview1" "fd_read"
    (func $fd_read (param i32 i32 i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "fd_write"
    (func $fd_write (param i32 i32 i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "proc_exit" (func $proc_exit (param i32)))
  (import "wasi_snapshot_preview1" "fd_prestat_get"
    (func $prestat_get (param i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "fd_prestat_dir_name"
    (func $prestat_dir_name (param i32 i32 i32) (result i32)))
  (memory (export "memory") 1)

  ;; Writes the `$length` bytes at `$pointer` to standard output and keeps the errno at address
  ;; 12, since the AArch64 generator has no `drop`.
  (func $out (param $pointer i32) (param $length i32)
    (i32.store (i32.const 0) (local.get $pointer))
    (i32.store (i32.const 4) (local.get $length))
    (i32.store (i32.const 12)
      (call $fd_write (i32.const 1) (i32.const 0) (i32.const 1) (i32.const 8))))

  ;; `fd_prestat_dir_name` of `$fd` into `$capacity` bytes at 128.
  (func $name (param $fd i32) (param $capacity i32)
    (i64.store (i32.const 128) (i64.const 0xbbbbbbbbbbbbbbbb))
    (i32.store (i32.const 16)
      (call $prestat_dir_name (local.get $fd) (i32.const 128) (local.get $capacity)))
    (call $out (i32.const 16) (i32.const 4))
    (call $out (i32.const 128) (i32.const 8)))

  (func $probe (param $fd i32)
    (i64.store (i32.const 64) (i64.const 0))
    (i32.store (i32.const 16) (call $prestat_get (local.get $fd) (i32.const 64)))
    (call $out (i32.const 16) (i32.const 4))
    (call $out (i32.const 64) (i32.const 8))
    (call $name (local.get $fd) (i32.const 0))
    (call $name (local.get $fd) (i32.const 1))
    (call $name (local.get $fd) (i32.const 4)))

  (func (export "_start")
    (call $probe (i32.const 0))
    (call $probe (i32.const 1))
    (call $probe (i32.const 2))
    (call $probe (i32.const 3))
    (call $probe (i32.const 4))
    (call $probe (i32.const 5))
    (call $probe (i32.const 1023))
    (call $probe (i32.const 1024))
    (call $probe (i32.const 0x7fffffff))
    (call $probe (i32.const 0x80000000))
    (call $probe (i32.const 0xffffffff))))
