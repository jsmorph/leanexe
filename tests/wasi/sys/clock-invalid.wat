;; `clock_time_get` with the clock id 4, outside the enum `$clockid` of four values.  Wasmtime 44
;; rejects the value when it converts the argument and traps; the test expects that trap, and
;; status 0 from `proc_exit` would mean that the call returned.
(module
  (import "wasi_snapshot_preview1" "clock_time_get"
    (func $clock_time_get (param i32 i64 i32) (result i32)))
  (import "wasi_snapshot_preview1" "proc_exit" (func $proc_exit (param i32)))
  (memory (export "memory") 1)
  (func (export "_start")
    (drop (call $clock_time_get (i32.const 4) (i64.const 1) (i32.const 0)))
    (call $proc_exit (i32.const 0))))
