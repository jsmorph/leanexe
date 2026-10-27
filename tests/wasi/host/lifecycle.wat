(module
  (import "wasi_snapshot_preview1" "fd_write"
    (func $write (param i32 i32 i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "proc_exit" (func $exit (param i32)))
  (memory (export "memory") 1)
  (table (export "__indirect_function_table") 0 funcref)
  (data (i32.const 128) "before\0a")
  (data (i32.const 144) "after\0a")

  (func $emit (param $ptr i32) (param $len i32) (result i64 i64)
    (local $errno i32)
    i32.const 32
    local.get $ptr
    i32.store
    i32.const 36
    local.get $len
    i32.store
    i32.const 48
    i32.const 0
    i32.store
    i32.const 1
    i32.const 32
    i32.const 1
    i32.const 48
    call $write
    local.tee $errno
    i64.extend_i32_u
    local.get $errno
    i32.eqz
    if (result i64)
      i32.const 48
      i32.load
      i64.extend_i32_u
    else
      i64.const 0
    end)

  (func (export "before") (result i64 i64)
    i32.const 128
    i32.const 7
    call $emit)
  (func (export "after") (result i64 i64)
    i32.const 144
    i32.const 6
    call $emit)
  (func (export "exit") (param $code i64)
    local.get $code
    i32.wrap_i64
    call $exit
    unreachable)
  (func (export "trap")
    unreachable))
