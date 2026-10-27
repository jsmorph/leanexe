(module
  (import "wasi_snapshot_preview1" "proc_exit" (func $exit (param i32)))
  (memory (export "memory") 1)
  (table (export "__indirect_function_table") 0 funcref)
  (func (export "_start")
    i64.const 4294967422
    i32.wrap_i64
    call $exit
    unreachable))
