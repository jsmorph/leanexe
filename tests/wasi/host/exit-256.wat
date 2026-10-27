(module
  (import "wasi_snapshot_preview1" "proc_exit" (func $exit (param i32)))
  (memory (export "memory") 1)
  (table (export "__indirect_function_table") 0 funcref)
  (func (export "_start")
    i32.const 256
    call $exit
    unreachable))
