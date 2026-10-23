(module
  (import "wasi_snapshot_preview1" "fd_read"
    (func $read (param i32 i32 i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "fd_write"
    (func $write (param i32 i32 i32 i32) (result i32)))
  (memory (export "memory") 1)
  (table (export "__indirect_function_table") 0 funcref)
  (global (export "allocCount") i64 (i64.const 0))
  (global (export "freeCount") i64 (i64.const 0))
  (global $calls (mut i64) (i64.const 0))
  (data (i32.const 128) "\ff\00ERR\0a")

  (func $count (param $errno i32) (param $ptr i32) (result i32)
    local.get $errno
    i32.eqz
    if (result i32)
      local.get $ptr
      i32.load
    else
      i32.const 0
    end)

  (func $echo (export "echo") (result i64 i64 i64 i64 i64)
    (local $read_errno i32) (local $read_count i32) (local $write_errno i32)
    i32.const 32
    i32.const 256
    i32.store
    i32.const 36
    i32.const 4
    i32.store
    i32.const 48
    i32.const 0
    i32.store
    i32.const 52
    i32.const 0
    i32.store
    i32.const 0
    i32.const 32
    i32.const 1
    i32.const 48
    call $read
    local.set $read_errno
    local.get $read_errno
    i32.const 48
    call $count
    local.set $read_count
    i32.const 36
    local.get $read_count
    i32.store
    i32.const 1
    i32.const 32
    i32.const 1
    i32.const 52
    call $write
    local.set $write_errno
    global.get $calls
    i64.const 1
    i64.add
    global.set $calls
    local.get $read_errno
    i64.extend_i32_u
    local.get $read_count
    i64.extend_i32_u
    local.get $write_errno
    i64.extend_i32_u
    local.get $write_errno
    i32.const 52
    call $count
    i64.extend_i32_u
    global.get $calls)

  (func $stderr (export "stderr") (result i64 i64)
    (local $errno i32)
    i32.const 32
    i32.const 128
    i32.store
    i32.const 36
    i32.const 6
    i32.store
    i32.const 52
    i32.const 0
    i32.store
    i32.const 2
    i32.const 32
    i32.const 1
    i32.const 52
    call $write
    local.tee $errno
    i64.extend_i32_u
    local.get $errno
    i32.const 52
    call $count
    i64.extend_i32_u)

  (func (export "zero") (result i64 i64 i64 i64)
    (local $read_errno i32) (local $write_errno i32)
    i32.const 32
    i32.const 256
    i32.store
    i32.const 36
    i32.const 0
    i32.store
    i32.const 48
    i32.const 99
    i32.store
    i32.const 52
    i32.const 99
    i32.store
    i32.const 0
    i32.const 32
    i32.const 1
    i32.const 48
    call $read
    local.set $read_errno
    i32.const 1
    i32.const 32
    i32.const 1
    i32.const 52
    call $write
    local.set $write_errno
    local.get $read_errno
    i64.extend_i32_u
    local.get $read_errno
    i32.const 48
    call $count
    i64.extend_i32_u
    local.get $write_errno
    i64.extend_i32_u
    local.get $write_errno
    i32.const 52
    call $count
    i64.extend_i32_u)

  (func (export "badFd") (result i64 i64)
    (local $errno i32)
    i32.const 32
    i32.const 256
    i32.store
    i32.const 36
    i32.const 4
    i32.store
    i32.const 48
    i32.const 99
    i32.store
    i32.const 9
    i32.const 32
    i32.const 1
    i32.const 48
    call $read
    local.tee $errno
    i64.extend_i32_u
    local.get $errno
    i32.const 48
    call $count
    i64.extend_i32_u)

  (func (export "_start")
    call $echo
    drop
    drop
    drop
    drop
    drop
    call $stderr
    drop
    drop))
