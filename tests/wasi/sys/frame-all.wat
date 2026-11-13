;; Frame test of every flat Preview 1 function, which tools/wasi-calls.py generates from
;; the pinned witx and its list of steps.  Each step fills the working memory [0, 65536)
;; with the guard byte 0xA5, writes the call's inputs, copies the working memory to the
;; shadow copy at 65536, and calls the function.  A result word or record lies at a
;; multiple of its alignment that is not a multiple of twice it, so that Wasmtime traps
;; when a description gives it a smaller alignment.  The step then checks the errno,
;; that every byte outside the call's declared regions equals the shadow copy, and the
;; values the step lists.  The exit status names the first failed check: the step's
;; number for the errno, 42 plus it for a byte outside the regions, and 84 plus it for
;; a value.
(module
  (import "wasi_snapshot_preview1" "args_get"
    (func $args_get (param i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "args_sizes_get"
    (func $args_sizes_get (param i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "environ_get"
    (func $environ_get (param i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "environ_sizes_get"
    (func $environ_sizes_get (param i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "clock_res_get"
    (func $clock_res_get (param i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "clock_time_get"
    (func $clock_time_get (param i32 i64 i32) (result i32)))
  (import "wasi_snapshot_preview1" "fd_advise"
    (func $fd_advise (param i32 i64 i64 i32) (result i32)))
  (import "wasi_snapshot_preview1" "fd_allocate"
    (func $fd_allocate (param i32 i64 i64) (result i32)))
  (import "wasi_snapshot_preview1" "fd_close"
    (func $fd_close (param i32) (result i32)))
  (import "wasi_snapshot_preview1" "fd_datasync"
    (func $fd_datasync (param i32) (result i32)))
  (import "wasi_snapshot_preview1" "fd_fdstat_get"
    (func $fd_fdstat_get (param i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "fd_fdstat_set_flags"
    (func $fd_fdstat_set_flags (param i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "fd_fdstat_set_rights"
    (func $fd_fdstat_set_rights (param i32 i64 i64) (result i32)))
  (import "wasi_snapshot_preview1" "fd_filestat_get"
    (func $fd_filestat_get (param i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "fd_filestat_set_size"
    (func $fd_filestat_set_size (param i32 i64) (result i32)))
  (import "wasi_snapshot_preview1" "fd_filestat_set_times"
    (func $fd_filestat_set_times (param i32 i64 i64 i32) (result i32)))
  (import "wasi_snapshot_preview1" "fd_prestat_get"
    (func $fd_prestat_get (param i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "fd_prestat_dir_name"
    (func $fd_prestat_dir_name (param i32 i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "fd_readdir"
    (func $fd_readdir (param i32 i32 i32 i64 i32) (result i32)))
  (import "wasi_snapshot_preview1" "fd_renumber"
    (func $fd_renumber (param i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "fd_seek"
    (func $fd_seek (param i32 i64 i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "fd_sync"
    (func $fd_sync (param i32) (result i32)))
  (import "wasi_snapshot_preview1" "fd_tell"
    (func $fd_tell (param i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "path_create_directory"
    (func $path_create_directory (param i32 i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "path_filestat_get"
    (func $path_filestat_get (param i32 i32 i32 i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "path_filestat_set_times"
    (func $path_filestat_set_times (param i32 i32 i32 i32 i64 i64 i32) (result i32)))
  (import "wasi_snapshot_preview1" "path_link"
    (func $path_link (param i32 i32 i32 i32 i32 i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "path_open"
    (func $path_open (param i32 i32 i32 i32 i32 i64 i64 i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "path_readlink"
    (func $path_readlink (param i32 i32 i32 i32 i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "path_remove_directory"
    (func $path_remove_directory (param i32 i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "path_rename"
    (func $path_rename (param i32 i32 i32 i32 i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "path_symlink"
    (func $path_symlink (param i32 i32 i32 i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "path_unlink_file"
    (func $path_unlink_file (param i32 i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "proc_raise"
    (func $proc_raise (param i32) (result i32)))
  (import "wasi_snapshot_preview1" "sched_yield"
    (func $sched_yield (result i32)))
  (import "wasi_snapshot_preview1" "random_get"
    (func $random_get (param i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "sock_accept"
    (func $sock_accept (param i32 i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "sock_shutdown"
    (func $sock_shutdown (param i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "proc_exit" (func $proc_exit (param i32)))
  (memory (export "memory") 3)
  (data (i32.const 131072) "d")
  (data (i32.const 131328) "f")
  (data (i32.const 131584) "g")
  (data (i32.const 131840) "s")
  (data (i32.const 132096) "h")
  (func $fail (param $status i32)
    (call $proc_exit (local.get $status))
    (unreachable))
  (func $prepare
    (memory.fill (i32.const 0) (i32.const 0xA5) (i32.const 65536)))
  (func $snapshot
    (memory.copy (i32.const 65536) (i32.const 0) (i32.const 65536)))
  (func $errno (param $step i32) (param $got i32) (param $want i32)
    (if (i32.ne (local.get $got) (local.get $want))
      (then (call $fail (local.get $step)))))
  (func $value (param $step i32) (param $got i64) (param $want i64)
    (if (i64.ne (local.get $got) (local.get $want))
      (then (call $fail (i32.add (i32.const 84) (local.get $step))))))
  (func $inside (param $address i32) (param $start i32) (param $length i32) (result i32)
    (i32.and (i32.ge_u (local.get $address) (local.get $start))
      (i32.lt_u (local.get $address) (i32.add (local.get $start) (local.get $length)))))
  (func $check (param $step i32) (param $s1 i32) (param $n1 i32) (param $s2 i32)
      (param $n2 i32)
    (local $index i32)
    (block $done
      (loop $next
        (br_if $done (i32.ge_u (local.get $index) (i32.const 65536)))
        (if (i32.eqz (i32.or
              (call $inside (local.get $index) (local.get $s1) (local.get $n1))
              (call $inside (local.get $index) (local.get $s2) (local.get $n2))))
          (then
            (if (i32.ne (i32.load8_u (local.get $index))
                  (i32.load8_u (i32.add (local.get $index) (i32.const 65536))))
              (then (call $fail (i32.add (i32.const 42) (local.get $step)))))))
        (local.set $index (i32.add (local.get $index) (i32.const 1)))
        (br $next))))
  (func (export "_start")
    (local $count i32) (local $size i32) (local $file i32) (local $second i32)
    ;; 1: args_sizes_get
    (call $prepare)
    (call $snapshot)
    (call $errno (i32.const 1) (call $args_sizes_get (i32.const 20) (i32.const 28)) (i32.const 0))
    (call $check (i32.const 1) (i32.const 20) (i32.const 4)
      (i32.const 28) (i32.const 4))
    (call $value (i32.const 1) (i64.load32_u (i32.const 20)) (i64.const 2))
    (call $value (i32.const 1) (i64.load32_u (i32.const 28)) (i64.const 7))
    (local.set $count (i32.load (i32.const 20)))
    (local.set $size (i32.load (i32.const 28)))
    ;; 2: args_get
    (call $prepare)
    (call $snapshot)
    (call $errno (i32.const 2) (call $args_get (i32.const 8196) (i32.const 12288)) (i32.const 0))
    (call $check (i32.const 2) (i32.const 8196) (i32.mul (local.get $count) (i32.const 4))
      (i32.const 12288) (local.get $size))
    ;; 3: environ_sizes_get
    (call $prepare)
    (call $snapshot)
    (call $errno (i32.const 3) (call $environ_sizes_get (i32.const 20)
      (i32.const 28)) (i32.const 0))
    (call $check (i32.const 3) (i32.const 20) (i32.const 4)
      (i32.const 28) (i32.const 4))
    (call $value (i32.const 3) (i64.load32_u (i32.const 20)) (i64.const 0))
    (call $value (i32.const 3) (i64.load32_u (i32.const 28)) (i64.const 0))
    (local.set $count (i32.load (i32.const 20)))
    (local.set $size (i32.load (i32.const 28)))
    ;; 4: environ_get
    (call $prepare)
    (call $snapshot)
    (call $errno (i32.const 4) (call $environ_get (i32.const 8196) (i32.const 12288)) (i32.const 0))
    (call $check (i32.const 4) (i32.const 8196) (i32.mul (local.get $count) (i32.const 4))
      (i32.const 12288) (local.get $size))
    ;; 5: clock_res_get
    (call $prepare)
    (call $snapshot)
    (call $errno (i32.const 5) (call $clock_res_get (i32.const 1) (i32.const 24)) (i32.const 0))
    (call $check (i32.const 5) (i32.const 24) (i32.const 8)
      (i32.const 0) (i32.const 0))
    ;; 6: clock_time_get
    (call $prepare)
    (call $snapshot)
    (call $errno (i32.const 6) (call $clock_time_get (i32.const 0) (i64.const 1)
      (i32.const 24)) (i32.const 0))
    (call $check (i32.const 6) (i32.const 24) (i32.const 8)
      (i32.const 0) (i32.const 0))
    ;; 7: random_get
    (call $prepare)
    (call $snapshot)
    (call $errno (i32.const 7) (call $random_get (i32.const 4096) (i32.const 32)) (i32.const 0))
    (call $check (i32.const 7) (i32.const 4096) (i32.const 32)
      (i32.const 0) (i32.const 0))
    ;; 8: sched_yield
    (call $prepare)
    (call $snapshot)
    (call $errno (i32.const 8) (call $sched_yield ) (i32.const 0))
    (call $check (i32.const 8) (i32.const 0) (i32.const 0)
      (i32.const 0) (i32.const 0))
    ;; 9: proc_raise
    (call $prepare)
    (call $snapshot)
    (call $errno (i32.const 9) (call $proc_raise (i32.const 1)) (i32.const 58))
    (call $check (i32.const 9) (i32.const 0) (i32.const 0)
      (i32.const 0) (i32.const 0))
    ;; 10: fd_prestat_get
    (call $prepare)
    (call $snapshot)
    (call $errno (i32.const 10) (call $fd_prestat_get (i32.const 3) (i32.const 68)) (i32.const 0))
    (call $check (i32.const 10) (i32.const 68) (i32.const 8)
      (i32.const 0) (i32.const 0))
    (call $value (i32.const 10) (i64.load8_u (i32.const 68)) (i64.const 0))
    (call $value (i32.const 10) (i64.load32_u (i32.const 72)) (i64.const 1))
    ;; 11: fd_prestat_dir_name
    (call $prepare)
    (call $snapshot)
    (call $errno (i32.const 11) (call $fd_prestat_dir_name (i32.const 3) (i32.const 4096)
      (i32.const 1)) (i32.const 0))
    (call $check (i32.const 11) (i32.const 4096) (i32.const 1)
      (i32.const 0) (i32.const 0))
    (call $value (i32.const 11) (i64.load8_u (i32.const 4096)) (i64.const 46))
    ;; 12: fd_fdstat_get
    (call $prepare)
    (call $snapshot)
    (call $errno (i32.const 12) (call $fd_fdstat_get (i32.const 3) (i32.const 72)) (i32.const 0))
    (call $check (i32.const 12) (i32.const 72) (i32.const 24)
      (i32.const 0) (i32.const 0))
    (call $value (i32.const 12) (i64.load8_u (i32.const 72)) (i64.const 3))
    ;; 13: fd_filestat_get
    (call $prepare)
    (call $snapshot)
    (call $errno (i32.const 13) (call $fd_filestat_get (i32.const 3) (i32.const 72)) (i32.const 0))
    (call $check (i32.const 13) (i32.const 72) (i32.const 64)
      (i32.const 0) (i32.const 0))
    (call $value (i32.const 13) (i64.load8_u (i32.const 88)) (i64.const 3))
    ;; 14: path_create_directory
    (call $prepare)
    (memory.copy (i32.const 1024) (i32.const 131072) (i32.const 1))
    (call $snapshot)
    (call $errno (i32.const 14) (call $path_create_directory (i32.const 3) (i32.const 1024)
      (i32.const 1)) (i32.const 0))
    (call $check (i32.const 14) (i32.const 0) (i32.const 0)
      (i32.const 0) (i32.const 0))
    ;; 15: path_open
    (call $prepare)
    (memory.copy (i32.const 1024) (i32.const 131328) (i32.const 1))
    (call $snapshot)
    (call $errno (i32.const 15) (call $path_open (i32.const 3) (i32.const 0) (i32.const 1024)
      (i32.const 1) (i32.const 1) (i64.const 1073741823) (i64.const 1073741823) (i32.const 0)
      (i32.const 20)) (i32.const 0))
    (call $check (i32.const 15) (i32.const 20) (i32.const 4)
      (i32.const 0) (i32.const 0))
    (local.set $file (i32.load (i32.const 20)))
    ;; 16: fd_allocate
    (call $prepare)
    (call $snapshot)
    (call $errno (i32.const 16) (call $fd_allocate (local.get $file) (i64.const 0)
      (i64.const 16)) (i32.const 58))
    (call $check (i32.const 16) (i32.const 0) (i32.const 0)
      (i32.const 0) (i32.const 0))
    ;; 17: fd_filestat_set_size
    (call $prepare)
    (call $snapshot)
    (call $errno (i32.const 17) (call $fd_filestat_set_size (local.get $file)
      (i64.const 4294967301)) (i32.const 0))
    (call $check (i32.const 17) (i32.const 0) (i32.const 0)
      (i32.const 0) (i32.const 0))
    ;; 18: fd_filestat_set_times
    (call $prepare)
    (call $snapshot)
    (call $errno (i32.const 18) (call $fd_filestat_set_times (local.get $file) (i64.const 0)
      (i64.const 0) (i32.const 0)) (i32.const 0))
    (call $check (i32.const 18) (i32.const 0) (i32.const 0)
      (i32.const 0) (i32.const 0))
    ;; 19: fd_fdstat_set_flags
    (call $prepare)
    (call $snapshot)
    (call $errno (i32.const 19) (call $fd_fdstat_set_flags (local.get $file)
      (i32.const 0)) (i32.const 0))
    (call $check (i32.const 19) (i32.const 0) (i32.const 0)
      (i32.const 0) (i32.const 0))
    ;; 20: fd_fdstat_set_rights
    (call $prepare)
    (call $snapshot)
    (call $errno (i32.const 20) (call $fd_fdstat_set_rights (local.get $file) (i64.const 1073741823)
      (i64.const 1073741823)) (i32.const 58))
    (call $check (i32.const 20) (i32.const 0) (i32.const 0)
      (i32.const 0) (i32.const 0))
    ;; 21: fd_advise
    (call $prepare)
    (call $snapshot)
    (call $errno (i32.const 21) (call $fd_advise (local.get $file) (i64.const 0) (i64.const 0)
      (i32.const 0)) (i32.const 0))
    (call $check (i32.const 21) (i32.const 0) (i32.const 0)
      (i32.const 0) (i32.const 0))
    ;; 22: fd_seek
    (call $prepare)
    (call $snapshot)
    (call $errno (i32.const 22) (call $fd_seek (local.get $file) (i64.const 5) (i32.const 0)
      (i32.const 24)) (i32.const 0))
    (call $check (i32.const 22) (i32.const 24) (i32.const 8)
      (i32.const 0) (i32.const 0))
    (call $value (i32.const 22) (i64.load (i32.const 24)) (i64.const 5))
    ;; 23: fd_tell
    (call $prepare)
    (call $snapshot)
    (call $errno (i32.const 23) (call $fd_tell (local.get $file) (i32.const 24)) (i32.const 0))
    (call $check (i32.const 23) (i32.const 24) (i32.const 8)
      (i32.const 0) (i32.const 0))
    (call $value (i32.const 23) (i64.load (i32.const 24)) (i64.const 5))
    ;; 24: fd_datasync
    (call $prepare)
    (call $snapshot)
    (call $errno (i32.const 24) (call $fd_datasync (local.get $file)) (i32.const 0))
    (call $check (i32.const 24) (i32.const 0) (i32.const 0)
      (i32.const 0) (i32.const 0))
    ;; 25: fd_sync
    (call $prepare)
    (call $snapshot)
    (call $errno (i32.const 25) (call $fd_sync (local.get $file)) (i32.const 0))
    (call $check (i32.const 25) (i32.const 0) (i32.const 0)
      (i32.const 0) (i32.const 0))
    ;; 26: path_filestat_get
    (call $prepare)
    (memory.copy (i32.const 1024) (i32.const 131328) (i32.const 1))
    (call $snapshot)
    (call $errno (i32.const 26) (call $path_filestat_get (i32.const 3) (i32.const 0)
      (i32.const 1024) (i32.const 1) (i32.const 72)) (i32.const 0))
    (call $check (i32.const 26) (i32.const 72) (i32.const 64)
      (i32.const 0) (i32.const 0))
    (call $value (i32.const 26) (i64.load8_u (i32.const 88)) (i64.const 4))
    (call $value (i32.const 26) (i64.load (i32.const 104)) (i64.const 4294967301))
    ;; 27: path_filestat_set_times
    (call $prepare)
    (memory.copy (i32.const 1024) (i32.const 131328) (i32.const 1))
    (call $snapshot)
    (call $errno (i32.const 27) (call $path_filestat_set_times (i32.const 3) (i32.const 0)
      (i32.const 1024) (i32.const 1) (i64.const 0) (i64.const 0) (i32.const 0)) (i32.const 0))
    (call $check (i32.const 27) (i32.const 0) (i32.const 0)
      (i32.const 0) (i32.const 0))
    ;; 28: path_link
    (call $prepare)
    (memory.copy (i32.const 1024) (i32.const 131328) (i32.const 1))
    (memory.copy (i32.const 1280) (i32.const 131584) (i32.const 1))
    (call $snapshot)
    (call $errno (i32.const 28) (call $path_link (i32.const 3) (i32.const 0) (i32.const 1024)
      (i32.const 1) (i32.const 3) (i32.const 1280) (i32.const 1)) (i32.const 0))
    (call $check (i32.const 28) (i32.const 0) (i32.const 0)
      (i32.const 0) (i32.const 0))
    ;; 29: path_symlink
    (call $prepare)
    (memory.copy (i32.const 1024) (i32.const 131328) (i32.const 1))
    (memory.copy (i32.const 1280) (i32.const 131840) (i32.const 1))
    (call $snapshot)
    (call $errno (i32.const 29) (call $path_symlink (i32.const 1024) (i32.const 1) (i32.const 3)
      (i32.const 1280) (i32.const 1)) (i32.const 0))
    (call $check (i32.const 29) (i32.const 0) (i32.const 0)
      (i32.const 0) (i32.const 0))
    ;; 30: path_readlink
    (call $prepare)
    (memory.copy (i32.const 1024) (i32.const 131840) (i32.const 1))
    (call $snapshot)
    (call $errno (i32.const 30) (call $path_readlink (i32.const 3) (i32.const 1024) (i32.const 1)
      (i32.const 4096) (i32.const 1) (i32.const 20)) (i32.const 0))
    (call $check (i32.const 30) (i32.const 4096) (i32.const 1)
      (i32.const 20) (i32.const 4))
    (call $value (i32.const 30) (i64.load8_u (i32.const 4096)) (i64.const 102))
    (call $value (i32.const 30) (i64.load32_u (i32.const 20)) (i64.const 1))
    ;; 31: fd_readdir
    (call $prepare)
    (call $snapshot)
    (call $errno (i32.const 31) (call $fd_readdir (i32.const 3) (i32.const 4096) (i32.const 16)
      (i64.const 0) (i32.const 20)) (i32.const 0))
    (call $check (i32.const 31) (i32.const 4096) (i32.const 16)
      (i32.const 20) (i32.const 4))
    ;; 32: path_rename
    (call $prepare)
    (memory.copy (i32.const 1024) (i32.const 131584) (i32.const 1))
    (memory.copy (i32.const 1280) (i32.const 132096) (i32.const 1))
    (call $snapshot)
    (call $errno (i32.const 32) (call $path_rename (i32.const 3) (i32.const 1024) (i32.const 1)
      (i32.const 3) (i32.const 1280) (i32.const 1)) (i32.const 0))
    (call $check (i32.const 32) (i32.const 0) (i32.const 0)
      (i32.const 0) (i32.const 0))
    ;; 33: path_open
    (call $prepare)
    (memory.copy (i32.const 1024) (i32.const 132096) (i32.const 1))
    (call $snapshot)
    (call $errno (i32.const 33) (call $path_open (i32.const 3) (i32.const 0) (i32.const 1024)
      (i32.const 1) (i32.const 0) (i64.const 1073741823) (i64.const 1073741823) (i32.const 0)
      (i32.const 20)) (i32.const 0))
    (call $check (i32.const 33) (i32.const 20) (i32.const 4)
      (i32.const 0) (i32.const 0))
    (local.set $second (i32.load (i32.const 20)))
    ;; 34: fd_renumber
    (call $prepare)
    (call $snapshot)
    (call $errno (i32.const 34) (call $fd_renumber (local.get $file)
      (local.get $second)) (i32.const 0))
    (call $check (i32.const 34) (i32.const 0) (i32.const 0)
      (i32.const 0) (i32.const 0))
    ;; 35: fd_close
    (call $prepare)
    (call $snapshot)
    (call $errno (i32.const 35) (call $fd_close (local.get $second)) (i32.const 0))
    (call $check (i32.const 35) (i32.const 0) (i32.const 0)
      (i32.const 0) (i32.const 0))
    ;; 36: path_unlink_file
    (call $prepare)
    (memory.copy (i32.const 1024) (i32.const 132096) (i32.const 1))
    (call $snapshot)
    (call $errno (i32.const 36) (call $path_unlink_file (i32.const 3) (i32.const 1024)
      (i32.const 1)) (i32.const 0))
    (call $check (i32.const 36) (i32.const 0) (i32.const 0)
      (i32.const 0) (i32.const 0))
    ;; 37: path_unlink_file
    (call $prepare)
    (memory.copy (i32.const 1024) (i32.const 131840) (i32.const 1))
    (call $snapshot)
    (call $errno (i32.const 37) (call $path_unlink_file (i32.const 3) (i32.const 1024)
      (i32.const 1)) (i32.const 0))
    (call $check (i32.const 37) (i32.const 0) (i32.const 0)
      (i32.const 0) (i32.const 0))
    ;; 38: path_unlink_file
    (call $prepare)
    (memory.copy (i32.const 1024) (i32.const 131328) (i32.const 1))
    (call $snapshot)
    (call $errno (i32.const 38) (call $path_unlink_file (i32.const 3) (i32.const 1024)
      (i32.const 1)) (i32.const 0))
    (call $check (i32.const 38) (i32.const 0) (i32.const 0)
      (i32.const 0) (i32.const 0))
    ;; 39: path_remove_directory
    (call $prepare)
    (memory.copy (i32.const 1024) (i32.const 131072) (i32.const 1))
    (call $snapshot)
    (call $errno (i32.const 39) (call $path_remove_directory (i32.const 3) (i32.const 1024)
      (i32.const 1)) (i32.const 0))
    (call $check (i32.const 39) (i32.const 0) (i32.const 0)
      (i32.const 0) (i32.const 0))
    ;; 40: sock_accept
    (call $prepare)
    (call $snapshot)
    (call $errno (i32.const 40) (call $sock_accept (i32.const 3) (i32.const 0)
      (i32.const 20)) (i32.const 57))
    (call $check (i32.const 40) (i32.const 20) (i32.const 4)
      (i32.const 0) (i32.const 0))
    ;; 41: sock_shutdown
    (call $prepare)
    (call $snapshot)
    (call $errno (i32.const 41) (call $sock_shutdown (i32.const 3) (i32.const 1)) (i32.const 57))
    (call $check (i32.const 41) (i32.const 0) (i32.const 0)
      (i32.const 0) (i32.const 0))
    (call $proc_exit (i32.const 0)))
)
