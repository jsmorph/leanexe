;; Frame test of the flat WASI calls of LeanExe.Wasi.Sys under an engine.
;;
;; `_start` fills the whole memory with the guard byte 0xA5, then makes each call with its output
;; regions at fixed aligned addresses.  After each call it checks the errno, fills the call's declared
;; output regions with the guard byte again, and scans the whole memory: every byte must hold the
;; guard, so the call wrote nothing outside its declared regions.  `args_get` writes into regions of
;; the sizes that `args_sizes_get` reported: 4 bytes per argument at 4096 and the argument bytes at
;; 8192.  The test also checks that the strings fill their region exactly, ending with a zero byte,
;; and that each argument pointer points into it.  The exit status names the first failed check:
;;
;;   10+k  the errno of call k differs from the expected one
;;   20+k  call k wrote outside its declared regions
;;   30    the argument count or size exceeds the test's room
;;   31    the argument strings do not end at the reported size with a zero byte
;;   32    an argument pointer lies outside the string region
;;   33    the zero bytes of the string region do not number the reported count
;;
;; Calls: 1 clock 0, 2 clock 1, 3 clock 2 (badf, 8), 5 random 0 bytes, 6 random 1 byte,
;; 7 random 1000 bytes, 8 args_sizes_get, 9 args_get.  A clock id above 3 traps in Wasmtime 44, which
;; `clock-invalid.wat` tests.
(module
  (import "wasi_snapshot_preview1" "clock_time_get"
    (func $clock_time_get (param i32 i64 i32) (result i32)))
  (import "wasi_snapshot_preview1" "random_get"
    (func $random_get (param i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "args_sizes_get"
    (func $args_sizes_get (param i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "args_get"
    (func $args_get (param i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "proc_exit" (func $proc_exit (param i32)))
  (memory (export "memory") 1)

  (func $guard (param $start i32) (param $length i32)
    (memory.fill (local.get $start) (i32.const 0xA5) (local.get $length)))

  ;; 1 when every byte of memory holds the guard.
  (func $clean (result i32) (local $index i32)
    (block $done
      (loop $next
        (br_if $done (i32.ge_u (local.get $index) (i32.const 65536)))
        (if (i32.ne (i32.load8_u (local.get $index)) (i32.const 0xA5))
          (then (return (i32.const 0))))
        (local.set $index (i32.add (local.get $index) (i32.const 1)))
        (br $next)))
    (i32.const 1))

  (func $fail (param $status i32)
    (call $proc_exit (local.get $status))
    (unreachable))

  ;; Checks the errno of call `$call`, restores `$length` bytes at `$start`, and checks the memory.
  (func $after (param $call i32) (param $errno i32) (param $expected i32)
      (param $start i32) (param $length i32)
    (if (i32.ne (local.get $errno) (local.get $expected))
      (then (call $fail (i32.add (i32.const 10) (local.get $call)))))
    (call $guard (local.get $start) (local.get $length))
    (if (i32.eqz (call $clean))
      (then (call $fail (i32.add (i32.const 20) (local.get $call))))))

  (func (export "_start")
    (local $count i32) (local $size i32) (local $index i32) (local $pointer i32) (local $zeros i32)
    (call $guard (i32.const 0) (i32.const 65536))
    (call $after (i32.const 1) (call $clock_time_get (i32.const 0) (i64.const 1) (i32.const 1024))
      (i32.const 0) (i32.const 1024) (i32.const 8))
    (call $after (i32.const 2) (call $clock_time_get (i32.const 1) (i64.const 1) (i32.const 1024))
      (i32.const 0) (i32.const 1024) (i32.const 8))
    (call $after (i32.const 3) (call $clock_time_get (i32.const 2) (i64.const 1) (i32.const 1024))
      (i32.const 8) (i32.const 1024) (i32.const 8))
    (call $after (i32.const 5) (call $random_get (i32.const 2048) (i32.const 0))
      (i32.const 0) (i32.const 2048) (i32.const 0))
    (call $after (i32.const 6) (call $random_get (i32.const 2049) (i32.const 1))
      (i32.const 0) (i32.const 2049) (i32.const 1))
    (call $after (i32.const 7) (call $random_get (i32.const 2051) (i32.const 1000))
      (i32.const 0) (i32.const 2051) (i32.const 1000))
    ;; args_sizes_get writes the count at 3072 and the size at 3080.
    (if (i32.ne (call $args_sizes_get (i32.const 3072) (i32.const 3080)) (i32.const 0))
      (then (call $fail (i32.const 18))))
    (local.set $count (i32.load (i32.const 3072)))
    (local.set $size (i32.load (i32.const 3080)))
    (call $guard (i32.const 3072) (i32.const 4))
    (call $guard (i32.const 3080) (i32.const 4))
    (if (i32.eqz (call $clean)) (then (call $fail (i32.const 28))))
    (if (i32.or (i32.gt_u (local.get $count) (i32.const 1024))
                (i32.gt_u (local.get $size) (i32.const 32768)))
      (then (call $fail (i32.const 30))))
    (if (i32.ne (call $args_get (i32.const 4096) (i32.const 8192)) (i32.const 0))
      (then (call $fail (i32.const 19))))
    (if (i32.gt_u (local.get $size) (i32.const 0))
      (then
        (if (i32.ne (i32.load8_u (i32.add (i32.const 8191) (local.get $size))) (i32.const 0))
          (then (call $fail (i32.const 31))))))
    (block $pointers_done
      (loop $pointers
        (br_if $pointers_done (i32.ge_u (local.get $index) (local.get $count)))
        (local.set $pointer
          (i32.load (i32.add (i32.const 4096) (i32.mul (local.get $index) (i32.const 4)))))
        (if (i32.or (i32.lt_u (local.get $pointer) (i32.const 8192))
                    (i32.ge_u (local.get $pointer) (i32.add (i32.const 8192) (local.get $size))))
          (then (call $fail (i32.const 32))))
        (local.set $index (i32.add (local.get $index) (i32.const 1)))
        (br $pointers)))
    (local.set $index (i32.const 0))
    (block $zeros_done
      (loop $bytes
        (br_if $zeros_done (i32.ge_u (local.get $index) (local.get $size)))
        (if (i32.eqz (i32.load8_u (i32.add (i32.const 8192) (local.get $index))))
          (then (local.set $zeros (i32.add (local.get $zeros) (i32.const 1)))))
        (local.set $index (i32.add (local.get $index) (i32.const 1)))
        (br $bytes)))
    (if (i32.ne (local.get $zeros) (local.get $count)) (then (call $fail (i32.const 33))))
    (call $guard (i32.const 8192) (local.get $size))
    (call $after (i32.const 9) (i32.const 0) (i32.const 0) (i32.const 4096)
      (i32.mul (local.get $count) (i32.const 4)))
    (call $proc_exit (i32.const 0))))
