#!/usr/bin/env python3
"""Emit the small representation-conversion adapter (not yet formally proved)."""
from pathlib import Path
import sys
Path(sys.argv[1]).write_text('''(module
  (memory (export "memory") 2560 2560)
  ;; Embeddings in binary32 at 0; binary64 staging at 160000000;
  ;; binary32 GPU staging at 161000000. All conversion arithmetic is in Wasm.
  (func (export "embedding") (param $position i64) (param $kind i64)
    (local $i i32) (local $base i32)
    (if (i64.eqz (local.get $kind))
      (then (if (i64.ge_u (local.get $position) (i64.const 50257)) (then unreachable)))
      (else (if (i64.ge_u (local.get $position) (i64.const 128)) (then unreachable))))
    (local.set $base (i32.add (i32.mul (i32.wrap_i64 (local.get $position)) (i32.const 3072))
      (select (i32.const 0) (i32.const 154389504) (i64.eqz (local.get $kind)))))
    (loop $loop
      (f64.store (i32.add (i32.const 160000000) (i32.mul (local.get $i) (i32.const 8)))
        (f64.promote_f32 (f32.load (i32.add (local.get $base) (i32.mul (local.get $i) (i32.const 4))))))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br_if $loop (i32.lt_u (local.get $i) (i32.const 768)))))
  (func (export "convert") (param $direction i64) (param $length i64)
    (local $i i32)
    (if (i64.gt_u (local.get $length) (i64.const 50257)) (then unreachable))
    (if (i64.eqz (local.get $length)) (then return))
    (loop $loop
      (if (i64.eqz (local.get $direction))
        (then (f32.store (i32.add (i32.const 161000000) (i32.mul (local.get $i) (i32.const 4)))
          (f32.demote_f64 (f64.load (i32.add (i32.const 160000000) (i32.mul (local.get $i) (i32.const 8)))))))
        (else (f64.store (i32.add (i32.const 160000000) (i32.mul (local.get $i) (i32.const 8)))
          (f64.promote_f32 (f32.load (i32.add (i32.const 161000000) (i32.mul (local.get $i) (i32.const 4))))))))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br_if $loop (i64.lt_u (i64.extend_i32_u (local.get $i)) (local.get $length))))))
''')
