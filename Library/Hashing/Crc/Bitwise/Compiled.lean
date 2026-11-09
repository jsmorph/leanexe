import Library.Hashing.Crc.Bitwise.Proof
import Verified.Reflect.Command

/-! The verified compiler's module of the bitwise CRC-32, `crcBitwise`.  The functions use no
linear memory, so the generated `compiled.f.pure` of each states that the function computes its
Lean definition from every store without a trap and keeps the store, and the call theorems compose
it with the equalities of `Library.Hashing.Crc.Bitwise.Proof`. -/

namespace Library.Hashing.Crc.Bitwise

open Wasm LeanExe.Pipeline

verified_compile compiled := [crc32Reg, crc32Byte, crc32Word]

theorem crc32Reg_export :
    ({ name := "crc32Reg", funcIdx := 2 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem crc32Byte_export :
    ({ name := "crc32Byte", funcIdx := 3 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem crc32Word_export :
    ({ name := "crc32Word", funcIdx := 4 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 2, the export `crc32Reg`, called with the register `r` and the word `b` from any
store, returns without a trap the register of the table program's step `byteStep crc32Table r b`
and leaves the store unchanged. -/
theorem crc32Reg_call (env : HostEnv Unit) (store : Store Unit) (r b : UInt64) :
    Runs false env compiled.module 2 store [.i64 b, .i64 r] fun final values =>
      final = store ∧ values = [.i64 (byteStep crc32Table r b)] :=
  (compiled.crc32Reg.pure env store (r, b)).mono fun _ values ⟨hs, hv⟩ => by
    refine ⟨hs, ?_⟩
    rw [← crc32Reg_eq r b]
    simpa [Scalar.values] using congrArg List.reverse hv

/-- Function 3, the export `crc32Byte`, called with the words `crc` and `b` from any store, returns
without a trap `crc32Update crc #[b] 1`, the CRC-32 that continues from `crc` with the low byte of
`b`, and leaves the store unchanged. -/
theorem crc32Byte_call (env : HostEnv Unit) (store : Store Unit) (crc b : UInt64) :
    Runs false env compiled.module 3 store [.i64 b, .i64 crc] fun final values =>
      final = store ∧ values = [.i64 (crc32Update crc #[b] 1)] :=
  (compiled.crc32Byte.pure env store (crc, b)).mono fun _ values ⟨hs, hv⟩ => by
    refine ⟨hs, ?_⟩
    rw [← crc32Byte_eq crc b]
    simpa [Scalar.values] using congrArg List.reverse hv

/-- Function 4, the export `crc32Word`, called with the words `crc`, `w`, and `n` from any store,
returns without a trap `crc32Update crc #[Words.bswap w] (min n 8)`, the CRC-32 that continues
from `crc` with the first `n` bytes of `w`, at most eight, from the most significant, and leaves
the store unchanged. -/
theorem crc32Word_call (env : HostEnv Unit) (store : Store Unit) (crc w n : UInt64) :
    Runs false env compiled.module 4 store [.i64 n, .i64 w, .i64 crc] fun final values =>
      final = store ∧ values = [.i64 (crc32Update crc #[Words.bswap w] (min n 8))] :=
  (compiled.crc32Word.pure env store (crc, w, n)).mono fun _ values ⟨hs, hv⟩ => by
    refine ⟨hs, ?_⟩
    rw [← crc32Word_eq crc w n]
    simpa [Scalar.values] using congrArg List.reverse hv

#print axioms crc32Reg_eq
#print axioms crc32Byte_eq
#print axioms crc32Word_eq
#print axioms crc32Byte_spec
#print axioms crc32Word_spec
#print axioms crc32Reg_call
#print axioms crc32Byte_call
#print axioms crc32Word_call

end Library.Hashing.Crc.Bitwise
