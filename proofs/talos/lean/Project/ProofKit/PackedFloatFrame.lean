import Project.ProofKit.Frame

namespace Project.ProofKit.PackedFloatFrame

open Wasm

theorem wrap_extend (word : UInt32) :
    UInt32.ofNat (word.toUInt64.toNat % 2^32) = word := by simp

theorem mask (word : UInt32) : word.toUInt64 &&& 4294967295 = word.toUInt64 := by
  apply UInt64.toNat.inj
  simp only [UInt64.toNat_and, UInt32.toNat_toUInt64]
  change word.toNat &&& (2^32 - 1) = word.toNat
  exact Nat.and_two_pow_sub_one_of_lt_two_pow word.toNat_lt

theorem widen_and (left right : UInt32) :
    left.toUInt64 &&& right.toUInt64 = (left &&& right).toUInt64 := by
  apply UInt64.toNat.inj
  simp only [UInt64.toNat_and, UInt32.toNat_and, UInt32.toNat_toUInt64]

theorem widen_or (left right : UInt32) :
    left.toUInt64 ||| right.toUInt64 = (left ||| right).toUInt64 := by
  apply UInt64.toNat.inj
  simp only [UInt64.toNat_or, UInt32.toNat_or, UInt32.toNat_toUInt64]

theorem widen_lt (left right : UInt32) : left.toUInt64 < right.toUInt64 ↔ left < right := by
  simp only [UInt64.lt_iff_toNat_lt, UInt32.lt_iff_toNat_lt, UInt32.toNat_toUInt64]

theorem narrow_byte (word : UInt32) : word.toUInt64 &&& 255 = word.toUInt8.toUInt64 := by
  apply UInt64.toNat.inj
  simp only [UInt64.toNat_and, UInt32.toNat_toUInt64, UInt8.toNat_toUInt64,
    UInt32.toNat_toUInt8]
  exact Nat.and_two_pow_sub_one_eq_mod word.toNat 8

theorem mask32_eq_mod (word : UInt64) : word &&& 4294967295 = word % 4294967296 := by
  apply UInt64.toNat.inj
  simp only [UInt64.toNat_and, UInt64.toNat_mod]
  exact Nat.and_two_pow_sub_one_eq_mod word.toNat 32

theorem widen_add (left right : UInt32) :
    (left.toUInt64 + right.toUInt64) &&& 4294967295 = (left + right).toUInt64 := by
  rw [mask32_eq_mod, UInt32.toUInt64_add]

theorem widen_mul (left right : UInt32) :
    (left.toUInt64 * right.toUInt64) &&& 4294967295 = (left * right).toUInt64 := by
  rw [mask32_eq_mod, UInt32.toUInt64_mul]

syntax (name := wpPackedFrame) "wp_packed_frame" (Lean.Parser.Tactic.simpArgs)? : tactic

macro_rules
  | `(tactic| wp_packed_frame $[[$args,*]]?) => do
    let extra := args.map (·.getElems) |>.getD #[]
    `(tactic| wp_run [Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff,
      reduceIte, List.length_set, List.getElem?_set, List.nil_append, List.cons_append,
      UInt64.ofNat_uInt32ToNat, wrap_extend, mask, Wasm.f32Add, Wasm.f32Sub,
      Wasm.f32Mul, Wasm.f32Div, Wasm.f32Sqrt, $extra,*])

end Project.ProofKit.PackedFloatFrame
