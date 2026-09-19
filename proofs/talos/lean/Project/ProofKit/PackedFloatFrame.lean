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

syntax (name := wpPackedFrame) "wp_packed_frame" (Lean.Parser.Tactic.simpArgs)? : tactic

macro_rules
  | `(tactic| wp_packed_frame $[[$args,*]]?) => do
    let extra := args.map (·.getElems) |>.getD #[]
    `(tactic| wp_run [Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff,
      reduceIte, List.length_set, List.getElem?_set, List.nil_append, List.cons_append,
      UInt64.ofNat_uInt32ToNat, wrap_extend, mask, Wasm.f32Add, Wasm.f32Sub,
      Wasm.f32Mul, Wasm.f32Div, Wasm.f32Sqrt, $extra,*])

end Project.ProofKit.PackedFloatFrame
