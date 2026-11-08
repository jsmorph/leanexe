import Examples.Floor.Proof
import Verified.Reflect.Command

/-! The verified compiler's module of `floorDiv`, `average`, and `clamp`.  The generated
`compiled.floorDiv.pure`, `compiled.average.pure`, and `compiled.clamp.pure` state that functions 2,
3, and 4 compute the Lean definitions from every store without a trap and keep the store, each
`Int64` passed and returned as its word.  `floorDiv_call`, `average_call`, and `clamp_call` compose
them with the specifications. -/

namespace Examples.Floor

open Wasm LeanExe.Pipeline

verified_compile compiled := [floorDiv, average, clamp]

theorem floorDiv_export :
    ({ name := "floorDiv", funcIdx := 2 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem average_export :
    ({ name := "average", funcIdx := 3 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 2, the export `floorDiv`, called with the words of `a` and of a nonzero `b`, other
than `minValue` by -1, from any store, returns without a trap the word of the `Int64` whose integer
is `Int.fdiv a.toInt b.toInt` and leaves the store unchanged. -/
theorem floorDiv_call (env : HostEnv Unit) (store : Store Unit) (a b : Int64) (hb : b ≠ 0)
    (ho : ¬(a = Int64.minValue ∧ b = -1)) :
    Runs false env compiled.module 2 store [.i64 b.toUInt64, .i64 a.toUInt64] fun final values =>
      final = store ∧ ∃ w : UInt64, values = [.i64 w] ∧ w.toInt64.toInt = expectedDiv a b :=
  (compiled.floorDiv.pure env store (a, b)).mono fun _ values ⟨hs, hv⟩ => by
    refine ⟨hs, (floorDiv a b).toUInt64, ?_, floorDiv_spec a b hb ho⟩
    simpa [Scalar.values, Flat.flat] using congrArg List.reverse hv

/-- Function 3, the export `average`, called with the words of `a` and `b` from any store,
returns without a trap the word of the `Int64` whose integer is the floor of the mean of `a` and
`b` and leaves the store unchanged. -/
theorem average_call (env : HostEnv Unit) (store : Store Unit) (a b : Int64) :
    Runs false env compiled.module 3 store [.i64 b.toUInt64, .i64 a.toUInt64] fun final values =>
      final = store ∧ ∃ w : UInt64, values = [.i64 w] ∧
        w.toInt64.toInt = expectedAverage a b :=
  (compiled.average.pure env store (a, b)).mono fun _ values ⟨hs, hv⟩ => by
    refine ⟨hs, (average a b).toUInt64, ?_, average_spec a b⟩
    simpa [Scalar.values, Flat.flat] using congrArg List.reverse hv

/-- Function 4, the export `clamp`, called with the words of `x`, `lo`, and `hi` from any store,
returns without a trap the word of the `Int64` whose integer is `x` bounded by `lo` and `hi` and
leaves the store unchanged. -/
theorem clamp_call (env : HostEnv Unit) (store : Store Unit) (x lo hi : Int64) :
    Runs false env compiled.module 4 store [.i64 hi.toUInt64, .i64 lo.toUInt64, .i64 x.toUInt64]
      fun final values => final = store ∧ ∃ w : UInt64, values = [.i64 w] ∧
        w.toInt64.toInt = expectedClamp x lo hi :=
  (compiled.clamp.pure env store (x, lo, hi)).mono fun _ values ⟨hs, hv⟩ => by
    refine ⟨hs, (clamp x lo hi).toUInt64, ?_, clamp_spec x lo hi⟩
    simpa [Scalar.values, Flat.flat] using congrArg List.reverse hv

#print axioms compiled.bytes
#print axioms floorDiv_call
#print axioms average_call
#print axioms clamp_call

end Examples.Floor
