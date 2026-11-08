import Examples.Convert.Proof
import Verified.Reflect.Command

/-! The verified compiler's module of `toDouble`, `toSingle`, `ofDouble`, `ofSingle`, and `scale`.
The reflector writes each conversion with the word forms of `LeanExe.ProofKit.Signed64Float` over
the unsigned conversions, so the module executes none of `f64.convert_i64_s`, `f32.convert_i64_s`,
`i64.trunc_sat_f64_s`, and `i64.trunc_sat_f32_s`.  The generated theorems `compiled.toDouble.pure`
to `compiled.scale.pure` state that functions 2 to 6 compute the Lean definitions from every store
without a trap and keep the store, and the call theorems compose them with the specifications: each
export returns what those instructions would return. -/

namespace Examples.Convert

open Wasm LeanExe.Pipeline

verified_compile compiled := [toDouble, toSingle, ofDouble, ofSingle, scale]

theorem toDouble_export :
    ({ name := "toDouble", funcIdx := 2 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem scale_export :
    ({ name := "scale", funcIdx := 6 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 2, the export `toDouble`, called with the word of `a` from any store, returns without
a trap the double whose bits are `f64.convert_i64_s` of the word and leaves the store unchanged. -/
theorem toDouble_call (env : HostEnv Unit) (store : Store Unit) (a : Int64) :
    Runs false env compiled.module 2 store [.i64 a.toUInt64] fun final values =>
      final = store ∧ values = [.f64 (expectedToDouble a)] :=
  (compiled.toDouble.pure env store a).mono fun _ values ⟨hs, hv⟩ => by
    refine ⟨hs, ?_⟩
    rw [← toDouble_spec a]
    simpa [Scalar.values, Flat.flat] using congrArg List.reverse hv

/-- Function 3, the export `toSingle`, called with the word of `a` from any store, returns without
a trap the single whose bits are `f32.convert_i64_s` of the word and leaves the store unchanged. -/
theorem toSingle_call (env : HostEnv Unit) (store : Store Unit) (a : Int64) :
    Runs false env compiled.module 3 store [.i64 a.toUInt64] fun final values =>
      final = store ∧ values = [.f32 (expectedToSingle a)] :=
  (compiled.toSingle.pure env store a).mono fun _ values ⟨hs, hv⟩ => by
    refine ⟨hs, ?_⟩
    rw [← toSingle_spec a]
    simpa [Scalar.values, Flat.flat] using congrArg List.reverse hv

/-- Function 4, the export `ofDouble`, called with the bits of `x` from any store, returns without
a trap the word that `i64.trunc_sat_f64_s` gives for `x` and leaves the store unchanged. -/
theorem ofDouble_call (env : HostEnv Unit) (store : Store Unit) (x : Float) :
    Runs false env compiled.module 4 store [.f64 x.toBits] fun final values =>
      final = store ∧ values = [.i64 (expectedOfDouble x)] :=
  (compiled.ofDouble.pure env store x).mono fun _ values ⟨hs, hv⟩ => by
    refine ⟨hs, ?_⟩
    rw [← ofDouble_spec x]
    simpa [Scalar.values, Flat.flat] using congrArg List.reverse hv

/-- Function 5, the export `ofSingle`, called with the bits of `x` from any store, returns without
a trap the word that `i64.trunc_sat_f32_s` gives for `x` and leaves the store unchanged. -/
theorem ofSingle_call (env : HostEnv Unit) (store : Store Unit) (x : Float32) :
    Runs false env compiled.module 5 store [.f32 x.toBits] fun final values =>
      final = store ∧ values = [.i64 (expectedOfSingle x)] :=
  (compiled.ofSingle.pure env store x).mono fun _ values ⟨hs, hv⟩ => by
    refine ⟨hs, ?_⟩
    rw [← ofSingle_spec x]
    simpa [Scalar.values, Flat.flat] using congrArg List.reverse hv

/-- Function 6, the export `scale`, called with the word of `a` and the bits of `k` from any store,
returns without a trap the word that `i64.trunc_sat_f64_s` gives for the product of
`f64.convert_i64_s` of `a`'s word and `k`, and leaves the store unchanged. -/
theorem scale_call (env : HostEnv Unit) (store : Store Unit) (a : Int64) (k : Float) :
    Runs false env compiled.module 6 store [.f64 k.toBits, .i64 a.toUInt64] fun final values =>
      final = store ∧ values = [.i64 (expectedScale a k)] :=
  (compiled.scale.pure env store (a, k)).mono fun _ values ⟨hs, hv⟩ => by
    refine ⟨hs, ?_⟩
    rw [← scale_spec a k]
    simpa [Scalar.values, Flat.flat] using congrArg List.reverse hv

#print axioms compiled.bytes
#print axioms toDouble_call
#print axioms toSingle_call
#print axioms ofDouble_call
#print axioms ofSingle_call
#print axioms scale_call

end Examples.Convert
