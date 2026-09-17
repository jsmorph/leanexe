import Project.F64Clip.Array
import Project.F64Clip.Prepare
import Project.F64Clip.AnnotationMatches

namespace Project.F64Clip.Spec
open Wasm CodeLib.IEEE64

theorem clip_real (env : HostEnv Unit) (initial : Store Unit) (bound x : UInt64)
    (hb : validBound bound = true) (hx : Finite x) :
    TerminatesWith env Project.F64Clip.module 5 initial [.i64 x, .i64 bound]
      (fun final values => final = initial ∧ ∃ output : UInt64, values = [.i64 output] ∧
        Finite output ∧ |value output| ≤ value bound ∧
        value output = max (-value bound) (min (value bound) (value x))) := by
  have hBound := (validBound_iff bound).mp hb
  refine TerminatesWith.mono (clip_exact env initial bound x) ?_
  rintro final values ⟨rfl, rfl⟩
  have hc := clip_bounded bound x hBound.1 hBound.2.1 hx
  exact ⟨rfl, clip bound x, rfl, hc.1, hc.2, clip_value bound x hBound.1 hBound.2.1 hx⟩

#print axioms clip_real

theorem prepare_real (env : HostEnv Unit) (initial : Store Unit)
    (count bound ptr base : UInt64) (w : Array UInt64)
    (allocations retains releases frees : UInt64)
    (hGlobals : initial.globals.globals =
      [.i64 base, .i64 0, .i64 allocations, .i64 retains, .i64 releases, .i64 frees])
    (hInput : Project.ProofKit.UInt64Array.At initial ptr w)
    (hBefore : ptr.toNat+8*(w.size+1) ≤ base.toNat)
    (hFit : base.toNat+48+8*(w.size+1) ≤ 4294967296)
    (hMemory : base.toNat+48+8*(w.size+1) ≤ initial.mem.pages*65536)
    (hPages : initial.mem.pages ≤ 65536)
    (hCap : initial.mem.pages ≤ initial.memoryCap Project.F64Clip.module 0)
    (ha : accepted count.toNat bound w = true) :
    TerminatesWith env Project.F64Clip.module 6 initial [.i64 ptr, .i64 bound, .i64 count]
      (fun final values => ∃ output : Array UInt64,
        values = [.i64 (base+48)] ∧ Project.ProofKit.UInt64Array.At final (base+48) output ∧
        output.size = count.toNat ∧
        (∀ (i : Nat), i < w.size → Finite output[i]! ∧ |value output[i]!| ≤ value bound ∧
          value output[i]! = max (-value bound) (min (value bound) (value w[i]!))) ∧
        Project.ProofKit.UInt64Array.At final ptr w ∧ final.mem.pages = initial.mem.pages) := by
  refine TerminatesWith.mono (prepare_exact env initial count bound ptr base w
    allocations retains releases frees hGlobals hInput hBefore hFit hMemory hPages hCap) ?_
  rintro final values ⟨hValues, hOutput, hPreserved, hFinalPages⟩
  exact ⟨prepare count.toNat bound w, hValues, hOutput, prepare_size count.toNat bound w ha,
    prepare_element count.toNat bound w ha, hPreserved, hFinalPages⟩

#print axioms prepare_real
end Project.F64Clip.Spec
