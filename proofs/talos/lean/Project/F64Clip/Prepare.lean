import Project.F64Clip.Accept
import Project.F64Clip.Reject
import Project.F64Clip.Validation

namespace Project.F64Clip.Spec
open Wasm Project.ProofKit

theorem prepare_exact (env : HostEnv Unit) (initial : Store Unit)
    (count bound ptr base : UInt64) (w : Array UInt64)
    (allocations retains releases frees : UInt64)
    (hGlobals : initial.globals.globals =
      [.i64 base, .i64 0, .i64 allocations, .i64 retains, .i64 releases, .i64 frees])
    (hInput : UInt64Array.At initial ptr w)
    (hBefore : ptr.toNat+8*(w.size+1) ≤ base.toNat)
    (hFit : base.toNat+48+8*(w.size+1) ≤ 4294967296)
    (hMemory : base.toNat+48+8*(w.size+1) ≤ initial.mem.pages*65536)
    (hPages : initial.mem.pages ≤ 65536)
    (hCap : initial.mem.pages ≤ initial.memoryCap Project.F64Clip.module 0) :
    TerminatesWith env Project.F64Clip.module 6 initial [.i64 ptr, .i64 bound, .i64 count]
      (fun final values => values = [.i64 (base+48)] ∧
        UInt64Array.At final (base+48) (prepare count.toNat bound w) ∧
        UInt64Array.At final ptr w ∧ final.mem.pages = initial.mem.pages ∧
        Memory.WritesRange
          (clipInitialize initial base (prepare count.toNat bound w).size allocations) final
          (base+48).toNat ((base+48).toNat+8*((prepare count.toNat bound w).size+1))) := by
  refine TerminatesWith.of_wp_entry_for (f := func6Def) rfl ?_ (by decide)
  change wp Project.F64Clip.module func6 _ initial
    (func6Def.toLocals [.i64 count, .i64 bound, .i64 ptr]) env
  rw [prepare_shape]
  simp only [func6, List.take, List.cons_append, List.nil_append]
  wp_fixed_frame [func6Def]
  refine wp_call_tw (accepted_exact env initial count bound 0 ptr w hInput) ?_
  rintro checked values ⟨hChecked, rfl⟩
  subst checked
  cases ha : accepted count.toNat bound w
  all_goals
    wp_fixed_frame [ha]
    try simp only [wp_iff_control_types]
    refine wp_iff_cons rfl ?_
    simp [show (1 : UInt32) ≠ 0 by decide]
    refine wp_iff_cons rfl ?_
    simp [show (1 : UInt32) ≠ 0 by decide]
  · refine reject_program_spec env initial count bound ptr base w allocations retains releases frees
      hGlobals hInput hBefore (by omega) (by omega) hPages hCap _ [] ?_
    rintro final frame ⟨hRoot, hValues, hOutput, hPreserved, hFinalPages, hWrites⟩
    simp [wp_simp, prepare, ha, hOutput, hPreserved, hFinalPages]
    change (match frame.get 15 with | some v => v = .i64 (base+48) ∧ _ | none => False)
    rw [hRoot]
    exact ⟨rfl, by simpa using hWrites⟩
  · refine accept_program_spec env initial count bound ptr base w allocations retains releases frees
      hGlobals hInput hBefore hFit hMemory hPages hCap _ [] ?_
    rintro final frame ⟨hRoot, hValues, hOutput, hPreserved, hFinalPages, hWrites⟩
    simp [wp_simp, prepare, ha, hOutput, hPreserved, hFinalPages]
    change (match frame.get 15 with | some v => v = .i64 (base+48) ∧ _ | none => False)
    rw [hRoot]
    exact ⟨rfl, by simpa using hWrites⟩

#print axioms prepare_exact
end Project.F64Clip.Spec
