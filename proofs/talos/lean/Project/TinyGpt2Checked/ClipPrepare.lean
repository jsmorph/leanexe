import Project.TinyGpt2Checked.ClipAccept
import Project.TinyGpt2Checked.ClipReject
import Project.F64Clip.AllocationState

namespace Project.TinyGpt2Checked.Spec
open Wasm Project.ProofKit Project.Clob Memory Project.F64Clip Project.F64Clip.Spec

theorem prepare_exact (env : HostEnv Unit) (initial : Store Unit)
    (count bound owner ptr base : UInt64) (w : Array UInt64)
    (allocations retains releases frees : UInt64)
    (hGlobals : initial.globals.globals =
      [.i64 base, .i64 0, .i64 allocations, .i64 retains, .i64 releases, .i64 frees])
    (hInput : UInt64Array.At initial ptr w)
    (hBefore : ptr.toNat+8*(w.size+1) ≤ base.toNat)
    (hFit : base.toNat+48+8*(w.size+1) ≤ 4294967296)
    (hMemory : base.toNat+48+8*(w.size+1) ≤ initial.mem.pages*65536)
    (hPages : initial.mem.pages ≤ 65536)
    (hCap : initial.mem.pages ≤ initial.memoryCap Project.TinyGpt2Checked.module 0) :
    TerminatesWith env Project.TinyGpt2Checked.module 6 initial [.i64 ptr, .i64 owner, .i64 bound, .i64 count]
      (fun final values => values = [.i64 (base+48), .i64 (base+48)] ∧
        UInt64Array.At final (base+48) (prepare count.toNat bound w) ∧
        UInt64Array.At final ptr w ∧ final.mem.pages = initial.mem.pages ∧
        Memory.WritesRange
          (clipInitialize initial base (prepare count.toNat bound w).size allocations) final
          (base+48).toNat ((base+48).toNat+8*((prepare count.toNat bound w).size+1))) := by
  refine TerminatesWith.of_wp_entry_for (f := func6Def) rfl ?_ (by decide)
  change wp Project.TinyGpt2Checked.module func6 _ initial
    (func6Def.toLocals [.i64 count, .i64 bound, .i64 owner, .i64 ptr]) env
  rw [prepare_shape]
  simp only [func6, List.take, List.cons_append, List.nil_append]
  wp_fixed_frame [func6Def]
  refine wp_call_tw (accepted_exact env initial count bound owner ptr w hInput) ?_
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
  · refine reject_program_spec env initial count bound owner ptr base w allocations retains releases frees
      hGlobals hInput hBefore (by omega) (by omega) hPages hCap _ [] ?_
    rintro final frame ⟨hOwner, hRoot, hValues, hOutput, hPreserved, hFinalPages, hWrites⟩
    simp [wp_simp, prepare, ha, hOutput, hPreserved, hFinalPages]
    change (match frame.get 15 with
      | some v => match frame.get 16 with | some v' => _ | none => False
      | none => False)
    rw [hOwner, hRoot]
    exact ⟨⟨rfl, rfl⟩, by simpa using hWrites⟩
  · refine accept_program_spec env initial count bound owner ptr base w allocations retains releases frees
      hGlobals hInput hBefore hFit hMemory hPages hCap _ [] ?_
    rintro final frame ⟨hOwner, hRoot, hValues, hOutput, hPreserved, hFinalPages, hWrites⟩
    simp [wp_simp, prepare, ha, hOutput, hPreserved, hFinalPages]
    change (match frame.get 15 with
      | some v => match frame.get 16 with | some v' => _ | none => False
      | none => False)
    rw [hOwner, hRoot]
    exact ⟨⟨rfl, rfl⟩, by simpa using hWrites⟩

theorem prepare_state (env : HostEnv Unit) (initial : Store Unit)
    (count bound owner ptr base : UInt64) (w : Array UInt64)
    (allocations retains releases frees : UInt64)
    (hGlobals : initial.globals.globals =
      [.i64 base, .i64 0, .i64 allocations, .i64 retains, .i64 releases, .i64 frees])
    (hInput : UInt64Array.At initial ptr w)
    (hBefore : ptr.toNat+8*(w.size+1) ≤ base.toNat)
    (hFit : base.toNat+48+8*(w.size+1) ≤ 4294967296)
    (hMemory : base.toNat+48+8*(w.size+1) ≤ initial.mem.pages*65536)
    (hPages : initial.mem.pages ≤ 65536)
    (hCap : initial.mem.pages ≤ initial.memoryCap Project.TinyGpt2Checked.module 0) :
    TerminatesWith env Project.TinyGpt2Checked.module 6 initial [.i64 ptr, .i64 owner, .i64 bound, .i64 count]
      (fun final values =>
        let output := prepare count.toNat bound w
        values = [.i64 (base+48), .i64 (base+48)] ∧ UInt64Array.At final (base+48) output ∧
        UInt64Array.At final ptr w ∧ final.mem.pages = initial.mem.pages ∧
        final.globals.globals =
          [.i64 (base+48+clipCapacity output.size), .i64 0, .i64 (allocations+1),
            .i64 retains, .i64 releases, .i64 frees] ∧
        FreshFixedArrayAt final (base+48) (clipCapacity output.size) 1 ∧
        (∀ address : Nat, address < base.toNat → final.mem.bytes address = initial.mem.bytes address) ∧
        final = { initial with mem := final.mem, globals := final.globals }) := by
  refine TerminatesWith.mono (prepare_exact env initial count bound owner ptr base w
    allocations retains releases frees hGlobals hInput hBefore hFit hMemory hPages hCap) ?_
  rintro final values ⟨hValues, hOutput, hInput', hPages', hWrites⟩
  let output := prepare count.toNat bound w
  have hSize : output.size ≤ w.size := by simp [output, prepare]; split <;> simp
  have hFit' : base.toNat+48+8*(output.size+1) ≤ 4294967296 := by omega
  have hMemory' : base.toNat+48+8*(output.size+1) ≤ initial.mem.pages*65536 := by omega
  exact ⟨hValues, hOutput, hInput', hPages',
    clip_result_state initial final base output.size allocations retains releases frees
      hGlobals hFit' hMemory' hWrites⟩

#print axioms prepare_exact
#print axioms prepare_state
end Project.TinyGpt2Checked.Spec
