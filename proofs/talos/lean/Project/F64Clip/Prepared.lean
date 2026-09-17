import Project.F64Clip.Prepare
import Project.F64Clip.AllocationState

namespace Project.F64Clip.Spec
open Wasm Project.ProofKit Project.Clob Memory

theorem prepare_state (env : HostEnv Unit) (initial : Store Unit)
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
      (fun final values =>
        let output := prepare count.toNat bound w
        values = [.i64 (base+48)] ∧ UInt64Array.At final (base+48) output ∧
        UInt64Array.At final ptr w ∧ final.mem.pages = initial.mem.pages ∧
        final.globals.globals =
          [.i64 (base+48+clipCapacity output.size), .i64 0, .i64 (allocations+1),
            .i64 retains, .i64 releases, .i64 frees] ∧
        FreshFixedArrayAt final (base+48) (clipCapacity output.size) 1 ∧
        (∀ address : Nat, address < base.toNat → final.mem.bytes address = initial.mem.bytes address) ∧
        final = { initial with mem := final.mem, globals := final.globals }) := by
  refine TerminatesWith.mono (prepare_exact env initial count bound ptr base w
    allocations retains releases frees hGlobals hInput hBefore hFit hMemory hPages hCap) ?_
  rintro final values ⟨hValues, hOutput, hInput', hPages', hWrites⟩
  let output := prepare count.toNat bound w
  have hSize : output.size ≤ w.size := by simp [output, prepare]; split <;> simp
  have hFit' : base.toNat+48+8*(output.size+1) ≤ 4294967296 := by omega
  have hMemory' : base.toNat+48+8*(output.size+1) ≤ initial.mem.pages*65536 := by omega
  exact ⟨hValues, hOutput, hInput', hPages',
    clip_result_state initial final base output.size allocations retains releases frees
      hGlobals hFit' hMemory' hWrites⟩

#print axioms prepare_state
end Project.F64Clip.Spec
