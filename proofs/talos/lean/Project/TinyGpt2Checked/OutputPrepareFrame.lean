import Project.TinyGpt2Checked.OutputPrepareExec
import Project.TinyGpt2Checked.OutputFrame

namespace Project.TinyGpt2Checked.Spec
open Project.TinyGpt2Infer
open Wasm Project.TinyGpt2 Project.Runtime Project.ProofKit ArrayPushLayout FixedArrayFold

theorem output_prepare_frame_spec (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (owner pointer empty : UInt64) (x : Row) (start count : Nat)
    (allocations retains releases frees : UInt64)
    (hSaved : OutputSaved owner pointer empty x frame)
    (hGlobals : initial.globals.globals = OutputMemory.globals start count allocations retains releases frees)
    (hList : FreeListAt initial.mem (freed start count))
    (hFit : top start (count + 1) < 4294967296)
    (hMemory : top start (count + 1) ≤ initial.mem.pages * 65536)
    (hPages : initial.mem.pages ≤ 65536)
    (hCap : initial.mem.pages ≤ initial.memoryCap module 0)
    (hLength : frame.get 55 = some (.i64 (UInt64.ofNat (count + 1))))
    (hNeed : frame.get 61 = some (.i64 (UInt64.ofNat (capacity (count + 1)))))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ finalFrame : Locals, OutputSaved owner pointer empty x finalFrame →
      finalFrame.get 56 = some (.i64 (node start (count + 1)).root) →
      (∀ index : Nat, index ≠ 56 → (index < 61 ∨ 67 ≤ index) →
        finalFrame.get index = frame.get index) →
      wp module rest Q (OutputMemory.prepare initial start (count + 1) allocations) finalFrame env) :
    wp module ((outputBody.drop 67).take 21 ++ rest) Q initial frame env := by
  let params := frame.params
  let saved := frame.locals.take 55
  let tail := frame.locals.drop 61
  have hStart : params.length + saved.length = 61 := by
    simp [params, saved, hSaved.params, hSaved.locals]
  obtain ⟨need, previous, current, capacity', next, result, hFrame⟩ :=
    hSaved.scratch.window 55 (by rw [hSaved.params])
      (by rw [hSaved.params]) (by rw [hSaved.locals]; decide) hSaved.values
  change frame = FixedArraySearch.frame params saved tail need previous current capacity' next result at hFrame
  have hRead := FixedArraySearch.frame_get params saved tail need previous current capacity' next result
    0 (by decide)
  have hNeedEq : need = UInt64.ofNat (capacity (count + 1)) := by
    rw [hFrame] at hNeed
    simpa only [hStart, Nat.add_zero, List.getElem?_cons_zero, hNeed,
      Option.some.injEq, Value.i64.injEq] using hRead.symm
  subst need
  have hCanonical : OutputSaved owner pointer empty x
      (FixedArraySearch.frame params saved tail (UInt64.ofNat (capacity (count + 1)))
        previous current capacity' next result) := hFrame ▸ hSaved
  conv_lhs => rw [hFrame]
  apply output_prepare_spec env initial params saved tail hSaved.params hStart start count
    allocations retains releases frees previous current capacity' next result
    hGlobals hList hFit hMemory hPages hCap
    (by rw [← hFrame]; exact hLength)
  intro previous'
  let allocated := TinyGpt2Infer.Spec.outputAllocationFrame params saved tail start count previous'
  have hAllocated : OutputSaved owner pointer empty x allocated :=
    hCanonical.search params saved tail _ _ _ _ _ _ hStart _ _ _ _ _ _
  apply hNext (resultFrame allocated 56 (node start (count + 1)).root)
    (hAllocated.result 56 _ (by decide) (by decide) (by decide))
    (resultFrame_get_result allocated 56 _ (by rw [hAllocated.params]; decide)
      (hAllocated.valid 56 (by decide)))
  intro index hIndex hOutside
  rw [resultFrame_get_ne allocated 56 index _ (by rw [hAllocated.params]; decide) hIndex]
  change (FixedArraySearch.frame params saved tail _ _ _ _ _ _).get index = _
  rw [FixedArraySearch.frame_get_outside params saved tail
    (UInt64.ofNat (capacity (count + 1))) previous current capacity' next result
    _ _ _ _ _ _ index (by simpa only [hStart] using hOutside), ← hFrame]

#print axioms output_prepare_frame_spec
end Project.TinyGpt2Checked.Spec
