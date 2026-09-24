import Project.TinyGpt2Checked.InitialPrefix
import Project.TinyGpt2Infer.OutputAllocation

namespace Project.TinyGpt2Checked.Spec
open Project.TinyGpt2Infer
open Wasm Project.TinyGpt2 Project.Runtime Project.ProofKit ArrayPushLayout

def initialAllocatedFrame (owner pointer t0 t1 t2 t3 : UInt64) (x : Row) (start : Nat)
    (previous : UInt64) : Locals :=
  initialAllocationFrame owner pointer t0 t1 t2 t3 x 8 previous 0
    (UInt64.ofNat (top start 0)) ((UInt64.ofNat (top start 0) - 1) / 65536 + 1)
    (node start 0).root

theorem initial_allocation_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner pointer t0 t1 t2 t3 : UInt64) (x : Row) (start : Nat)
    (allocations retains releases frees : UInt64)
    (hGlobals : initial.globals.globals =
      [.i64 (UInt64.ofNat start), .i64 0, .i64 allocations, .i64 retains, .i64 releases, .i64 frees])
    (hFit : top start 0 < 4294967296)
    (hMemory : top start 0 ≤ initial.mem.pages * 65536)
    (hPages : initial.mem.pages ≤ 65536)
    (hCap : initial.mem.pages ≤ initial.memoryCap module 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previous : UInt64, wp module rest Q (OutputMemory.allocate initial start 0 allocations)
      (initialAllocatedFrame owner pointer t0 t1 t2 t3 x start previous) env) :
    wp module ((func84.drop 52).take 15 ++ rest) Q initial
      (initialAllocationFrame owner pointer t0 t1 t2 t3 x 8 0 0 0 0 0) env := by
  have hWords := OutputMemory.allocation_words start 0 hFit
  have hPagesNeeded : FixedArrayBump.requiredPages (UInt64.ofNat (base start 0)) 8 ≤ initial.mem.pages := by
    unfold FixedArrayBump.requiredPages
    rw [hWords.1]
    change base start 0 + 48 + 8 ≤ initial.mem.pages * 65536 at hMemory
    change (base start 0 + 48 + 8 - 1) / 65536 + 1 ≤ initial.mem.pages
    omega
  rw [initial_allocation_shape]
  apply FixedArrayAllocateNone.program_spec module env initial
    (inferenceParams owner pointer t0 t1 t2 t3) (inferenceSaved owner pointer t0 t1 t2 t3 x)
    (List.replicate 13 (.i64 0)) 55 (by simp [inferenceParams, inferenceSaved])
    (FixedArrayReuse.program 55 1) (UInt64.ofNat (base start 0)) 8 1 0 0 0 0 0 allocations []
  · simpa [hGlobals, base]
  · simp [hGlobals, freeHead]
  · simp [hGlobals]
  · exact .nil
  · rfl
  · rw [hWords.1]
    exact hFit.le
  · exact hPages
  · rfl
  · exact hPagesNeeded.trans hCap
  · intro previous
    change wp module rest Q _
      (initialAllocationFrame owner pointer t0 t1 t2 t3 x 8 previous 0
        (UInt64.ofNat (base start 0) + 48 + UInt64.ofNat (capacity 0))
        ((UInt64.ofNat (base start 0) + 48 + UInt64.ofNat (capacity 0) - 1) / 65536 + 1)
        (UInt64.ofNat (base start 0) + 48)) env
    rw [OutputMemory.allocation_top_word, OutputMemory.allocation_root_word]
    exact hNext previous

#print axioms initial_allocation_spec
end Project.TinyGpt2Checked.Spec
