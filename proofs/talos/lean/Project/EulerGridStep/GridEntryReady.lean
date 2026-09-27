import Project.EulerGridStep.GridInitialFacts

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- Explicit initial memory/counter assumptions for the exact exported grid function. -/
structure GridEntryReady (initial : Store Unit) (pointer : UInt64) (input : Array UInt64)
    (base : Nat) (allocs releases frees : UInt64) : Prop where
  inputAt : UInt64Array.At initial pointer input
  pages : initial.mem.pages ≤ 65536
  budget : base + (input.size / 3 + 6) * arenaObjectSize (1 + 6 * (input.size / 3)) ≤ initial.mem.pages * 65536
  heap : initial.globals.globals[0]? = some (.i64 (arenaHeap base (1 + 6 * (input.size / 3)) 0))
  freeHead : initial.globals.globals[1]? = some (.i64 0)
  allocations : initial.globals.globals[2]? = some (.i64 allocs)
  releases : initial.globals.globals[4]? = some (.i64 releases)
  frees : initial.globals.globals[5]? = some (.i64 frees)
  separate : ∀ slot < input.size / 3 + 6,
    ObjectsSeparate (arenaRoot base (1 + 6 * (input.size / 3)) slot) (1 + 6 * (input.size / 3)) pointer input.size

theorem GridEntryReady.invalid_fit {initial : Store Unit} {pointer : UInt64} {input : Array UInt64}
    {base : Nat} {allocs releases frees : UInt64} (h : GridEntryReady initial pointer input base allocs releases frees) :
    (arenaHeap base (1 + 6 * (input.size / 3)) 0).toNat + 48 + 16 ≤ initial.mem.pages * 65536 := by
  have hBudget := h.budget
  have hPages := h.pages
  have hBudget32 : base + (input.size / 3 + 6) * arenaObjectSize (1 + 6 * (input.size / 3)) ≤ 4294967296 := by omega
  have hFit := arena_slot_fit_of_lt base (1 + 6 * (input.size / 3)) 0 (input.size / 3 + 6)
    (initial.mem.pages * 65536) (by omega) hBudget
  rw [arena_heap_toNat_of_le base (1 + 6 * (input.size / 3)) 0 (input.size / 3 + 6) (by omega) hBudget32]
  omega

#print axioms GridEntryReady.invalid_fit
end Project.EulerGridStep.Execution
