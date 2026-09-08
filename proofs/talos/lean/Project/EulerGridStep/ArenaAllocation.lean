import Project.EulerGridStep.ArenaLayout

namespace Project.EulerGridStep.Execution
open Wasm

/-- A bounded unused arena slot supplies every fresh-clone allocation precondition. -/
theorem arena_fresh_valid (current : Store Unit) (base count slot previous : Nat) (allocs : UInt64)
    (input : Array UInt64) (hSize : input.size = count) (hSlot : slot ≤ 6) (hPrevious : previous ≤ 6)
    (hDistinct : previous ≠ slot)
    (hBudget : base + 7 * arenaObjectSize count ≤ current.mem.pages * 65536)
    (hPages : current.mem.pages ≤ 65536)
    (hHeap : current.globals.globals[0]? = some (.i64 (arenaHeap base count slot)))
    (hFree : current.globals.globals[1]? = some (.i64 0))
    (hAllocs : current.globals.globals[2]? = some (.i64 allocs)) :
    (FieldAllocation.fresh (arenaHeap base count slot) allocs).Valid
      current (arenaRoot base count previous) input := by
  subst count
  have hBudget32 : base + 7 * arenaObjectSize input.size ≤ 4294967296 := by omega
  have hFit32 := arena_slot_fit base input.size slot 4294967296 hSlot hBudget32
  have hFitMemory := arena_slot_fit base input.size slot (current.mem.pages * 65536) hSlot hBudget
  have hHeapNat := arena_heap_toNat base input.size slot (by omega) hBudget32
  have hRootNat : (arenaHeap base input.size slot + 48).toNat =
      base + slot * arenaObjectSize input.size + 48 := by
    rw [← arena_root_eq_heap]
    exact arena_root_toNat base input.size slot hSlot hBudget32
  have hRequestNat : (fieldRequest input.size).toNat = 8 * (input.size + 1) :=
    UInt64.toNat_ofNat_of_lt' (by change 8 * (input.size + 1) < 18446744073709551616; omega)
  refine ⟨⟨?_, hHeap, hFree, hAllocs⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hHeapNat]
    omega
  · change 48 ≤ (arenaHeap base input.size slot + 48).toNat
    rw [hRootNat]
    omega
  · change (arenaHeap base input.size slot + 48).toNat < 4294967296
    rw [hRootNat]
    omega
  · change 8 * (input.size + 1) ≤ (fieldRequest input.size).toNat
    rw [hRequestNat]
  · change (arenaHeap base input.size slot + 48).toNat + (fieldRequest input.size).toNat ≤ 4294967296
    rw [hRootNat, hRequestNat]
    exact hFit32
  · change (arenaHeap base input.size slot + 48).toNat + (fieldRequest input.size).toNat ≤ current.mem.pages * 65536
    rw [hRootNat, hRequestNat]
    exact hFitMemory
  · change (arenaRoot base input.size previous).toNat + 8 * (input.size + 1) ≤
        (arenaHeap base input.size slot + 48).toNat - 48 ∨
      (arenaHeap base input.size slot + 48).toNat + 8 * (input.size + 1) ≤
        (arenaRoot base input.size previous).toNat
    rw [← arena_root_eq_heap]
    have hSeparate := arena_roots_separate base input.size previous slot hPrevious hSlot hDistinct hBudget32
    rcases hSeparate with hLeft | hRight
    · exact Or.inl hLeft
    · exact Or.inr (by omega)

#print axioms arena_fresh_valid
end Project.EulerGridStep.Execution
