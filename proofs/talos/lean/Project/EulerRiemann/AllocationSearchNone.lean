import Project.EulerRiemann.AllocationSearchGuard
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime

def searchNoneInvariant (initial : Store Unit) (params saved : List Wasm.Value)
    (need : UInt64) (nodes : List FreeNode) : AssertionF Unit :=
  fun store frame => ∃ previous capacity next : UInt64, ∃ visited remaining : List FreeNode,
    store = initial ∧ nodes = visited ++ remaining ∧ FreeListAt initial.mem remaining ∧
    (∀ node ∈ remaining, node.capacity < need) ∧
    frame = allocationFrame params saved need previous (freeHead remaining) capacity next 0

def searchMeasure (nodes : List FreeNode) (_ : Store Unit) (frame : Locals) : Nat :=
  match frame.get 49 with
  | some (.i64 root) => scanRemaining nodes root
  | _ => 0

theorem search_none_spec (env : HostEnv Unit) (initial : Store Unit)
    (params saved : List Wasm.Value) (hParams : params.length = 5)
    (hPrefix : saved.length = 42) (need capacity next : UInt64) (nodes : List FreeNode)
    (hList : FreeListAt initial.mem nodes) (hNone : takeFirstFit need nodes = none)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previous capacity next : UInt64, wp Project.EulerRiemann.«module» rest Q initial
      (allocationFrame params saved need previous 0 capacity next 0) env) :
    wp Project.EulerRiemann.«module» ([.block 0 0 [.loop 0 0 sweepSearch]] ++ rest) Q initial
      (allocationFrame params saved need 0 (freeHead nodes) capacity next 0) env := by
  simp only [List.cons_append, List.nil_append]
  apply wp_block_cons
  apply wp_loop_cons (Inv := searchNoneInvariant initial params saved need nodes)
    (μ := searchMeasure nodes)
  · exact ⟨0, capacity, next, [], nodes, rfl, by simp, hList,
      (takeFirstFit_none_iff need nodes).mp hNone, rfl⟩
  · rintro store frame ⟨previous, oldCapacity, oldNext, visited, remaining, rfl,
      hSplit, hRemaining, hSmall, rfl⟩
    cases remaining with
    | nil =>
      rw [sweep_search_parts]
      simpa [searchGuard, wp_simp, allocationFrame, freeHead, hParams, hPrefix]
        using hNext previous oldCapacity oldNext
    | cons node tail =>
      have hRoot := hRemaining.head_ne_zero
      simp only [freeHead] at hRoot
      cases hRemaining with
      | cons hp h32 hFit hRc hCapacity hNodeNext hSep hTail =>
        have hCapSmall := hSmall node List.mem_cons_self
        have hNotFit : ¬need ≤ node.capacity := by
          rw [UInt64.le_iff_toNat_le]
          rw [UInt64.lt_iff_toNat_lt] at hCapSmall
          omega
        rw [sweep_search_parts]
        simp only [List.append_assoc]
        refine searchGuard_spec _ env store _ node.root rfl hRoot ?_ ?_ _ _ ?_
        · simp [allocationFrame, Locals.get, freeHead, hParams, hPrefix]
        · simp [allocationFrame, Locals.get, hParams, hPrefix]
        apply searchRead_spec env store params saved hParams hPrefix need previous node.root
          node.capacity (freeHead tail) 0 oldCapacity oldNext hp (by omega) (by omega)
          hCapacity hNodeNext
        simp [wp_simp, allocationFrame, hParams, hPrefix]
        refine wp_iff_cons rfl ?_
        rw [if_neg (by simp [hNotFit])]
        apply searchAdvance_spec env store params saved hParams hPrefix need previous node.root
          node.capacity (freeHead tail) 0 _ []
        simp [wp_simp]
        have hSplitNext : nodes = (visited ++ [node]) ++ tail := by
          simpa [List.append_assoc] using hSplit
        refine ⟨⟨node.root, node.capacity, freeHead tail, visited ++ [node], tail,
          rfl, hSplitNext, hTail, ?_, rfl⟩, ?_⟩
        · intro other hOther
          exact hSmall other (List.mem_cons_of_mem _ hOther)
        · have hBefore := hList.scanRemaining_suffix hSplit
          have hAfter := hList.scanRemaining_suffix hSplitNext
          simp only [freeHead, List.length_cons] at hBefore
          simp [searchMeasure, allocationFrame, Locals.get, hParams, hPrefix, hAfter]
          simpa only [freeHead, hBefore] using Nat.lt_succ_self tail.length

#print axioms search_none_spec

end Project.EulerRiemann.Execution
