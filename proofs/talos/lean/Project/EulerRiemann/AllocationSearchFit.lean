import Project.EulerRiemann.AllocationSearchNone

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ClobMatchFuel.BookAllocFit Project.ProofKit.Memory

theorem choice_previous_bound {mem : Wasm.Mem} {nodes : List FreeNode}
    {need : UInt64} {choice : FreeChoice} (hList : FreeListAt mem nodes)
    (hTake : takeFirstFitFrom 0 need nodes = some choice) (hNonzero : choice.previous ≠ 0) :
    (choice.previous - 8).toUInt32.toNat + 8 ≤ mem.pages * 65536 := by
  obtain ⟨skipped, tail, hNodes, hPrevious, _, _, _⟩ :=
    takeFirstFitFrom_some_decompose hTake
  have hSkipped : skipped ≠ [] := by
    intro hEmpty
    exact hNonzero (by simpa [hEmpty, previousRoot] using hPrevious)
  let predecessor := skipped.getLast hSkipped
  have hSplit : skipped.dropLast ++ [predecessor] = skipped :=
    List.dropLast_append_getLast hSkipped
  have hRoot : choice.previous = predecessor.root := by
    rw [hPrevious, ← hSplit, previousRoot_append_singleton]
  have hMem : predecessor ∈ nodes := by
    rw [hNodes, ← hSplit]
    simp
  obtain ⟨h48, h32, hFit⟩ := hList.mem_bounds hMem
  have hSub : (predecessor.root - 8).toNat = predecessor.root.toNat - 8 :=
    toNat_sub_of_le _ _ (by change 8 ≤ predecessor.root.toNat; omega)
  rw [hRoot, UInt64.toNat_toUInt32, hSub, Nat.mod_eq_of_lt (by omega)]
  omega

def searchFitInvariant (initial : Store Unit) (params saved : List Wasm.Value)
    (need : UInt64) (skipped tail : List FreeNode) (choice : FreeChoice) : AssertionF Unit :=
  fun store frame =>
    (∃ capacity next : UInt64, ∃ visited remaining : List FreeNode,
      store = initial ∧ skipped = visited ++ remaining ∧
      FreeListAt initial.mem (remaining ++ choice.node :: tail) ∧
      (∀ node ∈ remaining, node.capacity < need) ∧
      frame = allocationFrame params saved need (previousRoot 0 visited)
        (freeHead (remaining ++ choice.node :: tail)) capacity next 0) ∨
    (store = fixedArrayAllocFitStore initial choice 7 ∧
      frame = allocationFrame params saved need choice.previous choice.node.root
        choice.node.capacity choice.next choice.node.root)

def searchFitMeasure (nodes : List FreeNode) (store : Store Unit) (frame : Locals) : Nat :=
  match frame.get 52 with
  | some (.i64 result) => if result = 0 then searchMeasure nodes store frame else 0
  | _ => 0

theorem search_fit_spec (env : HostEnv Unit) (initial : Store Unit)
    (params saved : List Wasm.Value) (hParams : params.length = 5)
    (hPrefix : saved.length = 42) (need capacity next : UInt64) (nodes : List FreeNode)
    (choice : FreeChoice) (hGlobal : initial.globals.globals[1]? = some (.i64 (freeHead nodes)))
    (hList : FreeListAt initial.mem nodes) (hTake : takeFirstFitFrom 0 need nodes = some choice)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerRiemann.«module» rest Q (fixedArrayAllocFitStore initial choice 7)
      (allocationFrame params saved need choice.previous choice.node.root choice.node.capacity
        choice.next choice.node.root) env) :
    wp Project.EulerRiemann.«module» ([.block 0 0 [.loop 0 0 sweepSearch]] ++ rest) Q initial
      (allocationFrame params saved need 0 (freeHead nodes) capacity next 0) env := by
  obtain ⟨skipped, tail, hNodes, hPrevious, hNextRoot, _, hSmall⟩ :=
    takeFirstFitFrom_some_decompose hTake
  subst nodes
  have hChoiceFit := takeFirstFitFrom_some_capacity hTake
  have hChoiceRoot := hList.roots_ne_zero choice.node
    (List.mem_append_right skipped List.mem_cons_self)
  have hPreviousBound := choice_previous_bound hList hTake
  simp only [List.cons_append, List.nil_append]
  apply wp_block_cons
  apply wp_loop_cons (Inv := searchFitInvariant initial params saved need skipped tail choice)
    (μ := searchFitMeasure (skipped ++ choice.node :: tail))
  · left
    exact ⟨capacity, next, [], skipped, rfl, by simp, hList, hSmall, rfl⟩
  · rintro store frame hInv
    rcases hInv with hSearch | hDone
    · obtain ⟨oldCapacity, oldNext, visited, remaining, rfl, hSplit, hRemaining,
        hRemainingSmall, rfl⟩ := hSearch
      cases remaining with
      | cons node remaining =>
        simp only [List.cons_append] at hRemaining
        have hRoot := hRemaining.head_ne_zero
        simp only [freeHead] at hRoot
        cases hRemaining with
        | cons hp h32 hFit hRc hCapacity hNodeNext hSep hTail =>
          have hNotFit : ¬need ≤ node.capacity := by
            have hSmallNode := hRemainingSmall node List.mem_cons_self
            rw [UInt64.le_iff_toNat_le]
            rw [UInt64.lt_iff_toNat_lt] at hSmallNode
            omega
          rw [sweep_search_parts]
          simp only [List.append_assoc]
          refine searchGuard_spec _ env store _ node.root rfl hRoot ?_ ?_ _ _ ?_
          · simp [allocationFrame, Locals.get, freeHead, hParams, hPrefix]
          · simp [allocationFrame, Locals.get, hParams, hPrefix]
          apply searchRead_spec env store params saved hParams hPrefix need (previousRoot 0 visited)
            node.root node.capacity (freeHead (remaining ++ choice.node :: tail)) 0 oldCapacity
            oldNext hp (by omega) (by omega) hCapacity hNodeNext
          simp [wp_simp, allocationFrame, hParams, hPrefix]
          refine wp_iff_cons rfl ?_
          rw [if_neg (by simp [hNotFit])]
          apply searchAdvance_spec env store params saved hParams hPrefix need
            (previousRoot 0 visited) node.root node.capacity
            (freeHead (remaining ++ choice.node :: tail)) 0 _ []
          simp [wp_simp]
          have hSplitNext : skipped = (visited ++ [node]) ++ remaining := by
            simpa [List.append_assoc] using hSplit
          have hBeforeSplit : skipped ++ choice.node :: tail =
              visited ++ (node :: (remaining ++ choice.node :: tail)) := by
            rw [hSplit]
            simp [List.append_assoc]
          have hAfterSplit : skipped ++ choice.node :: tail =
              (visited ++ [node]) ++ (remaining ++ choice.node :: tail) := by
            rw [hSplitNext]
            simp [List.append_assoc]
          refine ⟨Or.inl ⟨node.capacity, freeHead (remaining ++ choice.node :: tail),
            visited ++ [node], remaining, rfl, hSplitNext, hTail, ?_, ?_⟩, ?_⟩
          · intro other hOther
            exact hRemainingSmall other (List.mem_cons_of_mem _ hOther)
          · simp [previousRoot_append_singleton, allocationFrame]
          · have hBefore := hList.scanRemaining_suffix hBeforeSplit
            have hAfter := hList.scanRemaining_suffix hAfterSplit
            simp only [freeHead, List.length_cons] at hBefore
            simp [searchFitMeasure, searchMeasure, allocationFrame, Locals.get,
              hParams, hPrefix, hAfter]
            simpa [freeHead, hBefore] using
              Nat.lt_succ_self (remaining ++ choice.node :: tail).length
      | nil =>
        simp only [List.nil_append] at hRemaining
        cases hRemaining with
        | cons hp h32 hFit hRc hCapacity hNodeNext hSep hTail =>
          have hRuntimePrevious : previousRoot 0 visited = choice.previous := by
            rw [hSplit] at hPrevious
            simpa using hPrevious.symm
          rw [sweep_search_parts]
          simp only [List.append_assoc]
          refine searchGuard_spec _ env store _ choice.node.root rfl hChoiceRoot ?_ ?_ _ _ ?_
          · simp [allocationFrame, Locals.get, freeHead, hParams, hPrefix]
          · simp [allocationFrame, Locals.get, hParams, hPrefix]
          apply searchRead_spec env store params saved hParams hPrefix need (previousRoot 0 visited)
            choice.node.root choice.node.capacity (freeHead tail) 0 oldCapacity oldNext hp
            (by omega) (by omega) hCapacity hNodeNext
          simp [wp_simp, allocationFrame, hParams, hPrefix]
          refine wp_iff_cons rfl ?_
          rw [if_pos (by simp [hChoiceFit])]
          change wp _ (sweepFit ++ []) _ store
            (allocationFrame params saved need (previousRoot 0 visited) choice.node.root
              choice.node.capacity (freeHead tail) 0) env
          rw [hRuntimePrevious, ← hNextRoot]
          apply sweep_fit_spec env store params saved hParams hPrefix need 0
            (freeHead (skipped ++ choice.node :: tail)) choice hGlobal hPreviousBound hp
            (by omega) hFit
          simp [wp_simp]
          refine ⟨Or.inr ⟨rfl, rfl⟩, ?_⟩
          have hScan := hList.scanRemaining_suffix
            (visited := skipped) (remaining := choice.node :: tail) rfl
          simp only [freeHead, List.length_cons] at hScan
          simp [searchFitMeasure, searchMeasure, allocationFrame, Locals.get,
            hParams, hPrefix, hChoiceRoot, freeHead, hScan]
    · rcases hDone with ⟨rfl, rfl⟩
      rw [sweep_search_parts]
      simpa [searchGuard, wp_simp, allocationFrame, hParams, hPrefix, hChoiceRoot] using hNext

#print axioms choice_previous_bound
#print axioms search_fit_spec

end Project.EulerRiemann.Execution
