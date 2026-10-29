import LeanExe.ProofKit.AlignedSearch
import LeanExe.ProofKit.AlignedHeaderExec
import LeanExe.ProofKit.FixedArraySearchFit

/-!
The reuse of a free block by `alloc` under `wpA`: the ports of the programs of
`FixedArrayReuse.lean` and of `fitProgram_spec_of` and `fitProgram_spec`, the search that finds
a block.  The unlink stores the link word of the block before the chosen one, at its root minus
8.  A split stores the chosen block's lowered size word at its root minus 32 and writes the new
object's header at `splitBase`, the root plus the capacity minus the request minus 48.  Every
access is aligned when the free blocks' roots and capacities and the request are multiples of 8.
-/

namespace LeanExe.ProofKit.FixedArrayReuse
open Wasm LeanExe.Runtime LeanExe.ProofKit LeanExe.ProofKit.Memory FixedArraySearch

theorem unlinkProgram_specA (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit)
    (params saved tail : List Wasm.Value) (start : Nat)
    (hStart : params.length + saved.length = start) (need result head : UInt64)
    (choice : FreeChoice) (hGlobal : store.globals.globals[1]? = some (.i64 head))
    (hBound : choice.previous ≠ 0 →
      (choice.previous - 8).toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (hPrevious : choice.previous ≠ 0 →
      48 ≤ choice.previous.toNat ∧ choice.previous.toNat < 4294967296 ∧
        choice.previous.toNat % 8 = 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wpA module_ rest Q (unlinkStore store choice)
      (frame params saved tail need choice.previous choice.node.root choice.node.capacity
        choice.next result) env) :
    wpA module_ (unlinkProgram start ++ rest) Q store
      (frame params saved tail need choice.previous choice.node.root choice.node.capacity
        choice.next result) env := by
  subst start
  obtain ⟨hGlobalLength, hGlobalRead⟩ := List.getElem_of_getElem? hGlobal
  unfold unlinkProgram
  simp [wpA_simp, wp_simp, frame, Nat.add_assoc]
  refine wpA_iff_cons rfl ?_
  by_cases hPrev : choice.previous = 0
  · simpa [wpA_simp, wp_simp, frame, Nat.add_assoc, hPrev,
      unlinkStore, unlinkFreeChoice, hGlobalLength, hGlobalRead] using hNext
  · have hWriteBound : (choice.previous.toUInt32 - 8).toNat + 8 ≤
        store.mem.pages * 65536 := by simpa using hBound hPrev
    obtain ⟨h48, h32, hAl⟩ := hPrevious hPrev
    have hs : (choice.previous.toUInt32 - 8).toNat = choice.previous.toNat - 8 := by
      simpa using toUInt32_sub_toNat (p := choice.previous) (k := 8) (by simp; omega) (by simp; omega)
    simp [wpA_simp, wp_simp, Nat.add_assoc, hPrev, Nat.reducePow, ← toUInt32_eq_ofNat,
      Nat.not_lt.mpr hWriteBound]
    wpA_close
    simpa [frame, unlinkStore, unlinkFreeChoice, hPrev] using hNext

theorem wholeProgram_specA (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit)
    (params saved tail : List Wasm.Value) (start : Nat)
    (hStart : params.length + saved.length = start) (need result head stride : UInt64)
    (choice : FreeChoice) (hGlobal : store.globals.globals[1]? = some (.i64 head))
    (hPrevious : choice.previous ≠ 0 →
      (choice.previous - 8).toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (hPreviousAl : choice.previous ≠ 0 →
      48 ≤ choice.previous.toNat ∧ choice.previous.toNat < 4294967296 ∧
        choice.previous.toNat % 8 = 0)
    (hRoot : 48 ≤ choice.node.root.toNat)
    (hRoot32 : choice.node.root.toNat + choice.node.capacity.toNat ≤ 4294967296)
    (hFit : choice.node.root.toNat + choice.node.capacity.toNat ≤ store.mem.pages * 65536)
    (hRootAl : choice.node.root.toNat % 8 = 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wpA module_ rest Q (fixedArrayAllocFitStore store choice stride)
      (frame params saved tail need choice.previous choice.node.root choice.node.capacity
        choice.next choice.node.root) env) :
    wpA module_ (wholeProgram start stride ++ rest) Q store
      (frame params saved tail need choice.previous choice.node.root choice.node.capacity
        choice.next result) env := by
  subst start
  have hBase : (choice.node.root - 48).toNat = choice.node.root.toNat - 48 :=
    toNat_sub_of_le choice.node.root 48 hRoot
  simp only [wholeProgram, List.append_assoc]
  apply unlinkProgram_specA module_ env store params saved tail _ rfl need result head choice
    hGlobal hPrevious hPreviousAl
  refine FixedArrayHeader.program_specA module_ env _ _ _ _
    (choice.node.root - 48) choice.node.capacity stride rfl ?_ ?_ ?_ ?_ ?_ _ _ ?_
  · simp [frame, Locals.get, Nat.add_assoc]
  · simp [frame, Locals.get, Nat.add_assoc]
  · rw [hBase]
    omega
  · rw [hBase, unlinkStore_pages]
    omega
  · rw [hBase]
    omega
  · rw [← fitStore_header store choice stride hRoot (by omega)]
    simpa [wpA_simp, wp_simp, frame, Nat.add_assoc] using hNext

theorem splitProgram_specA (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit)
    (params saved tail : List Wasm.Value) (start : Nat)
    (hStart : params.length + saved.length = start) (need result stride : UInt64)
    (choice : FreeChoice) (hRoot : 48 ≤ choice.node.root.toNat)
    (hRoot32 : choice.node.root.toNat + choice.node.capacity.toNat < 4294967296)
    (hFit : choice.node.root.toNat + choice.node.capacity.toNat ≤ store.mem.pages * 65536)
    (hNeed : need ≤ choice.node.capacity) (hSplit : splitsFit need choice = true)
    (hRootAl : choice.node.root.toNat % 8 = 0) (hCapAl : choice.node.capacity.toNat % 8 = 0)
    (hNeedAl : need.toNat % 8 = 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wpA module_ rest Q { store with mem := fixedArraySplitMem store.mem choice need stride }
      (frame params saved tail need choice.previous choice.node.root choice.node.capacity
        choice.next (choice.node.root + choice.node.capacity - need)) env) :
    wpA module_ (splitProgram start stride ++ rest) Q store
      (frame params saved tail need choice.previous choice.node.root choice.node.capacity
        choice.next result) env := by
  subst start
  have hNeedNat := UInt64.le_iff_toNat_le.mp hNeed
  have hSplitNat := hSplit
  simp only [splitsFit, decide_eq_true_eq, UInt64.le_iff_toNat_le,
    UInt64.toNat_sub_of_le _ _ hNeed] at hSplitNat
  simp only [UInt64.reduceToNat] at hSplitNat
  have h32 : (choice.node.root - 32).toUInt32.toNat = choice.node.root.toNat - 32 := by
    rw [toUInt32_toNat, toNat_sub_of_le _ _ (by simp; omega), Nat.mod_eq_of_lt (by simp; omega)]
    rfl
  have hSum : (choice.node.root + choice.node.capacity).toNat =
      choice.node.root.toNat + choice.node.capacity.toNat := by
    rw [UInt64.toNat_add]
    omega
  have hTop : (choice.node.root + choice.node.capacity - need).toNat =
      choice.node.root.toNat + choice.node.capacity.toNat - need.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hSum]; omega), hSum]
  have hBase : (splitBase need choice).toNat =
      choice.node.root.toNat + choice.node.capacity.toNat - need.toNat - 48 := by
    unfold splitBase
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hTop]; simp; omega), hTop]
    rfl
  have hs : (choice.node.root - 32).toNat = choice.node.root.toNat - 32 :=
    toNat_sub_of_le _ _ (by simp; omega)
  have hBound : ¬ store.mem.pages * 65536 < (choice.node.root - 32).toNat % 4294967296 + 8 := by
    rw [hs, Nat.mod_eq_of_lt (by omega)]
    omega
  simp only [splitProgram, List.cons_append, List.append_assoc]
  simp [wpA_simp, wp_simp, frame, Nat.add_assoc]
  rw [ite_eq_right hBound]
  refine ⟨by omega, ?_⟩
  rw [← toUInt32_eq_ofNat]
  refine FixedArrayHeader.program_specA module_ env _ _ _ _ (splitBase need choice) need stride
    rfl ?_ ?_ (by omega) (by simp only [Wasm.Mem.write64_pages]; omega) (by omega) _ _ ?_
  · simp [Locals.get, Nat.add_assoc, splitBase]
  · simp [Locals.get, Nat.add_assoc]
  · simpa [fixedArraySplitMem, frame, Nat.add_assoc] using hNext

theorem program_specA (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit)
    (params saved tail : List Wasm.Value) (start : Nat)
    (hStart : params.length + saved.length = start) (need result head stride : UInt64)
    (choice : FreeChoice) (hGlobal : store.globals.globals[1]? = some (.i64 head))
    (hPrevious : choice.previous ≠ 0 →
      (choice.previous - 8).toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (hPreviousAl : choice.previous ≠ 0 →
      48 ≤ choice.previous.toNat ∧ choice.previous.toNat < 4294967296 ∧
        choice.previous.toNat % 8 = 0)
    (hRoot : 48 ≤ choice.node.root.toNat)
    (hRoot32 : choice.node.root.toNat + choice.node.capacity.toNat < 4294967296)
    (hFit : choice.node.root.toNat + choice.node.capacity.toNat ≤ store.mem.pages * 65536)
    (hNeed : need ≤ choice.node.capacity)
    (hRootAl : choice.node.root.toNat % 8 = 0) (hCapAl : choice.node.capacity.toNat % 8 = 0)
    (hNeedAl : need.toNat % 8 = 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wpA module_ rest Q (fixedArrayReuseStore store choice need stride)
      (frame params saved tail need choice.previous choice.node.root choice.node.capacity
        choice.next (reuseRoot choice need)) env) :
    wpA module_ (program start stride ++ rest) Q store
      (frame params saved tail need choice.previous choice.node.root choice.node.capacity
        choice.next result) env := by
  subst start
  simp only [program, List.cons_append, List.nil_append]
  simp [wpA_simp, wp_simp, frame, Nat.add_assoc]
  refine wpA_iff_cons rfl ?_
  by_cases hSplit : splitsFit need choice = true
  · have hGe : 56 ≤ choice.node.capacity - need := by simpa [splitsFit] using hSplit
    simp only [fixedArrayReuseStore, reuseRoot, hSplit, ite_true] at hNext
    simp only [hGe, ite_true, ne_eq]
    rw [← List.append_nil (splitProgram _ stride)]
    apply splitProgram_specA module_ env store params saved tail _ rfl need result stride choice
      hRoot hRoot32 hFit hNeed hSplit hRootAl hCapAl hNeedAl
    simpa [wpA_simp, frame] using hNext
  · have hLt : ¬ 56 ≤ choice.node.capacity - need := by simpa [splitsFit] using hSplit
    simp only [fixedArrayReuseStore, reuseRoot, hSplit, Bool.false_eq_true, ite_false] at hNext
    simp only [hLt, ite_false, ne_eq, not_true_eq_false]
    rw [← List.append_nil (wholeProgram _ stride)]
    apply wholeProgram_specA module_ env store params saved tail _ rfl need result head stride
      choice hGlobal hPrevious hPreviousAl hRoot (by omega) hFit hRootAl
    simpa [wpA_simp, frame] using hNext

end LeanExe.ProofKit.FixedArrayReuse

namespace LeanExe.ProofKit.FixedArraySearch
open Wasm LeanExe.Runtime LeanExe.ProofKit LeanExe.ProofKit.Memory

theorem fitProgram_spec_ofA (module_ : Wasm.Module) (env : HostEnv Unit)
    (initial final : Store Unit) (params saved extra : List Wasm.Value) (start : Nat)
    (hStart : params.length + saved.length = start) (need capacity next : UInt64)
    (nodes : List FreeNode) (choice : FreeChoice) (fitProgram : Wasm.Program) (found : UInt64)
    (hFound : found ≠ 0) (hList : FreeListAt initial.mem nodes)
    (hTake : takeFirstFitFrom 0 need nodes = some choice)
    (hRoots : ∀ node ∈ nodes, node.root.toNat % 8 = 0)
    (hReuse : ∀ (Q : Assertion Unit) (rest : Wasm.Program),
      wpA module_ rest Q final
        (frame params saved extra need choice.previous choice.node.root choice.node.capacity
          choice.next found) env →
      wpA module_ (fitProgram ++ rest) Q initial
        (frame params saved extra need choice.previous choice.node.root choice.node.capacity
          choice.next 0) env)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wpA module_ rest Q final
      (frame params saved extra need choice.previous choice.node.root choice.node.capacity
        choice.next found) env) :
    wpA module_ (program start fitProgram ++ rest) Q initial
      (frame params saved extra need 0 (freeHead nodes) capacity next 0) env := by
  subst start
  obtain ⟨skipped, tail, hNodes, hPrevious, hNextRoot, _, hSmall⟩ :=
    takeFirstFitFrom_some_decompose hTake
  subst nodes
  have hChoiceFit := takeFirstFitFrom_some_capacity hTake
  have hChoiceRoot := hList.roots_ne_zero choice.node
    (List.mem_append_right skipped List.mem_cons_self)
  have hChoiceAl := hRoots choice.node (List.mem_append_right skipped List.mem_cons_self)
  simp only [program, List.cons_append, List.nil_append]
  apply wpA_block_cons
  apply wpA_loop_cons
    (Inv := fitInvariant initial final params saved extra need skipped tail choice found)
    (μ := fitMeasure (params.length + saved.length) (skipped ++ choice.node :: tail))
  · left
    exact ⟨capacity, next, [], skipped, rfl, by simp, hList, hSmall, rfl⟩
  · rintro store locals hInv
    rcases hInv with hSearch | hDone
    · obtain ⟨oldCapacity, oldNext, visited, remaining, rfl, hSplit, hRemaining,
        hRemainingSmall, rfl⟩ := hSearch
      cases remaining with
      | cons node remaining =>
        simp only [List.cons_append] at hRemaining
        have hRoot := hRemaining.head_ne_zero
        simp only [freeHead] at hRoot
        have hNodeAl : node.root.toNat % 8 = 0 :=
          hRoots node (by rw [hSplit]; simp)
        cases hRemaining with
        | cons hp h32 hFit hRc hCapacity hNodeNext hSep hTail =>
          have hNotFit : ¬need ≤ node.capacity := by
            have hSmallNode := hRemainingSmall node List.mem_cons_self
            rw [UInt64.le_iff_toNat_le]
            rw [UInt64.lt_iff_toNat_lt] at hSmallNode
            omega
          simp only [body]
          simp only [List.append_assoc]
          refine wpA_append_accessFree (by rfl) ?_
          rw [← List.append_nil (guardProgram _)]
          refine guardProgram_spec module_ env store _ _ node.root rfl hRoot ?_ ?_ _ _
            (wp_nil.mpr ?_)
          · simp [frame, Locals.get, freeHead, Nat.add_assoc]
          · simp [frame, Locals.get, Nat.add_assoc]
          apply readProgram_specA module_ env store params saved extra _ rfl need
            (previousRoot 0 visited) node.root node.capacity
            (freeHead (remaining ++ choice.node :: tail)) 0 oldCapacity oldNext hp (by omega)
            (by omega) hNodeAl hCapacity hNodeNext
          simp [wpA_simp, wp_simp, frame, Nat.add_assoc]
          refine wpA_iff_cons rfl ?_
          rw [ite_eq_right (by simp [hNotFit]), ← List.append_nil (advanceProgram _)]
          refine wpA_append_accessFree (by rfl) ?_
          apply advanceProgram_spec module_ env store params saved extra _ rfl need
            (previousRoot 0 visited) node.root node.capacity
            (freeHead (remaining ++ choice.node :: tail)) 0 _ []
          simp [wpA_simp, wp_simp]
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
          · simp [previousRoot_append_singleton, frame]
          · have hBefore := hList.scanRemaining_suffix hBeforeSplit
            have hAfter := hList.scanRemaining_suffix hAfterSplit
            simp only [freeHead, List.length_cons] at hBefore
            simp [fitMeasure, measure, frame, Locals.get,
              Nat.add_assoc, hAfter]
            simp [freeHead, hBefore]
      | nil =>
        simp only [List.nil_append] at hRemaining
        cases hRemaining with
        | cons hp h32 hFit hRc hCapacity hNodeNext hSep hTail =>
          have hRuntimePrevious : previousRoot 0 visited = choice.previous := by
            rw [hSplit] at hPrevious
            simpa using hPrevious.symm
          simp only [body]
          simp only [List.append_assoc]
          refine wpA_append_accessFree (by rfl) ?_
          rw [← List.append_nil (guardProgram _)]
          refine guardProgram_spec module_ env store _ _ choice.node.root rfl hChoiceRoot ?_ ?_
            _ _ (wp_nil.mpr ?_)
          · simp [frame, Locals.get, freeHead, Nat.add_assoc]
          · simp [frame, Locals.get, Nat.add_assoc]
          apply readProgram_specA module_ env store params saved extra _ rfl need
            (previousRoot 0 visited) choice.node.root choice.node.capacity (freeHead tail) 0
            oldCapacity oldNext hp (by omega) (by omega) hChoiceAl hCapacity hNodeNext
          simp [wpA_simp, wp_simp, frame, Nat.add_assoc]
          refine wpA_iff_cons rfl ?_
          rw [ite_eq_left (by simp [hChoiceFit])]
          rw [← List.append_nil fitProgram]
          change wpA _ (fitProgram ++ []) _ store
            (frame params saved extra need (previousRoot 0 visited) choice.node.root
              choice.node.capacity (freeHead tail) 0) env
          rw [hRuntimePrevious, ← hNextRoot]
          apply hReuse
          simp [wpA_simp, wp_simp]
          refine ⟨Or.inr ⟨rfl, rfl⟩, ?_⟩
          have hScan := hList.scanRemaining_suffix
            (visited := skipped) (remaining := choice.node :: tail) rfl
          simp only [freeHead, List.length_cons] at hScan
          simp [fitMeasure, measure, frame, Locals.get,
            Nat.add_assoc, hFound, freeHead, hScan]
    · rcases hDone with ⟨rfl, rfl⟩
      simp only [body]
      simpa [guardProgram, wpA_simp, wp_simp, frame, Nat.add_assoc, hChoiceRoot,
        hFound] using hNext

theorem fitProgram_specA (module_ : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (params saved extra : List Wasm.Value) (start : Nat)
    (hStart : params.length + saved.length = start) (need capacity next stride : UInt64)
    (nodes : List FreeNode) (choice : FreeChoice)
    (hGlobal : initial.globals.globals[1]? = some (.i64 (freeHead nodes)))
    (hList : FreeListAt initial.mem nodes) (hTake : takeFirstFitFrom 0 need nodes = some choice)
    (hRoots : ∀ node ∈ nodes, node.root.toNat % 8 = 0)
    (hCapacities : ∀ node ∈ nodes, node.capacity.toNat % 8 = 0) (hNeedAl : need.toNat % 8 = 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wpA module_ rest Q (fixedArrayReuseStore initial choice need stride)
      (frame params saved extra need choice.previous choice.node.root choice.node.capacity
        choice.next (reuseRoot choice need)) env) :
    wpA module_ (program start (FixedArrayReuse.program start stride) ++ rest) Q initial
      (frame params saved extra need 0 (freeHead nodes) capacity next 0) env := by
  apply fitProgram_spec_ofA module_ env initial _ params saved extra start hStart need capacity
    next nodes choice (FixedArrayReuse.program start stride) (reuseRoot choice need)
    (reuseRoot_ne_zero hList hTake) hList hTake hRoots _ Q rest hNext
  intro post continuation hContinuation
  have hMem := takeFirstFitFrom_some_mem hTake
  obtain ⟨hRoot, hRoot32, hFit⟩ := hList.mem_bounds hMem
  have hPreviousAl : choice.previous ≠ 0 → 48 ≤ choice.previous.toNat ∧
      choice.previous.toNat < 4294967296 ∧ choice.previous.toNat % 8 = 0 := fun hNonzero => by
    obtain ⟨predecessor, hPred, hEq⟩ := FreeListMemory.previous_mem hTake hNonzero
    rw [hEq]
    exact ⟨(hList.mem_bounds hPred).1, by have := (hList.mem_bounds hPred).2.1; omega,
      hRoots predecessor hPred⟩
  exact FixedArrayReuse.program_specA module_ env initial params saved extra start hStart need 0
    (freeHead nodes) stride choice hGlobal (choice_previous_bound hList hTake) hPreviousAl hRoot
    hRoot32 hFit (takeFirstFitFrom_some_capacity hTake) (hRoots _ hMem) (hCapacities _ hMem)
    hNeedAl post continuation hContinuation

end LeanExe.ProofKit.FixedArraySearch
