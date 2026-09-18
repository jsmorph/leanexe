import Project.ProofKit.FixedArraySearchNone
import Project.ProofKit.FixedArrayReuse
import Project.ProofKit.FreeListMemory

namespace Project.ProofKit.FixedArraySearch
open Wasm Project.Runtime Project.ClobMatchFuel.BookAllocFit Project.ProofKit.Memory

theorem choice_previous_bound {mem : Wasm.Mem} {nodes : List FreeNode}
    {need : UInt64} {choice : FreeChoice} (hList : FreeListAt mem nodes)
    (hTake : takeFirstFitFrom 0 need nodes = some choice) (hNonzero : choice.previous ≠ 0) :
    (choice.previous - 8).toUInt32.toNat + 8 ≤ mem.pages * 65536 := by
  obtain ⟨predecessor, hMem, hRoot⟩ := Project.ProofKit.FreeListMemory.previous_mem hTake hNonzero
  obtain ⟨h48, h32, hFit⟩ := hList.mem_bounds hMem
  have hSub : (predecessor.root - 8).toNat = predecessor.root.toNat - 8 :=
    toNat_sub_of_le _ _ (by change 8 ≤ predecessor.root.toNat; omega)
  rw [hRoot, UInt64.toNat_toUInt32, hSub, Nat.mod_eq_of_lt (by omega)]
  omega

def fitInvariant (initial final : Store Unit) (params saved extra : List Wasm.Value)
    (need : UInt64) (skipped tail : List FreeNode) (choice : FreeChoice) : AssertionF Unit :=
  fun store locals =>
    (∃ capacity next : UInt64, ∃ visited remaining : List FreeNode,
      store = initial ∧ skipped = visited ++ remaining ∧
      FreeListAt initial.mem (remaining ++ choice.node :: tail) ∧
      (∀ node ∈ remaining, node.capacity < need) ∧
      locals = frame params saved extra need (previousRoot 0 visited)
        (freeHead (remaining ++ choice.node :: tail)) capacity next 0) ∨
    (store = final ∧
      locals = frame params saved extra need choice.previous choice.node.root
        choice.node.capacity choice.next choice.node.root)

def fitMeasure (start : Nat) (nodes : List FreeNode) (store : Store Unit) (locals : Locals) : Nat :=
  match locals.get (start + 5) with
  | some (.i64 result) => if result = 0 then measure start nodes store locals else 0
  | _ => 0

theorem fitProgram_spec_of (module_ : Wasm.Module) (env : HostEnv Unit) (initial final : Store Unit)
    (params saved extra : List Wasm.Value) (start : Nat)
    (hStart : params.length + saved.length = start) (need capacity next : UInt64) (nodes : List FreeNode)
    (choice : FreeChoice) (fitProgram : Wasm.Program)
    (hList : FreeListAt initial.mem nodes) (hTake : takeFirstFitFrom 0 need nodes = some choice)
    (hReuse : ∀ (Q : Assertion Unit) (rest : Wasm.Program),
      wp module_ rest Q final
        (frame params saved extra need choice.previous choice.node.root choice.node.capacity
          choice.next choice.node.root) env →
      wp module_ (fitProgram ++ rest) Q initial
        (frame params saved extra need choice.previous choice.node.root choice.node.capacity
          choice.next 0) env)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q final
      (frame params saved extra need choice.previous choice.node.root choice.node.capacity
        choice.next choice.node.root) env) :
    wp module_ (program start fitProgram ++ rest) Q initial
      (frame params saved extra need 0 (freeHead nodes) capacity next 0) env := by
  subst start
  obtain ⟨skipped, tail, hNodes, hPrevious, hNextRoot, _, hSmall⟩ :=
    takeFirstFitFrom_some_decompose hTake
  subst nodes
  have hChoiceFit := takeFirstFitFrom_some_capacity hTake
  have hChoiceRoot := hList.roots_ne_zero choice.node
    (List.mem_append_right skipped List.mem_cons_self)
  simp only [program, List.cons_append, List.nil_append]
  apply wp_block_cons
  apply wp_loop_cons (Inv := fitInvariant initial final params saved extra need skipped tail choice)
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
        cases hRemaining with
        | cons hp h32 hFit hRc hCapacity hNodeNext hSep hTail =>
          have hNotFit : ¬need ≤ node.capacity := by
            have hSmallNode := hRemainingSmall node List.mem_cons_self
            rw [UInt64.le_iff_toNat_le]
            rw [UInt64.lt_iff_toNat_lt] at hSmallNode
            omega
          simp only [body]
          simp only [List.append_assoc]
          refine guardProgram_spec module_ env store _ _ node.root rfl hRoot ?_ ?_ _ _ ?_
          · simp [frame, Locals.get, freeHead, Nat.add_assoc]
          · simp [frame, Locals.get, Nat.add_assoc]
          apply readProgram_spec module_ env store params saved extra _ rfl need (previousRoot 0 visited)
            node.root node.capacity (freeHead (remaining ++ choice.node :: tail)) 0 oldCapacity
            oldNext hp (by omega) (by omega) hCapacity hNodeNext
          simp [wp_simp, frame, Nat.add_assoc]
          refine wp_iff_cons rfl ?_
          rw [ite_eq_right (by simp [hNotFit])]
          apply advanceProgram_spec module_ env store params saved extra _ rfl need
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
          refine guardProgram_spec module_ env store _ _ choice.node.root rfl hChoiceRoot ?_ ?_ _ _ ?_
          · simp [frame, Locals.get, freeHead, Nat.add_assoc]
          · simp [frame, Locals.get, Nat.add_assoc]
          apply readProgram_spec module_ env store params saved extra _ rfl need (previousRoot 0 visited)
            choice.node.root choice.node.capacity (freeHead tail) 0 oldCapacity oldNext hp
            (by omega) (by omega) hCapacity hNodeNext
          simp [wp_simp, frame, Nat.add_assoc]
          refine wp_iff_cons rfl ?_
          rw [ite_eq_left (by simp [hChoiceFit])]
          rw [← List.append_nil fitProgram]
          change wp _ (fitProgram ++ []) _ store
            (frame params saved extra need (previousRoot 0 visited) choice.node.root
              choice.node.capacity (freeHead tail) 0) env
          rw [hRuntimePrevious, ← hNextRoot]
          apply hReuse
          simp [wp_simp]
          refine ⟨Or.inr ⟨rfl, rfl⟩, ?_⟩
          have hScan := hList.scanRemaining_suffix
            (visited := skipped) (remaining := choice.node :: tail) rfl
          simp only [freeHead, List.length_cons] at hScan
          simp [fitMeasure, measure, frame, Locals.get,
            Nat.add_assoc, hChoiceRoot, freeHead, hScan]
    · rcases hDone with ⟨rfl, rfl⟩
      simp only [body]
      simpa [guardProgram, wp_simp, frame, Nat.add_assoc, hChoiceRoot] using hNext

theorem fitProgram_spec (module_ : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (params saved extra : List Wasm.Value) (start : Nat)
    (hStart : params.length + saved.length = start) (need capacity next stride : UInt64) (nodes : List FreeNode)
    (choice : FreeChoice) (hGlobal : initial.globals.globals[1]? = some (.i64 (freeHead nodes)))
    (hList : FreeListAt initial.mem nodes) (hTake : takeFirstFitFrom 0 need nodes = some choice)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q (fixedArrayAllocFitStore initial choice stride)
      (frame params saved extra need choice.previous choice.node.root choice.node.capacity
        choice.next choice.node.root) env) :
    wp module_ (program start (FixedArrayReuse.program start stride) ++ rest) Q initial
      (frame params saved extra need 0 (freeHead nodes) capacity next 0) env := by
  apply fitProgram_spec_of module_ env initial _ params saved extra start hStart need capacity next
    nodes choice (FixedArrayReuse.program start stride) hList hTake _ Q rest hNext
  intro post continuation hContinuation
  obtain ⟨hRoot, hRoot32, hFit⟩ := hList.mem_bounds (takeFirstFitFrom_some_mem hTake)
  exact FixedArrayReuse.program_spec module_ env initial params saved extra start hStart need 0
    (freeHead nodes) stride choice hGlobal (choice_previous_bound hList hTake) hRoot
    (by omega) hFit post continuation hContinuation

#print axioms choice_previous_bound
#print axioms fitProgram_spec_of
#print axioms fitProgram_spec

end Project.ProofKit.FixedArraySearch
