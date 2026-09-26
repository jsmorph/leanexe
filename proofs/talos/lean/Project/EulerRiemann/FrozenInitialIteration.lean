import Project.EulerRiemann.FrozenInitialInvariant

namespace Project.EulerRiemann.Frozen.Execution
open Wasm Project.Runtime Project.ProofKit FixedArrayCapacity

def initialIterationPost (initial : Store Unit) (initialHeap : Heap)
    (n size limit pageLimit measure : Nat) : Assertion Unit :=
  BlockLoop.stepPost (initialInvariant initial initialHeap n size limit pageLimit)
    (initialExit initial initialHeap n size limit pageLimit) (fun _ frame => initialMeasure frame) measure

theorem initial_iteration_spec (env : HostEnv Unit) (initial : Store Unit) (initialHeap : Heap)
    (n size limit pageLimit : Nat) (store : Store Unit) (frame : Locals)
    (hn : n ≤ 800) (hSizeBound : size ≤ 640000) (hLimit : limit < 4294967296)
    (hCap : limit ≤ initial.memoryCap module 0 * 65536) (hPhysicalLimit : limit ≤ pageLimit * 65536)
    (hInv : initialInvariant initial initialHeap n size limit pageLimit store frame) :
    wp module initialLoop (initialIterationPost initial initialHeap n size limit pageLimit (initialMeasure frame))
      store frame env := by
  have hOriginal := hInv
  obtain ⟨heap, hState, hPages, hActive | hDone⟩ := hInv
  · obtain ⟨fuel, rounds, source, tracked, grid, hFrame, hScratch, hRounds, hPrefix,
      hOwner, hCapacity, hBelow, hBudget, hSeparated⟩ := hActive
    rw [initial_loop_body_shape, List.append_assoc]
    apply initial_guard_spec env store frame fuel n size source.root
      (if tracked then source.root else 0) 0 false hFrame
    by_cases hFuel : fuel = 0
    · simp only [hFuel, true_or, ite_true]
      exact ⟨hOriginal, Or.inl (by simp [hFrame.params, hFuel])⟩
    · simp only [hFuel, Bool.false_eq_true, or_self, ite_false]
      have hFuelNat := retryFuel_unfold fuel hFuel
      have hRoundBound : rounds < 20 := by omega
      have hGridSize := hPrefix.size
      have hCount : grid.size + grid.size ≤ 1048576 := by
        rw [hGridSize]
        exact initial_growth_double_bound rounds hRoundBound
      have hParams : frame.params.length = 5 := by rw [hFrame.params]; rfl
      have hSelected := hFrame.selected
      have hSelectedScratch := hScratch.selected source.root hParams hFrame.locals
      have hSelfPrefix : InitialPrefix n grid.size grid := by simpa only [hGridSize] using hPrefix
      have hCurrentCap : limit ≤ store.memoryCap module 0 * 65536 := by rw [hState.cap]; exact hCap
      apply initial_select_spec env store frame source.root size grid hParams hFrame.locals hFrame.values
        (by simp [Locals.get, hFrame.params]) (by simp [Locals.get, hFrame.params])
        (by change size < 18446744073709551616; omega)
        (by change grid.size < 18446744073709551616; omega) hOwner.buffer.values
      by_cases hSize : size ≤ grid.size
      · simp only [hSize, ite_true]
        refine wp_iff_cons rfl ?_
        rw [ite_eq_left (by decide)]
        change wp module initialDoneBody _ store (initialSelectedFrame frame source.root) env
        rw [← List.append_nil initialDoneBody]
        apply initial_extract_resources_spec env initial store initialHeap heap
          (initialSelectedFrame frame source.root) fuel n size source (if tracked then source.root else 0)
          0 false true grid limit pageLimit hSelected hSelectedScratch hState hOwner hSelfPrefix hSize
          (by omega) hBelow hBudget hLimit hCurrentCap hPages hPhysicalLimit
        dsimp only
        intro final resultFrame hFinal hResult hResultPrefix hFinalPages hTop hSaved hResultCapacity hResultFrame
        have hResultValues := hResultFrame.values
        have hTrim : ({ resultFrame with values := [] } : Locals) = resultFrame :=
          Frame.ext _ _ rfl rfl hResultValues.symm
        simp only [wp_simp, List.take_zero, List.drop_zero, List.nil_append, hTrim]
        change initialInvariant _ _ _ _ _ _ _ _ ∧ _
        refine ⟨⟨_, hFinal, hFinalPages, Or.inr ⟨fuel, source.root,
          (if tracked then source.root else 0),
          allocatedNode heap.top (normalizedCapacity (UInt64.ofNat size) 7) heap.nodes,
          grid.extract 0 size, hResultFrame, hResult, hResultPrefix,
          hResultCapacity, hTop, hSaved⟩⟩, ?_⟩
        dsimp only
        rw [hResultFrame.measure, hFrame.measure]
        simp
      · simp only [hSize, ite_false]
        refine wp_iff_cons rfl ?_
        rw [ite_eq_right (by decide)]
        change wp module initialGrowBody _ store (initialSelectedFrame frame source.root) env
        rw [← List.append_nil initialGrowBody]
        apply initial_growth_spec env initial store initialHeap heap (initialSelectedFrame frame source.root)
          fuel n size source tracked grid limit pageLimit hSelected hSelectedScratch hState hOwner hSelfPrefix
          hCount (by rw [hGridSize]; positivity) (by omega) hBelow hCapacity hSeparated
          (by omega) hBudget hLimit hCurrentCap hPages hPhysicalLimit hn
        intro final finalHeap resultFrame hFinal hResult hResultPrefix hFinalPages hFinalBelow hFinalBudget
          hSaved hResultCapacity hResultFrame hResultScratch
        have hNewSize : (grid ++ initialMapOutput n grid.size grid).size = grid.size + grid.size :=
          hResultPrefix.size
        have hNextRounds : rounds + 1 + (fuel - 1).toNat = 20 := by omega
        have hNextPrefix : InitialPrefix n (2 ^ (rounds + 1)) (grid ++ initialMapOutput n grid.size grid) := by
          simpa only [Nat.pow_succ, Nat.mul_two, hGridSize] using hResultPrefix
        have hNextBudget : finalHeap.top.toNat + initialRemainingBytes
            (grid ++ initialMapOutput n grid.size grid).size (fuel - 1).toNat size ≤ limit := by
          rw [hNewSize]
          have hSub : (fuel - 1).toNat = fuel.toNat - 1 := by omega
          rw [hSub]
          exact hFinalBudget
        have hTrim : ({ resultFrame with values := [] } : Locals) = resultFrame :=
          Frame.ext _ _ rfl rfl hResultFrame.values.symm
        simp only [wp_simp, List.take_zero, List.drop_zero, List.nil_append, hTrim]
        change initialInvariant _ _ _ _ _ _ _ _ ∧ _
        refine ⟨⟨finalHeap, hFinal, hFinalPages, Or.inl ⟨fuel - 1, rounds + 1,
          initialGrowthNode heap grid.size, true, grid ++ initialMapOutput n grid.size grid,
          hResultFrame, hResultScratch, hNextRounds, hNextPrefix, hResult,
          ?_, ?_, hNextBudget, fun _ => hSaved⟩⟩, ?_⟩
        · simpa only [hNewSize] using hResultCapacity
        · simpa only [hNewSize] using hFinalBelow
        · dsimp only
          rw [hResultFrame.measure, hFrame.measure]
          simpa using retryFuel_decreases fuel hFuel
  · obtain ⟨fuel, source, tracker, result, grid, hFrame, _⟩ := hDone
    rw [← List.take_append_drop 7 initialLoop]
    apply initial_guard_spec env store frame fuel n size source tracker result.root true hFrame
    simp only [or_true, ite_true]
    exact ⟨hOriginal, Or.inr hFrame.done⟩

#print axioms initial_iteration_spec

end Project.EulerRiemann.Frozen.Execution
