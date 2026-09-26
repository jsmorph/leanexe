import Project.EulerRiemann.FrozenInitialLoop

namespace Project.EulerRiemann.Frozen.Execution
open Wasm Project.Runtime Project.ProofKit FixedArrayCapacity

def initialPostLoop : Wasm.Program := (func95.drop 5).take 4

theorem initial_post_loop_shape : initialPostLoop =
    [.localGet 8, .constI64 0, .eqI64, .iff 0 0 initialExtractBody []] := rfl

theorem initial_post_loop_spec (env : HostEnv Unit) (initial : Store Unit) (initialHeap : Heap)
    (n size limit pageLimit : Nat) (store : Store Unit) (frame : Locals)
    (hSizeBound : size ≤ 640000) (hLimit : limit < 4294967296)
    (hCap : limit ≤ initial.memoryCap module 0 * 65536) (hPhysicalLimit : limit ≤ pageLimit * 65536)
    (hExit : initialExit initial initialHeap n size limit pageLimit store frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final finalHeap resultFrame done,
      RetryStoreAt initial initialHeap final finalHeap → final.mem.pages ≤ pageLimit →
      InitialResult initial initialHeap n size limit final finalHeap resultFrame done →
      wp module rest Q final resultFrame env) :
    wp module (initialPostLoop ++ rest) Q store frame env := by
  obtain ⟨⟨heap, hState, hPages, hActive | hDone⟩, hStopped⟩ := hExit
  · obtain ⟨fuel, rounds, source, tracked, grid, hFrame, hScratch, hRounds, hPrefix,
      hOwner, hCapacity, hBelow, hBudget, hSeparated⟩ := hActive
    have hFuel : fuel = 0 := by
      simpa [initialStopped, hFrame.params, hFrame.done] using hStopped
    have hRound : rounds = 20 := by simpa [hFuel] using hRounds
    have hGridSize : grid.size = 1048576 := by simpa [hRound] using hPrefix.size
    have hSelfPrefix : InitialPrefix n grid.size grid := by rw [hPrefix.size]; exact hPrefix
    have hCurrentCap : limit ≤ store.memoryCap module 0 * 65536 := by rw [hState.cap]; exact hCap
    have hParams := hFrame.params
    have hLocals := hFrame.locals
    have hValues := hFrame.values
    have hEmpty : ({ frame with values := [] } : Locals) = frame := Frame.ext _ _ rfl rfl hValues.symm
    rw [initial_post_loop_shape]
    wp_run [List.cons_append, List.nil_append, hParams, hLocals, hValues, hFrame.done,
      Nat.reduceLT, Nat.reduceAdd, Nat.reduceSub, reduceIte]
    rw [← hParams]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_left (by decide)]
    change wp module initialExtractBody _ store { frame with values := [] } env
    rw [hEmpty, ← List.append_nil initialExtractBody]
    apply initial_extract_resources_spec env initial store initialHeap heap frame fuel n size source
      (if tracked then source.root else 0) 0 false false grid limit pageLimit hFrame hScratch hState
      hOwner hSelfPrefix (by omega) (by omega) hBelow hBudget hLimit hCurrentCap hPages hPhysicalLimit
    dsimp only
    intro final resultFrame hFinal hResult hResultPrefix hFinalPages hTop hSaved hResultCapacity hResultFrame
    have hTrim : ({ resultFrame with values := [] } : Locals) = resultFrame :=
      Frame.ext _ _ rfl rfl hResultFrame.values.symm
    simp only [wp_simp, List.take_zero, List.drop_zero, List.nil_append, hTrim]
    apply hNext final _ resultFrame false hFinal hFinalPages
    exact ⟨fuel, source.root, (if tracked then source.root else 0),
      allocatedNode heap.top (normalizedCapacity (UInt64.ofNat size) 7) heap.nodes,
      grid.extract 0 size, hResultFrame, hResult, hResultPrefix, hResultCapacity, hTop, hSaved⟩
  · have hCompleted := hDone
    obtain ⟨fuel, source, tracker, result, grid, hFrame, _⟩ := hDone
    have hParams := hFrame.params
    have hLocals := hFrame.locals
    have hValues := hFrame.values
    have hEmpty : ({ frame with values := [] } : Locals) = frame := Frame.ext _ _ rfl rfl hValues.symm
    rw [initial_post_loop_shape]
    wp_run [List.cons_append, List.nil_append, hParams, hLocals, hValues, hFrame.done,
      Nat.reduceLT, Nat.reduceAdd, Nat.reduceSub, reduceIte]
    rw [← hParams]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by decide)]
    simpa only [wp_simp, List.take_zero, List.drop_zero, List.nil_append, hEmpty] using
      hNext store heap frame true hState hPages hCompleted

#print axioms initial_post_loop_shape
#print axioms initial_post_loop_spec

end Project.EulerRiemann.Frozen.Execution
