import Project.Gpt2QuantizedCached.Validation.BlockScans

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.Validation
open Wasm Project.ProofKit PackedFloatFrame LeanExe.Models.Gpt2.Quantized

def blockStep : Program := scansCode ++ (blockLoop.drop 184).dropLast

theorem blocks_code : blocksCode = blocksCode.take 14 ++
    RangeFoldLoop.program 52 53 blockStep ++ blocksCode.drop 15 := rfl

def LoopState (owner ptr : UInt64) (weights : ByteArray) (index : Nat) (frame : Locals) : Prop :=
  frame.params = parameters owner ptr weights ∧ frame.locals.length = 62 ∧
    frame.locals[51]? = some (.i64 1) ∧ frame.locals[27]? = some (.i64 0) ∧
    frame.locals[28]? = some (.i64 0) ∧ frame.locals[29]? = some (.i64 0) ∧
    ∀ previous, previous < index → validBlock weights (blocksOffset + previous * blockBytes) = true

def ExitState (owner ptr : UInt64) (weights : ByteArray) (index : Nat) (frame : Locals) : Prop :=
  frame.params = parameters owner ptr weights ∧ frame.locals.length = 62 ∧
    frame.locals[27]? = some (.i64 1) ∧ frame.locals[28]? = some (.i64 2) ∧ frame.locals[29]? = some (.i64 0) ∧
    validBlock weights (blocksOffset + index * blockBytes) = false

theorem blockStep_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr : UInt64) (weights : ByteArray) (index : Nat)
    (hWeights : PackedMemory.ByteArrayAt initial.mem ptr.toNat weights)
    (hSize : weights.size = modelBytes) (hIndex : index < 12)
    (frame : Locals) (hReady : RangeFoldLoop.Ready 52 53 12 index frame)
    (hState : LoopState owner ptr weights index frame)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ result, RangeFoldLoop.Ready 52 53 12 (index + 1) result →
      LoopState owner ptr weights (index + 1) result → wp «module» rest Q initial result env)
    (hExit : ∀ result, result.values = [] → ExitState owner ptr weights index result →
      Q (.Break 1 initial result)) :
    wp «module» (blockStep ++ rest) Q initial frame env := by
  rcases hState with ⟨hParams, hLength, hStride, hFlag, hStatus, hZero, hPrefix⟩
  have hCounter : frame.locals[49]? = some (.i64 (UInt64.ofNat index)) := by
    simpa [Locals.get, hParams, parameters, hLength] using hReady.2.1
  have hStop : frame.locals[50]? = some (.i64 12) := by
    simpa [Locals.get, hParams, parameters, hLength] using hReady.2.2
  have hInc := CheckedNatAdd.guard_of_fits index 1
    (by change index + 1 < 18446744073709551616; omega)
  simp only [blockStep, List.append_assoc]
  apply scans_spec env initial owner ptr weights index hWeights hSize hIndex frame
    ⟨hParams, hLength, hCounter, hStop, hStride⟩ hReady.1
  intro scanned hScanned
  rcases hScanned with ⟨⟨hParams', hLength', hCounter', hStop', hStride'⟩,
    hValues', hFlag', hStatus', hZero', hExit'⟩
  simp only [blockLoop, blocksCode, globalCode, func28, List.getElem?_cons_zero,
    List.getElem?_cons_succ, List.drop, List.dropLast, List.cons_append, List.nil_append]
  cases hAnswer : validBlock weights (blocksOffset + index * blockBytes)
  · wp_packed_frame [parameters, hParams', hLength', hValues', hFlag', hStatus', hZero', hExit', hAnswer]
    rw [ite_eq_left (by decide)]
    apply hExit _ rfl
    simp [ExitState, hParams', parameters, hLength', hAnswer]
  · wp_packed_frame [parameters, hParams', hLength', hValues', hFlag', hStatus', hZero', hExit', hAnswer]
    rw [ite_eq_right (by decide)]
    wp_packed_frame [parameters, hParams', hLength', hCounter', hStride']
    refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by simpa using hInc)]
    wp_packed_frame [parameters, hParams', hLength', ← UInt64.ofNat_add]
    apply hNext
    · simp only [RangeFoldLoop.Ready, Locals.get, hLength', List.length_set,
        List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
        reduceIte, List.getElem?_set, Nat.reduceEqDiff, hStop', UInt64.ofNat_add, true_and]
      exact ⟨rfl, rfl⟩
    · refine ⟨rfl, by simpa using hLength', ?_, ?_, ?_, ?_, ?_⟩
      · simp only [List.getElem?_set, List.length_set, hLength', Nat.reduceLT,
          Nat.reduceEqDiff, reduceIte, hStride']
      · simp [hLength']
      · simp [hLength']
      · simp [hLength']
      · intro previous hPrevious
        by_cases hEq : previous = index
        · simpa only [hEq] using hAnswer
        · exact hPrefix previous (by omega)

#print axioms blockStep_spec
end Project.Gpt2QuantizedCached.Validation
