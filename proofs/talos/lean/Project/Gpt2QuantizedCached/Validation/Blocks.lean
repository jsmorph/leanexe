import Project.Gpt2QuantizedCached.Validation.BlockStep

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.Validation
open Wasm Project.ProofKit PackedFloatFrame LeanExe.Models.Gpt2.Quantized

theorem blocks_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr : UInt64) (weights : ByteArray)
    (hWeights : PackedMemory.ByteArrayAt initial.mem ptr.toNat weights)
    (hSize : weights.size = modelBytes)
    (frame : Locals) (hParams : frame.params = parameters owner ptr weights)
    (hLength : frame.locals.length = 64) (hValues : frame.values = [])
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ result, result.params = parameters owner ptr weights → result.locals.length = 64 →
      result.values = [] → result.locals[48]? = some (.i64 (if Model.blocksValid weights then 0 else 2)) →
      wp «module» rest Q initial result env) :
    wp «module» (blocksCode ++ rest) Q initial frame env := by
  rw [blocks_code]
  simp only [List.append_assoc, blocksCode, globalCode, func28,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.take, List.drop,
    List.cons_append, List.nil_append]
  wp_packed_frame [hParams, parameters, hLength, hValues]
  apply RangeExitLoop.program_spec (P := LoopState owner ptr weights)
    (Exit := ExitState owner ptr weights) (count := 12)
  · decide
  · simp [RangeFoldLoop.Ready, Locals.get, hLength]
  · simp [LoopState, hLength, parameters]
  · intro index next hIndex hReady hState Q rest hNext hExit
    exact blockStep_spec env initial owner ptr weights index hWeights hSize hIndex next
      hReady hState Q rest hNext hExit
  · intro result hReady hState
    rcases hState with ⟨hParams', hLength', hStride', hFlag', hStatus', hZero', hPrefix⟩
    have hAll : Model.blocksValid weights = true := by
      simpa only [Model.blocksValid, List.all_eq_true, List.mem_range] using hPrefix
    wp_packed_frame [hParams', parameters, hLength', hReady.1, hFlag', hStatus', hZero']
    refine wp_iff_cons rfl ?_
    rw [ite_eq_left (by decide)]
    wp_packed_frame [hParams', parameters, hLength']
    apply hNext
    · rfl
    · simpa using hLength'
    · rfl
    · simp [hLength', hAll]
  · intro index result hIndex hValues' hExit
    rcases hExit with ⟨hParams', hLength', hFlag', hStatus', hZero', hBad⟩
    have hAll : Model.blocksValid weights = false := by
      cases hAnswer : Model.blocksValid weights
      · rfl
      · have hAll := hAnswer
        simp only [Model.blocksValid, List.all_eq_true, List.mem_range] at hAll
        have := hAll index hIndex
        simp_all
    wp_packed_frame [hParams', parameters, hLength', hValues', hFlag', hStatus', hZero']
    refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by decide)]
    wp_packed_frame [hParams', parameters, hLength']
    apply hNext
    · rfl
    · simpa using hLength'
    · rfl
    · simp [hLength', hAll]

#print axioms blocks_spec
end Project.Gpt2QuantizedCached.Validation
