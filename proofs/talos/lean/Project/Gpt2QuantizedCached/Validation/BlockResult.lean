import Project.Gpt2QuantizedCached.Validation.BlockProbe

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.Validation
open Wasm Project.ProofKit PackedFloatFrame LeanExe.Models.Gpt2.Quantized

def probeResultCode (which : Bool) (slot : Nat) (failure : UInt64) : Program :=
  probeCode (if which then 41 else 34) (if which then 42 else 35)
    (if which then 43 else 36) (if which then 44 else 37) ++
  ReadOnlyDisjunction.negateProgram ++ ReadOnlyDisjunction.canonicalProgram ++
  [.iff 0 1 [.constI64 failure] [.constI64 0] [] [.i64], .localSet (3 + slot)]

def probeResultFrame (frame : Locals) (owner ptr : UInt64) (weights : ByteArray)
    (layer : Nat) (which : Bool) (slot : Nat) (failure : UInt64) : Locals :=
  let scanned := probeFrame frame owner ptr weights layer
    (if which then 41 else 34) (if which then 42 else 35)
    (if which then 43 else 36) (if which then 44 else 37)
  { scanned with
    locals := scanned.locals.set slot
      (.i64 (if validBlock weights (blocksOffset + layer * blockBytes) then 0 else failure))
    values := [] }

theorem probeResult0_code : (blockLoop.drop 6).take 43 = probeResultCode false 35 1 := rfl
theorem probeResult1_code : (blockLoop.drop 49).take 43 = probeResultCode false 36 2 := rfl
theorem probeResult2_code : (blockLoop.drop 92).take 43 = probeResultCode false 37 0 := rfl
theorem probeResult3_code : (blockLoop.drop 141).take 43 = probeResultCode true 57 1 := rfl

theorem probeResult_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr : UInt64) (weights : ByteArray) (layer : Nat)
    (hWeights : PackedMemory.ByteArrayAt initial.mem ptr.toNat weights)
    (hSize : weights.size = modelBytes) (hLayer : layer < 12)
    (frame : Locals) (hParams : frame.params = parameters owner ptr weights)
    (hLength : frame.locals.length = 62) (hValues : frame.values = [])
    (hLayerRead : frame.locals[30]? = some (.i64 (UInt64.ofNat layer)))
    (which : Bool) (slot : Nat) (failure : UInt64) (hSlot : slot < 62)
    (Q : Assertion Unit) (rest : Program)
    (hNext : wp «module» rest Q initial
      (probeResultFrame frame owner ptr weights layer which slot failure) env) :
    wp «module» (probeResultCode which slot failure ++ rest) Q initial frame env := by
  have hLow : ¬ slot + 3 < 3 := by omega
  have hHigh : slot + 3 < 65 := by omega
  simp only [probeResultCode, List.append_assoc]
  apply probe_spec env initial owner ptr weights layer hWeights hSize hLayer
    frame hParams hLength hValues hLayerRead which
  apply ReadOnlyDisjunction.negate_spec _ _ _ _ _ rfl
  apply ReadOnlyDisjunction.canonical_spec _ _ _ _ _ rfl
  simp only [List.cons_append, List.nil_append, wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  cases hAnswer : validBlock weights (blocksOffset + layer * blockBytes)
  · rw [ite_eq_left (by decide)]
    wp_packed_frame [probeFrame, parameters, hParams, hLength, hSlot, Nat.add_comm, hLow, hHigh, Nat.add_sub_cancel]
    simpa only [probeResultFrame, probeFrame, hParams, parameters, hAnswer, Bool.false_eq_true, ite_false] using hNext
  · rw [ite_eq_right (by decide)]
    wp_packed_frame [probeFrame, parameters, hParams, hLength, hSlot, Nat.add_comm, hLow, hHigh, Nat.add_sub_cancel]
    simpa only [probeResultFrame, probeFrame, hParams, parameters, hAnswer, ite_true] using hNext

#print axioms probeResult_spec
end Project.Gpt2QuantizedCached.Validation
