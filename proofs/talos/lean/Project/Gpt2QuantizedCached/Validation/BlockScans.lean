import Project.Gpt2QuantizedCached.Validation.BlockResult
import Project.ProofKit.RangeExitLoop

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.Validation
open Wasm Project.ProofKit PackedFloatFrame LeanExe.Models.Gpt2.Quantized

def scansCode : Program :=
  [.localGet 52, .localSet 33] ++ probeResultCode false 35 1 ++
    probeResultCode false 36 2 ++ probeResultCode false 37 0 ++
    [.localGet 38, .localSet 61, .localGet 39, .localSet 62, .localGet 40, .localSet 63] ++
    probeResultCode true 57 1

theorem scans_code : (blockLoop.drop 4).take 180 = scansCode := rfl

def ScanState (owner ptr : UInt64) (weights : ByteArray) (layer : Nat) (frame : Locals) : Prop :=
  frame.params = parameters owner ptr weights ∧ frame.locals.length = 64 ∧
    frame.locals[49]? = some (.i64 (UInt64.ofNat layer)) ∧
    frame.locals[50]? = some (.i64 12) ∧ frame.locals[51]? = some (.i64 1)

def ScanResult (owner ptr : UInt64) (weights : ByteArray) (layer : Nat) (frame : Locals) : Prop :=
  ScanState owner ptr weights layer frame ∧ frame.values = [] ∧
    frame.locals[58]? = some (.i64 (if validBlock weights (blocksOffset + layer * blockBytes) then 0 else 1)) ∧
    frame.locals[59]? = some (.i64 (if validBlock weights (blocksOffset + layer * blockBytes) then 0 else 2)) ∧
    frame.locals[60]? = some (.i64 0) ∧
    frame.locals[57]? = some (.i64 (if validBlock weights (blocksOffset + layer * blockBytes) then 0 else 1))

theorem scans_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr : UInt64) (weights : ByteArray) (layer : Nat)
    (hWeights : PackedMemory.ByteArrayAt initial.mem ptr.toNat weights)
    (hSize : weights.size = modelBytes) (hLayer : layer < 12)
    (frame : Locals) (hState : ScanState owner ptr weights layer frame)
    (hValues : frame.values = []) (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ result, ScanResult owner ptr weights layer result → wp «module» rest Q initial result env) :
    wp «module» (scansCode ++ rest) Q initial frame env := by
  rcases hState with ⟨hParams, hLength, hCounter, hStop, hStride⟩
  simp only [scansCode, List.append_assoc, List.cons_append, List.nil_append]
  wp_packed_frame [parameters, hParams, hLength, hCounter, hValues]
  apply probeResult_spec env initial owner ptr weights layer hWeights hSize hLayer _
    (by simpa only [parameters] using hParams) (by simpa using hLength) rfl
    (by simp [hLength]) false 35 1 (by decide)
  apply probeResult_spec env initial owner ptr weights layer hWeights hSize hLayer _
    (by simpa only [probeResultFrame, probeFrame, parameters] using hParams)
    (by simpa only [probeResultFrame, probeFrame, List.length_set] using hLength) rfl
    (by simp [probeResultFrame, probeFrame, hLength]) false 36 2 (by decide)
  apply probeResult_spec env initial owner ptr weights layer hWeights hSize hLayer _
    (by simpa only [probeResultFrame, probeFrame, parameters] using hParams)
    (by simpa only [probeResultFrame, probeFrame, List.length_set] using hLength) rfl
    (by simp [probeResultFrame, probeFrame, hLength]) false 37 0 (by decide)
  wp_packed_frame [probeResultFrame, probeFrame, parameters, hParams, hLength]
  apply probeResult_spec env initial owner ptr weights layer hWeights hSize hLayer _
    (by simpa only [parameters] using hParams)
    (by simpa only [List.length_set] using hLength) rfl
    (by simp [hLength]) true 57 1 (by decide)
  apply hNext
  simp only [ScanResult, ScanState, probeResultFrame, probeFrame, parameters, hParams,
    hLength, List.length_set, List.getElem?_set, Nat.reduceSub, Nat.reduceAdd, Nat.reduceLT,
    Nat.reduceEqDiff, reduceIte, Bool.false_eq_true, ite_true, ite_false, ite_self,
    true_and, and_true, hCounter, hStop, hStride, and_self]

#print axioms scans_spec
end Project.Gpt2QuantizedCached.Validation
