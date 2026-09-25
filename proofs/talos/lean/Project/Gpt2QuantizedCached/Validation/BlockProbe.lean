import Project.Gpt2QuantizedCached.Validation.Global
import Project.ProofKit.CheckedNatMul
import Project.ProofKit.CheckedNatAddArithmetic

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.Validation
open Wasm Project.ProofKit PackedFloatFrame LeanExe.Models.Gpt2.Quantized

def blocksCode : Program :=
  match (globalCode[39]? : Option Instruction) with
  | some (.iff _ _ _ body _ _) => body
  | _ => []

def blockLoop : Program :=
  match (blocksCode[12]? : Option Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def probeCode (ownerLocal ptrLocal sizeLocal baseLocal : Nat) : Program :=
  [.localGet 0, .localSet ownerLocal, .localGet 1, .localSet ptrLocal,
   .localGet 2, .localSet sizeLocal, .call 4, .localSet 55,
   .localGet 33, .localSet 58, .call 19, .localSet 59] ++
    CheckedNatMul.program 58 59 ++
  [.localSet 56, .localGet 55, .localGet 56, .addI64, .localTee 57,
   .localGet 55, .ltUI64, .iff 0 1 [.unreachable] [.localGet 57] [] [.i64],
   .localSet baseLocal, .localGet ownerLocal, .localGet ptrLocal, .localGet sizeLocal,
   .localGet baseLocal, .call 27]

def probeFrame (frame : Locals) (owner ptr : UInt64) (weights : ByteArray) (layer : Nat)
    (ownerLocal ptrLocal sizeLocal baseLocal : Nat) : Locals :=
  { frame with
    locals := (((((((((frame.locals.set (ownerLocal - 3) (.i64 owner)).set
      (ptrLocal - 3) (.i64 ptr)).set (sizeLocal - 3) (.i64 (UInt64.ofNat weights.size))).set
      52 (.i64 (UInt64.ofNat blocksOffset))).set 55 (.i64 (UInt64.ofNat layer))).set
      56 (.i64 (UInt64.ofNat blockBytes))).set 53 (.i64 (UInt64.ofNat (layer * blockBytes)))).set
      54 (.i64 (UInt64.ofNat (blocksOffset + layer * blockBytes)))).set
      (baseLocal - 3) (.i64 (UInt64.ofNat (blocksOffset + layer * blockBytes))))
    values := [.i64 (if validBlock weights (blocksOffset + layer * blockBytes) then 1 else 0)] }

private theorem probe0_code : (blockLoop.drop 6).take 30 = probeCode 34 35 36 37 := rfl
private theorem probe1_code : (blockLoop.drop 49).take 30 = probeCode 34 35 36 37 := rfl
private theorem probe2_code : (blockLoop.drop 92).take 30 = probeCode 34 35 36 37 := rfl
private theorem probe3_code : (blockLoop.drop 141).take 30 = probeCode 41 42 43 44 := rfl

theorem probe_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr : UInt64) (weights : ByteArray) (layer : Nat)
    (hWeights : PackedMemory.ByteArrayAt initial.mem ptr.toNat weights)
    (hSize : weights.size = modelBytes) (hLayer : layer < 12)
    (frame : Locals) (hParams : frame.params = parameters owner ptr weights)
    (hLength : frame.locals.length = 64) (hValues : frame.values = [])
    (hLayerRead : frame.locals[30]? = some (.i64 (UInt64.ofNat layer)))
    (which : Bool) (Q : Assertion Unit) (rest : Program)
    (hNext : wp «module» rest Q initial
      (probeFrame frame owner ptr weights layer (if which then 41 else 34)
        (if which then 42 else 35) (if which then 43 else 36) (if which then 44 else 37)) env) :
    wp «module» (probeCode (if which then 41 else 34) (if which then 42 else 35)
      (if which then 43 else 36) (if which then 44 else 37) ++ rest) Q initial frame env := by
  have hLayer64 : layer < UInt64.size := by change layer < 18446744073709551616; omega
  have hMul : layer * blockBytes < UInt64.size := by
    change layer * 7145472 < 18446744073709551616; omega
  have hAdd := CheckedNatAdd.guard_of_fits blocksOffset (layer * blockBytes)
    (by change 41944164 + layer * 7145472 < 18446744073709551616; omega)
  have hExtent : blocksOffset + layer * blockBytes + blockBytes ≤ weights.size := by
    rw [hSize]; change 41944164 + layer * 7145472 + 7145472 ≤ 127695972; omega
  simp only [parameters] at hParams
  cases which <;> simp only [Bool.false_eq_true, ite_false, ite_true,
    probeCode, List.append_assoc, List.cons_append, List.nil_append]
  all_goals
    wp_packed_frame [hParams, hLength, hValues]
    refine wp_call_tw (Layout.blocksOffset_exact env initial) ?_
    rintro final values ⟨hFinal, rfl⟩
    subst final
    wp_packed_frame [hParams, hLength, hLayerRead]
    refine wp_call_tw (Layout.blockBytes_exact env initial) ?_
    rintro final values ⟨hFinal, rfl⟩
    subst final
    wp_packed_frame [hParams, hLength]
    apply CheckedNatMul.program_spec 58 59 «module» env initial _
      (UInt64.ofNat layer) (UInt64.ofNat blockBytes) []
    · rfl
    · simp [Locals.get, hParams, hLength]
    · simp [Locals.get, hParams, hLength]
    · simpa only [UInt64.toNat_ofNat_of_lt' hLayer64,
        UInt64.toNat_ofNat_of_lt' (show blockBytes < UInt64.size by decide)] using hMul
    wp_packed_frame [hParams, hLength, ← UInt64.ofNat_mul]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by simpa using hAdd)]
    wp_packed_frame [hParams, hLength, ← UInt64.ofNat_add]
    refine wp_call_tw (BlockValidation.exact env initial owner ptr weights
      (blocksOffset + layer * blockBytes) hWeights hExtent) ?_
    rintro final values ⟨hFinal, rfl⟩
    subst final
    simpa only [probeFrame, hParams, Bool.false_eq_true, ite_false, ite_true] using hNext

#print axioms probe_spec
end Project.Gpt2QuantizedCached.Validation
