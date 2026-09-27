import Project.Gpt2CachedStep.Program
import Project.ProofKit.CheckedNatMul
import Project.ProofKit.PackedFloatFrame

namespace Project.Gpt2CachedStep.CachedAttention
open Wasm Project.ProofKit PackedFloatFrame

theorem emitted_attention_signature : func29Def.params.length = 8 ∧ func29Def.locals.length = 114 := by
  constructor <;> rfl

def fixedSizeCode (count byteLocal : Nat) : Wasm.Program :=
  [.constI64 (UInt64.ofNat count), .localSet 109, .constI64 4, .localSet 110] ++
    CheckedNatMul.program 109 110 ++ [.localSet byteLocal, .localGet byteLocal, .localSet 109]

def fixedSizeFrame (frame : Locals) (count byteLocal : Nat) : Locals :=
  { frame with
    locals := (((frame.locals.set 101 (.i64 (UInt64.ofNat count))).set 102 (.i64 4)).set
      (byteLocal - 8) (.i64 (UInt64.ofNat (4 * count)))).set 101 (.i64 (UInt64.ofNat (4 * count)))
    values := [] }

theorem fixedSize_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals) (count byteLocal : Nat)
    (hParams : frame.params.length = 8) (hLocals : frame.locals.length = 114)
    (hValues : frame.values = []) (hLow : 8 ≤ byteLocal) (hHigh : byteLocal < 109)
    (hCount : 4 * count ≤ 2^32)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q store (fixedSizeFrame frame count byteLocal) env) :
    wp «module» (fixedSizeCode count byteLocal ++ rest) Q store frame env := by
  have hBytes : UInt64.ofNat count * 4 = UInt64.ofNat (4 * count) := by
    rw [Nat.mul_comm 4 count]
    simp
  have hNotParam : ¬ byteLocal < 8 := by omega
  have hValid : byteLocal < 8 + 114 := by omega
  have hSlot : byteLocal - 8 < 114 := by omega
  simp only [fixedSizeCode, List.append_assoc, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLocals, hValues]
  apply CheckedNatMul.program_spec 109 110 «module» env store _ (UInt64.ofNat count) 4 []
  · rfl
  · simp [Locals.get, hParams, hLocals]
  · simp [Locals.get, hParams, hLocals]
  · simp only [UInt64.toNat_ofNat', UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    change _ < 18446744073709551616
    omega
  wp_packed_frame [hParams, hLocals, hBytes, hNotParam, hValid, hSlot]
  exact hNext

set_option maxRecDepth 32768 in
theorem emitted_fixed_sizes :
    (func29.drop 68).take 11 = fixedSizeCode 12 25 ∧
    (func29.drop 173).take 11 = fixedSizeCode 12 51 ∧
    (func29.drop 278).take 11 = fixedSizeCode 768 76 := by
  constructor <;> first | rfl | (constructor <;> rfl)

#print axioms fixedSize_spec

end Project.Gpt2CachedStep.CachedAttention
