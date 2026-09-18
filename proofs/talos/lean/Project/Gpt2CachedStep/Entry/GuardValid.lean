import Project.Gpt2CachedStep.Entry.Plan
import Project.Gpt2CachedStep.Layout
import Project.ProofKit.FixedArrayEqNode

namespace Project.Gpt2CachedStep.Entry
open Wasm Project.Common Project.ProofKit PackedFloatFrame LeanExe.Models.Gpt2

def rejectedBody : Wasm.Program :=
  [.constI64 0, .localSet 51, .constI64 0, .localSet 52, .constI64 0, .localSet 53,
   .constI64 0, .localSet 54, .constI64 0, .localSet 55, .constI64 0, .localSet 56]

def returnCode : Wasm.Program := [.localGet 52, .localGet 53, .localGet 55, .localGet 56]

set_option maxRecDepth 32768 in
theorem emitted_guard : func38 = func38.take 25 ++ [.iff 0 0 rejectedBody validBody] ++ returnCode := rfl

theorem guard_valid_spec (env : HostEnv Unit) (initial : Store Unit)
    (weightsPtr cachePtr : UInt64) (weights cache : ByteArray) (token : UInt32) (position : Nat) (frame : Locals)
    (hValid : Valid weights cache token position)
    (hState : State (parameters weightsPtr cachePtr weights cache token position) frame)
    (Q : Assertion Unit)
    (hBody : ∀ result, State (parameters weightsPtr cachePtr weights cache token position) result →
      wp «module» validBody (FixedArrayEqNode.branchPost «module» env returnCode Q) initial result env) :
    wp «module» func38 Q initial frame env := by
  rcases hState with ⟨hParams, hLocals, hValues, hTyped⟩
  have hWeightsWord : UInt64.ofNat weights.size = 497759232 := by rw [hValid.1]; rfl
  have hToken : ¬(50257 : UInt64) ≤ token.toUInt64 := by
    simpa only [UInt64.le_iff_toNat_le, UInt32.toNat_toUInt64,
      show (50257 : UInt64).toNat = 50257 from rfl] using Nat.not_le.mpr hValid.2.1
  have hPosition : ¬(128 : UInt64) ≤ UInt64.ofNat position := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' (by change position < 18446744073709551616; have := hValid.2.2.1; omega)]
    exact Nat.not_le.mpr hValid.2.2.1
  have hCacheWord : UInt64.ofNat cache.size = UInt64.ofNat position * 18432 * 4 := by
    rw [hValid.2.2.2, UInt64.ofNat_mul, UInt64.mul_assoc]
    rfl
  have hMulPosition : ¬(-1 : UInt64) / 18432 < UInt64.ofNat position := by
    have := hValid.2.2.1
    change ¬(1000799917193443 : UInt64) < UInt64.ofNat position
    u64_omega
  have hMulCache : ¬(-1 : UInt64) / 4 < UInt64.ofNat position * 18432 := by
    simpa only [UInt64.ofNat_mul, show UInt64.ofNat 18432 = 18432 from rfl,
      show UInt64.ofNat 4 = 4 from rfl] using CheckedNatMul.guard_of_nat_fits (position * 18432) 4
        (by change position * 18432 * 4 < 18446744073709551616; have := hValid.2.2.1; omega) (by decide)
  rw [emitted_guard]
  simp only [func38, List.take, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, parameters, hLocals, hValues, List.getElem?_cons_zero, List.getElem?_cons_succ]
  refine wp_call_tw ((Layout.parameterWords_exact env initial).append_args rfl rfl rfl
    [.i64 (UInt64.ofNat weights.size)]) ?_
  rintro final values ⟨_, rfl, rfl, rfl⟩
  repeat' first
    | wp_packed_frame [hParams, parameters, hLocals, hWeightsWord, hToken, hPosition,
        List.getElem?_cons_zero, List.getElem?_cons_succ, show UInt64.ofNat parameterWords = 124439808 from rfl]
    | (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])
  refine wp_call_tw ((Layout.cachePositionWords_exact env final).append_args rfl rfl rfl
    [.i64 (UInt64.ofNat cache.size)]) ?_
  rintro final' values ⟨_, rfl, rfl, rfl⟩
  repeat' first
    | wp_packed_frame [hParams, parameters, hLocals, hCacheWord, hMulPosition, hMulCache,
        List.getElem?_cons_zero, List.getElem?_cons_succ, show UInt64.ofNat cachePositionWords = 18432 from rfl]
    | (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])
  apply wp.conseq (Q := FixedArrayEqNode.branchPost «module» env returnCode Q)
  · intro continuation hBranch
    cases continuation
    case Break depth final frame =>
      cases depth <;> simpa [FixedArrayEqNode.branchPost, wp_simp, Locals.get] using hBranch
    all_goals simpa [FixedArrayEqNode.branchPost, wp_simp, Locals.get] using hBranch
  · apply hBody
    simp (config := { maxDischargeDepth := 64 }) only [State, parameters, hLocals, List.length_set,
      I64Values.set, hTyped, hWeightsWord, hCacheWord, and_self]

#print axioms guard_valid_spec

end Project.Gpt2CachedStep.Entry
