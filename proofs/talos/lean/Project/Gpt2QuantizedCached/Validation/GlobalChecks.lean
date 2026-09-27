import Project.Gpt2QuantizedCached.BlockValidation
import Project.Gpt2QuantizedCached.ModelSource
import Project.ProofKit.ReadOnlyDisjunction

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.Validation
open Wasm Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2.Quantized

def parameters (owner ptr : UInt64) (weights : ByteArray) : List Value :=
  [.i64 owner, .i64 ptr, .i64 (UInt64.ofNat weights.size)]

def globalCode : Program :=
  match (func28[21]? : Option Instruction) with
  | some (.iff _ _ _ body _ _) => body
  | _ => []

def globalCheck (index : Nat) : Program :=
  match (globalCode[29 + index]? : Option Instruction) with
  | some (.iff _ _ _ body _ _) => body.take (body.length - 4)
  | _ => []

theorem coefficients_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr : UInt64) (weights : ByteArray)
    (hWeights : ByteArrayAt initial.mem ptr.toNat weights) (hSize : weights.size = modelBytes) :
    ReadOnlyBoolean.BodySpec «module» env initial (parameters owner ptr weights) 64
      (globalCode.take 25) (validCoefficients weights tokenWeightOffset (50257 * 768)) := by
  intro frame hParams hLength hValues Q rest hNext
  simp only [parameters] at hParams
  have hExtent : tokenWeightOffset + (50257 * 768) ≤ weights.size := by rw [hSize]; decide
  simp only [globalCheck, globalCode, func28, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.length_cons, List.length_nil, List.take, List.drop, List.cons_append, List.nil_append,
    Nat.reduceAdd, Nat.reduceSub]
  wp_packed_frame [hParams, hLength, hValues]
  refine wp_call_tw (Layout.tokenWeightOffset_exact env initial) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_packed_frame [hParams, hLength]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hParams, hLength]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hParams, hLength]
  refine wp_call_tw (Coefficients.exact env initial owner ptr weights tokenWeightOffset (50257 * 768)
    hWeights hExtent) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  apply hNext
  · rfl
  · simpa only [List.length_set] using hLength
  · rfl

theorem scales_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr : UInt64) (weights : ByteArray)
    (hWeights : ByteArrayAt initial.mem ptr.toNat weights) (hSize : weights.size = modelBytes) :
    ReadOnlyBoolean.BodySpec «module» env initial (parameters owner ptr weights) 64
      (globalCheck 0) (validScales weights tokenScaleOffset (50257)) := by
  intro frame hParams hLength hValues Q rest hNext
  simp only [parameters] at hParams
  have hExtent : tokenScaleOffset + (50257) * 4 ≤ weights.size := by rw [hSize]; decide
  simp only [globalCheck, globalCode, func28, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.length_cons, List.length_nil, List.take, List.drop, List.cons_append, List.nil_append,
    Nat.reduceAdd, Nat.reduceSub]
  wp_packed_frame [hParams, hLength, hValues]
  refine wp_call_tw (Layout.tokenScaleOffset_exact env initial) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_packed_frame [hParams, hLength]
  refine wp_call_tw (Scales.exact env initial owner ptr weights tokenScaleOffset (50257)
    hWeights hExtent) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  apply hNext
  · rfl
  · simpa only [List.length_set] using hLength
  · rfl

theorem positions_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr : UInt64) (weights : ByteArray)
    (hWeights : ByteArrayAt initial.mem ptr.toNat weights) (hSize : weights.size = modelBytes) :
    ReadOnlyBoolean.BodySpec «module» env initial (parameters owner ptr weights) 64
      (globalCheck 1) (finiteWords weights positionOffset (1024 * 768)) := by
  intro frame hParams hLength hValues Q rest hNext
  simp only [parameters] at hParams
  have hExtent : positionOffset + (1024 * 768) * 4 ≤ weights.size := by rw [hSize]; decide
  simp only [globalCheck, globalCode, func28, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.length_cons, List.length_nil, List.take, List.drop, List.cons_append, List.nil_append,
    Nat.reduceAdd, Nat.reduceSub]
  wp_packed_frame [hParams, hLength, hValues]
  refine wp_call_tw (Layout.positionOffset_exact env initial) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_packed_frame [hParams, hLength]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hParams, hLength]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hParams, hLength]
  refine wp_call_tw (FiniteWords.exact env initial owner ptr weights positionOffset (1024 * 768)
    hWeights hExtent) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  apply hNext
  · rfl
  · simpa only [List.length_set] using hLength
  · rfl

theorem normalization_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr : UInt64) (weights : ByteArray)
    (hWeights : ByteArrayAt initial.mem ptr.toNat weights) (hSize : weights.size = modelBytes) :
    ReadOnlyBoolean.BodySpec «module» env initial (parameters owner ptr weights) 64
      (globalCheck 2) (finiteWords weights finalNormOffset (1536)) := by
  intro frame hParams hLength hValues Q rest hNext
  simp only [parameters] at hParams
  have hExtent : finalNormOffset + (1536) * 4 ≤ weights.size := by rw [hSize]; decide
  simp only [globalCheck, globalCode, func28, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.length_cons, List.length_nil, List.take, List.drop, List.cons_append, List.nil_append,
    Nat.reduceAdd, Nat.reduceSub]
  wp_packed_frame [hParams, hLength, hValues]
  refine wp_call_tw (Layout.finalNormOffset_exact env initial) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_packed_frame [hParams, hLength]
  refine wp_call_tw (FiniteWords.exact env initial owner ptr weights finalNormOffset (1536)
    hWeights hExtent) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  apply hNext
  · rfl
  · simpa only [List.length_set] using hLength
  · rfl

#print axioms coefficients_spec
#print axioms scales_spec
#print axioms positions_spec
#print axioms normalization_spec
end Project.Gpt2QuantizedCached.Validation
