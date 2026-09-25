import Project.Gpt2QuantizedCached.Coefficients
import Project.Gpt2QuantizedCached.Scales
import Project.Gpt2QuantizedCached.FiniteWords
import Project.Gpt2QuantizedCached.Layout
import Project.ProofKit.ReadOnlyBoolean

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.BlockValidation
open Wasm Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2.Quantized

def parameters (owner ptr : UInt64) (weights : ByteArray) (base : Nat) : List Value :=
  [.i64 owner, .i64 ptr, .i64 (UInt64.ofNat weights.size), .i64 (UInt64.ofNat base)]

def checkBody (index : Nat) : Program :=
  match func27[19 + index]? with
  | some (.iff _ _ body _ _ _) => body.take (body.length - 3)
  | _ => []

theorem check0_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr : UInt64) (weights : ByteArray) (base : Nat)
    (hWeights : ByteArrayAt initial.mem ptr.toNat weights)
    (hExtent : base + blockBytes ≤ weights.size) :
    ReadOnlyBoolean.BodySpec «module» env initial (parameters owner ptr weights base) 69
      (checkBody 0) (validCoefficients weights (base + qkvWeightOffset) (768 * 2304)) := by
  intro frame hParams hLength hValues Q rest hNext
  simp only [parameters] at hParams
  have hFit := hWeights.1
  have hOffset : base + qkvWeightOffset + (768 * 2304) * 1 ≤ weights.size := by
    change base + qkvWeightOffset + (768 * 2304) * 1 ≤ weights.size
    have hLayout : qkvWeightOffset + (768 * 2304) * 1 ≤ blockBytes := by decide
    omega
  have hAdd := CheckedNatAdd.guard_of_fits base qkvWeightOffset
    (by change base + qkvWeightOffset < 18446744073709551616; omega)
  simp only [checkBody, func27, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.length_cons, List.length_nil, List.take, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLength, hValues]
  refine wp_call_tw (Layout.qkvWeightOffset_exact env initial) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_packed_frame [hParams, hLength]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hAdd)]
  wp_packed_frame [hParams, hLength, ← UInt64.ofNat_add]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hParams, hLength]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hParams, hLength]
  refine wp_call_tw (Coefficients.exact env initial owner ptr weights (base + qkvWeightOffset)
    (768 * 2304) hWeights (by simpa using hOffset)) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  apply hNext
  · rfl
  · simp [hLength]
  · rfl

theorem check1_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr : UInt64) (weights : ByteArray) (base : Nat)
    (hWeights : ByteArrayAt initial.mem ptr.toNat weights)
    (hExtent : base + blockBytes ≤ weights.size) :
    ReadOnlyBoolean.BodySpec «module» env initial (parameters owner ptr weights base) 69
      (checkBody 1) (validScales weights (base + qkvScaleOffset) (2304)) := by
  intro frame hParams hLength hValues Q rest hNext
  simp only [parameters] at hParams
  have hFit := hWeights.1
  have hOffset : base + qkvScaleOffset + (2304) * 4 ≤ weights.size := by
    change base + qkvScaleOffset + (2304) * 4 ≤ weights.size
    have hLayout : qkvScaleOffset + (2304) * 4 ≤ blockBytes := by decide
    omega
  have hAdd := CheckedNatAdd.guard_of_fits base qkvScaleOffset
    (by change base + qkvScaleOffset < 18446744073709551616; omega)
  simp only [checkBody, func27, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.length_cons, List.length_nil, List.take, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLength, hValues]
  refine wp_call_tw (Layout.qkvScaleOffset_exact env initial) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_packed_frame [hParams, hLength]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hAdd)]
  wp_packed_frame [hParams, hLength, ← UInt64.ofNat_add]
  refine wp_call_tw (Scales.exact env initial owner ptr weights (base + qkvScaleOffset)
    (2304) hWeights (by simpa using hOffset)) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  apply hNext
  · rfl
  · simp [hLength]
  · rfl

theorem check2_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr : UInt64) (weights : ByteArray) (base : Nat)
    (hWeights : ByteArrayAt initial.mem ptr.toNat weights)
    (hExtent : base + blockBytes ≤ weights.size) :
    ReadOnlyBoolean.BodySpec «module» env initial (parameters owner ptr weights base) 69
      (checkBody 2) (finiteWords weights (base + qkvBiasOffset) (2304)) := by
  intro frame hParams hLength hValues Q rest hNext
  simp only [parameters] at hParams
  have hFit := hWeights.1
  have hOffset : base + qkvBiasOffset + (2304) * 4 ≤ weights.size := by
    change base + qkvBiasOffset + (2304) * 4 ≤ weights.size
    have hLayout : qkvBiasOffset + (2304) * 4 ≤ blockBytes := by decide
    omega
  have hAdd := CheckedNatAdd.guard_of_fits base qkvBiasOffset
    (by change base + qkvBiasOffset < 18446744073709551616; omega)
  simp only [checkBody, func27, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.length_cons, List.length_nil, List.take, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLength, hValues]
  refine wp_call_tw (Layout.qkvBiasOffset_exact env initial) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_packed_frame [hParams, hLength]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hAdd)]
  wp_packed_frame [hParams, hLength, ← UInt64.ofNat_add]
  refine wp_call_tw (FiniteWords.exact env initial owner ptr weights (base + qkvBiasOffset)
    (2304) hWeights (by simpa using hOffset)) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  apply hNext
  · rfl
  · simp [hLength]
  · rfl

theorem check3_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr : UInt64) (weights : ByteArray) (base : Nat)
    (hWeights : ByteArrayAt initial.mem ptr.toNat weights)
    (hExtent : base + blockBytes ≤ weights.size) :
    ReadOnlyBoolean.BodySpec «module» env initial (parameters owner ptr weights base) 69
      (checkBody 3) (validCoefficients weights (base + attnWeightOffset) (768 * 768)) := by
  intro frame hParams hLength hValues Q rest hNext
  simp only [parameters] at hParams
  have hFit := hWeights.1
  have hOffset : base + attnWeightOffset + (768 * 768) * 1 ≤ weights.size := by
    change base + attnWeightOffset + (768 * 768) * 1 ≤ weights.size
    have hLayout : attnWeightOffset + (768 * 768) * 1 ≤ blockBytes := by decide
    omega
  have hAdd := CheckedNatAdd.guard_of_fits base attnWeightOffset
    (by change base + attnWeightOffset < 18446744073709551616; omega)
  simp only [checkBody, func27, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.length_cons, List.length_nil, List.take, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLength, hValues]
  refine wp_call_tw (Layout.attnWeightOffset_exact env initial) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_packed_frame [hParams, hLength]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hAdd)]
  wp_packed_frame [hParams, hLength, ← UInt64.ofNat_add]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hParams, hLength]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hParams, hLength]
  refine wp_call_tw (Coefficients.exact env initial owner ptr weights (base + attnWeightOffset)
    (768 * 768) hWeights (by simpa using hOffset)) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  apply hNext
  · rfl
  · simp [hLength]
  · rfl

theorem check4_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr : UInt64) (weights : ByteArray) (base : Nat)
    (hWeights : ByteArrayAt initial.mem ptr.toNat weights)
    (hExtent : base + blockBytes ≤ weights.size) :
    ReadOnlyBoolean.BodySpec «module» env initial (parameters owner ptr weights base) 69
      (checkBody 4) (validScales weights (base + attnScaleOffset) (768)) := by
  intro frame hParams hLength hValues Q rest hNext
  simp only [parameters] at hParams
  have hFit := hWeights.1
  have hOffset : base + attnScaleOffset + (768) * 4 ≤ weights.size := by
    change base + attnScaleOffset + (768) * 4 ≤ weights.size
    have hLayout : attnScaleOffset + (768) * 4 ≤ blockBytes := by decide
    omega
  have hAdd := CheckedNatAdd.guard_of_fits base attnScaleOffset
    (by change base + attnScaleOffset < 18446744073709551616; omega)
  simp only [checkBody, func27, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.length_cons, List.length_nil, List.take, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLength, hValues]
  refine wp_call_tw (Layout.attnScaleOffset_exact env initial) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_packed_frame [hParams, hLength]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hAdd)]
  wp_packed_frame [hParams, hLength, ← UInt64.ofNat_add]
  refine wp_call_tw (Scales.exact env initial owner ptr weights (base + attnScaleOffset)
    (768) hWeights (by simpa using hOffset)) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  apply hNext
  · rfl
  · simp [hLength]
  · rfl

theorem check5_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr : UInt64) (weights : ByteArray) (base : Nat)
    (hWeights : ByteArrayAt initial.mem ptr.toNat weights)
    (hExtent : base + blockBytes ≤ weights.size) :
    ReadOnlyBoolean.BodySpec «module» env initial (parameters owner ptr weights base) 69
      (checkBody 5) (finiteWords weights (base + attnBiasOffset) (768 * 3)) := by
  intro frame hParams hLength hValues Q rest hNext
  simp only [parameters] at hParams
  have hFit := hWeights.1
  have hOffset : base + attnBiasOffset + (768 * 3) * 4 ≤ weights.size := by
    change base + attnBiasOffset + (768 * 3) * 4 ≤ weights.size
    have hLayout : attnBiasOffset + (768 * 3) * 4 ≤ blockBytes := by decide
    omega
  have hAdd := CheckedNatAdd.guard_of_fits base attnBiasOffset
    (by change base + attnBiasOffset < 18446744073709551616; omega)
  simp only [checkBody, func27, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.length_cons, List.length_nil, List.take, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLength, hValues]
  refine wp_call_tw (Layout.attnBiasOffset_exact env initial) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_packed_frame [hParams, hLength]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hAdd)]
  wp_packed_frame [hParams, hLength, ← UInt64.ofNat_add]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hParams, hLength]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hParams, hLength]
  refine wp_call_tw (FiniteWords.exact env initial owner ptr weights (base + attnBiasOffset)
    (768 * 3) hWeights (by simpa using hOffset)) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  apply hNext
  · rfl
  · simp [hLength]
  · rfl

theorem check6_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr : UInt64) (weights : ByteArray) (base : Nat)
    (hWeights : ByteArrayAt initial.mem ptr.toNat weights)
    (hExtent : base + blockBytes ≤ weights.size) :
    ReadOnlyBoolean.BodySpec «module» env initial (parameters owner ptr weights base) 69
      (checkBody 6) (validCoefficients weights (base + fcWeightOffset) (768 * 3072)) := by
  intro frame hParams hLength hValues Q rest hNext
  simp only [parameters] at hParams
  have hFit := hWeights.1
  have hOffset : base + fcWeightOffset + (768 * 3072) * 1 ≤ weights.size := by
    change base + fcWeightOffset + (768 * 3072) * 1 ≤ weights.size
    have hLayout : fcWeightOffset + (768 * 3072) * 1 ≤ blockBytes := by decide
    omega
  have hAdd := CheckedNatAdd.guard_of_fits base fcWeightOffset
    (by change base + fcWeightOffset < 18446744073709551616; omega)
  simp only [checkBody, func27, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.length_cons, List.length_nil, List.take, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLength, hValues]
  refine wp_call_tw (Layout.fcWeightOffset_exact env initial) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_packed_frame [hParams, hLength]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hAdd)]
  wp_packed_frame [hParams, hLength, ← UInt64.ofNat_add]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hParams, hLength]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hParams, hLength]
  refine wp_call_tw (Coefficients.exact env initial owner ptr weights (base + fcWeightOffset)
    (768 * 3072) hWeights (by simpa using hOffset)) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  apply hNext
  · rfl
  · simp [hLength]
  · rfl

theorem check7_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr : UInt64) (weights : ByteArray) (base : Nat)
    (hWeights : ByteArrayAt initial.mem ptr.toNat weights)
    (hExtent : base + blockBytes ≤ weights.size) :
    ReadOnlyBoolean.BodySpec «module» env initial (parameters owner ptr weights base) 69
      (checkBody 7) (validScales weights (base + fcScaleOffset) (3072)) := by
  intro frame hParams hLength hValues Q rest hNext
  simp only [parameters] at hParams
  have hFit := hWeights.1
  have hOffset : base + fcScaleOffset + (3072) * 4 ≤ weights.size := by
    change base + fcScaleOffset + (3072) * 4 ≤ weights.size
    have hLayout : fcScaleOffset + (3072) * 4 ≤ blockBytes := by decide
    omega
  have hAdd := CheckedNatAdd.guard_of_fits base fcScaleOffset
    (by change base + fcScaleOffset < 18446744073709551616; omega)
  simp only [checkBody, func27, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.length_cons, List.length_nil, List.take, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLength, hValues]
  refine wp_call_tw (Layout.fcScaleOffset_exact env initial) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_packed_frame [hParams, hLength]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hAdd)]
  wp_packed_frame [hParams, hLength, ← UInt64.ofNat_add]
  refine wp_call_tw (Scales.exact env initial owner ptr weights (base + fcScaleOffset)
    (3072) hWeights (by simpa using hOffset)) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  apply hNext
  · rfl
  · simp [hLength]
  · rfl

theorem check8_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr : UInt64) (weights : ByteArray) (base : Nat)
    (hWeights : ByteArrayAt initial.mem ptr.toNat weights)
    (hExtent : base + blockBytes ≤ weights.size) :
    ReadOnlyBoolean.BodySpec «module» env initial (parameters owner ptr weights base) 69
      (checkBody 8) (finiteWords weights (base + fcBiasOffset) (3072)) := by
  intro frame hParams hLength hValues Q rest hNext
  simp only [parameters] at hParams
  have hFit := hWeights.1
  have hOffset : base + fcBiasOffset + (3072) * 4 ≤ weights.size := by
    change base + fcBiasOffset + (3072) * 4 ≤ weights.size
    have hLayout : fcBiasOffset + (3072) * 4 ≤ blockBytes := by decide
    omega
  have hAdd := CheckedNatAdd.guard_of_fits base fcBiasOffset
    (by change base + fcBiasOffset < 18446744073709551616; omega)
  simp only [checkBody, func27, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.length_cons, List.length_nil, List.take, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLength, hValues]
  refine wp_call_tw (Layout.fcBiasOffset_exact env initial) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_packed_frame [hParams, hLength]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hAdd)]
  wp_packed_frame [hParams, hLength, ← UInt64.ofNat_add]
  refine wp_call_tw (FiniteWords.exact env initial owner ptr weights (base + fcBiasOffset)
    (3072) hWeights (by simpa using hOffset)) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  apply hNext
  · rfl
  · simp [hLength]
  · rfl

theorem check9_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr : UInt64) (weights : ByteArray) (base : Nat)
    (hWeights : ByteArrayAt initial.mem ptr.toNat weights)
    (hExtent : base + blockBytes ≤ weights.size) :
    ReadOnlyBoolean.BodySpec «module» env initial (parameters owner ptr weights base) 69
      (checkBody 9) (validCoefficients weights (base + mlpWeightOffset) (3072 * 768)) := by
  intro frame hParams hLength hValues Q rest hNext
  simp only [parameters] at hParams
  have hFit := hWeights.1
  have hOffset : base + mlpWeightOffset + (3072 * 768) * 1 ≤ weights.size := by
    change base + mlpWeightOffset + (3072 * 768) * 1 ≤ weights.size
    have hLayout : mlpWeightOffset + (3072 * 768) * 1 ≤ blockBytes := by decide
    omega
  have hAdd := CheckedNatAdd.guard_of_fits base mlpWeightOffset
    (by change base + mlpWeightOffset < 18446744073709551616; omega)
  simp only [checkBody, func27, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.length_cons, List.length_nil, List.take, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLength, hValues]
  refine wp_call_tw (Layout.mlpWeightOffset_exact env initial) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_packed_frame [hParams, hLength]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hAdd)]
  wp_packed_frame [hParams, hLength, ← UInt64.ofNat_add]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hParams, hLength]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hParams, hLength]
  refine wp_call_tw (Coefficients.exact env initial owner ptr weights (base + mlpWeightOffset)
    (3072 * 768) hWeights (by simpa using hOffset)) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  apply hNext
  · rfl
  · simp [hLength]
  · rfl

theorem check10_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr : UInt64) (weights : ByteArray) (base : Nat)
    (hWeights : ByteArrayAt initial.mem ptr.toNat weights)
    (hExtent : base + blockBytes ≤ weights.size) :
    ReadOnlyBoolean.BodySpec «module» env initial (parameters owner ptr weights base) 69
      (checkBody 10) (validScales weights (base + mlpScaleOffset) (768)) := by
  intro frame hParams hLength hValues Q rest hNext
  simp only [parameters] at hParams
  have hFit := hWeights.1
  have hOffset : base + mlpScaleOffset + (768) * 4 ≤ weights.size := by
    change base + mlpScaleOffset + (768) * 4 ≤ weights.size
    have hLayout : mlpScaleOffset + (768) * 4 ≤ blockBytes := by decide
    omega
  have hAdd := CheckedNatAdd.guard_of_fits base mlpScaleOffset
    (by change base + mlpScaleOffset < 18446744073709551616; omega)
  simp only [checkBody, func27, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.length_cons, List.length_nil, List.take, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLength, hValues]
  refine wp_call_tw (Layout.mlpScaleOffset_exact env initial) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_packed_frame [hParams, hLength]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hAdd)]
  wp_packed_frame [hParams, hLength, ← UInt64.ofNat_add]
  refine wp_call_tw (Scales.exact env initial owner ptr weights (base + mlpScaleOffset)
    (768) hWeights (by simpa using hOffset)) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  apply hNext
  · rfl
  · simp [hLength]
  · rfl

theorem check11_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr : UInt64) (weights : ByteArray) (base : Nat)
    (hWeights : ByteArrayAt initial.mem ptr.toNat weights)
    (hExtent : base + blockBytes ≤ weights.size) :
    ReadOnlyBoolean.BodySpec «module» env initial (parameters owner ptr weights base) 69
      (checkBody 11) (finiteWords weights (base + mlpBiasOffset) (768)) := by
  intro frame hParams hLength hValues Q rest hNext
  simp only [parameters] at hParams
  have hFit := hWeights.1
  have hOffset : base + mlpBiasOffset + (768) * 4 ≤ weights.size := by
    change base + mlpBiasOffset + (768) * 4 ≤ weights.size
    have hLayout : mlpBiasOffset + (768) * 4 ≤ blockBytes := by decide
    omega
  have hAdd := CheckedNatAdd.guard_of_fits base mlpBiasOffset
    (by change base + mlpBiasOffset < 18446744073709551616; omega)
  simp only [checkBody, func27, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.length_cons, List.length_nil, List.take, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLength, hValues]
  refine wp_call_tw (Layout.mlpBiasOffset_exact env initial) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_packed_frame [hParams, hLength]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hAdd)]
  wp_packed_frame [hParams, hLength, ← UInt64.ofNat_add]
  refine wp_call_tw (FiniteWords.exact env initial owner ptr weights (base + mlpBiasOffset)
    (768) hWeights (by simpa using hOffset)) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  apply hNext
  · rfl
  · simp [hLength]
  · rfl

def checks (weights : ByteArray) (base : Nat) : List (Program × Bool) :=
  [(checkBody 0, validCoefficients weights (base + qkvWeightOffset) (768 * 2304)),
   (checkBody 1, validScales weights (base + qkvScaleOffset) (2304)),
   (checkBody 2, finiteWords weights (base + qkvBiasOffset) (2304)),
   (checkBody 3, validCoefficients weights (base + attnWeightOffset) (768 * 768)),
   (checkBody 4, validScales weights (base + attnScaleOffset) (768)),
   (checkBody 5, finiteWords weights (base + attnBiasOffset) (768 * 3)),
   (checkBody 6, validCoefficients weights (base + fcWeightOffset) (768 * 3072)),
   (checkBody 7, validScales weights (base + fcScaleOffset) (3072)),
   (checkBody 8, finiteWords weights (base + fcBiasOffset) (3072)),
   (checkBody 9, validCoefficients weights (base + mlpWeightOffset) (3072 * 768)),
   (checkBody 10, validScales weights (base + mlpScaleOffset) (768)),
   (checkBody 11, finiteWords weights (base + mlpBiasOffset) (768))]

theorem emitted_checks (weights : ByteArray) (base : Nat) :
    func27 = func27.take 19 ++
      (checks weights base).flatMap (fun entry => ReadOnlyBoolean.andProgram entry.1) ++
      func27.drop 31 := rfl

theorem checks_source (weights : ByteArray) (base : Nat) :
    (checks weights base).foldl (fun valid entry => valid && entry.2)
      (finiteWords weights base 1536) = validBlock weights base := rfl

theorem exact (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr : UInt64) (weights : ByteArray) (base : Nat)
    (hWeights : ByteArrayAt initial.mem ptr.toNat weights)
    (hExtent : base + blockBytes ≤ weights.size) :
    TerminatesWith env «module» 27 initial
      [.i64 (UInt64.ofNat base), .i64 (UInt64.ofNat weights.size), .i64 ptr, .i64 owner]
      (fun final values => final = initial ∧ values = [.i64 (if validBlock weights base then 1 else 0)]) := by
  have hChecks : ∀ entry ∈ checks weights base,
      ReadOnlyBoolean.BodySpec «module» env initial (parameters owner ptr weights base) 69 entry.1 entry.2 := by
    intro entry hEntry
    simp only [checks, List.mem_cons, List.not_mem_nil, or_false] at hEntry
    rcases hEntry with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact check0_spec env initial owner ptr weights base hWeights hExtent
    · exact check1_spec env initial owner ptr weights base hWeights hExtent
    · exact check2_spec env initial owner ptr weights base hWeights hExtent
    · exact check3_spec env initial owner ptr weights base hWeights hExtent
    · exact check4_spec env initial owner ptr weights base hWeights hExtent
    · exact check5_spec env initial owner ptr weights base hWeights hExtent
    · exact check6_spec env initial owner ptr weights base hWeights hExtent
    · exact check7_spec env initial owner ptr weights base hWeights hExtent
    · exact check8_spec env initial owner ptr weights base hWeights hExtent
    · exact check9_spec env initial owner ptr weights base hWeights hExtent
    · exact check10_spec env initial owner ptr weights base hWeights hExtent
    · exact check11_spec env initial owner ptr weights base hWeights hExtent
  refine TerminatesWith.of_wp_entry_for (f := func27Def) rfl ?_
  change wp «module» func27 _ initial
    { params := parameters owner ptr weights base, locals := List.replicate 69 (.i64 0) } env
  rw [emitted_checks weights base, List.append_assoc]
  simp only [func27, List.take, List.drop, List.cons_append, List.nil_append]
  wp_packed_frame [parameters]
  refine wp_call_tw (FiniteWords.exact env initial owner ptr weights base 1536 hWeights
    (by
      have : 1536 * 4 ≤ blockBytes := by decide
      omega)) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_packed_frame []
  apply ReadOnlyBoolean.chain_spec (checks weights base) «module» env initial
    (parameters owner ptr weights base) 69 (finiteWords weights base 1536) hChecks
  · rfl
  · simp
  · cases finiteWords weights base 1536 <;> rfl
  intro result hParams hLength hValues
  rw [checks_source] at hValues
  simp only [wp_iff_control_types]
  refine wp_iff_cons hValues ?_
  cases hValid : validBlock weights base
  all_goals
    first | rw [ite_eq_left (by simpa [hValid])] | rw [ite_eq_right (by simpa [hValid])]
    wp_packed_frame [hParams, hLength, parameters]
    simp [func27Def, hValid]

#print axioms exact
end Project.Gpt2QuantizedCached.BlockValidation
