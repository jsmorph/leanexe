import Project.Gpt2QuantizedCached.Layout
import Project.ProofKit.PackedHeaderField

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.Header
open Wasm Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2.Quantized

def fields : List (Nat × UInt32) :=
  [(0, 0x4751584C), (4, 0x00325450), (8, 1), (12, 32),
    (16, 127695940), (20, 2), (24, 128), (28, 0)]

theorem emitted : func22 = func22.take 9 ++
    fields.flatMap (fun field => PackedHeaderField.program field.1 field.2) ++ func22.drop 17 := rfl

theorem source_eq (weights : ByteArray) : validHeader weights =
    fields.foldl (fun valid field => valid && (LeanExe.Packed.getUInt32LE! weights field.1 == field.2))
      (weights.size == modelBytes) := rfl

theorem exact (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr : UInt64) (weights : ByteArray)
    (hWeights : ByteArrayAt initial.mem ptr.toNat weights) :
    TerminatesWith env «module» 22 initial
      [.i64 (UInt64.ofNat weights.size), .i64 ptr, .i64 owner]
      (fun final values => final = initial ∧ values = [.i64 (if validHeader weights then 1 else 0)]) := by
  have hFit := hWeights.1
  have hSize64 : weights.size < UInt64.size := by change weights.size < 18446744073709551616; omega
  have hSizeEq : UInt64.ofNat weights.size = UInt64.ofNat modelBytes ↔ weights.size = modelBytes := by
    constructor
    · intro h
      have hh := congrArg UInt64.toNat h
      simpa only [UInt64.toNat_ofNat_of_lt' hSize64,
        UInt64.toNat_ofNat_of_lt' (by decide : modelBytes < UInt64.size)] using hh
    · intro h
      rw [h]
  refine TerminatesWith.of_wp_entry_for (f := func22Def) rfl ?_
  change wp «module» func22 _ initial
    { params := [.i64 owner, .i64 ptr, .i64 (UInt64.ofNat weights.size)],
      locals := List.replicate 5 (.i64 0) } env
  rw [emitted, List.append_assoc]
  simp only [func22, List.take, List.drop, List.cons_append, List.nil_append]
  refine wp_call_tw (Layout.modelBytes_exact env initial) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_packed_frame []
  refine wp_iff_cons rfl ?_
  by_cases hSize : weights.size = modelBytes
  all_goals
    first
      | rw [ite_eq_left (by simpa [hSizeEq, hSize])]
      | rw [ite_eq_right (by simpa [hSizeEq, hSize])]
    wp_packed_frame []
    apply PackedHeaderField.fields_spec fields «module» env initial _ owner ptr weights
      (weights.size == modelBytes) [] hWeights
    · intro h field hf
      have hSize := beq_iff_eq.mp h
      rw [hSize]
      simp only [fields, List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · rfl
    · simp
    · simp [hSize]
    intro result hParams hLength hValues
    rw [← source_eq] at hValues
    simp only [wp_iff_control_types]
    refine wp_iff_cons hValues ?_
    cases hHeader : validHeader weights
    all_goals
      first
        | rw [ite_eq_left (by simpa [hHeader])]
        | rw [ite_eq_right (by simpa [hHeader])]
      wp_packed_frame [hParams, hLength]
      simp [func22Def, hHeader]

#print axioms exact

end Project.Gpt2QuantizedCached.Header
