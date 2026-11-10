import LeanExe.Requests.DelimitedWords

/-!
Lemmas for steps that hold the delimited framing's segment and answer in the buffers of
`LeanExe/Requests/DelimitedWords.lean`, segments of at most 36 bytes, as the echo of records of
`tests/TestSupport/M7/Delim.lean` and the BMS step of `Demos/Bms/Program.lean` do.  A step stores
a received byte with `push40` while fewer than 36 bytes are stored, and its abstraction takes the
segment as the last `min len 36` bytes of the buffer (`seg_store`).  It writes the answer from
the start of a buffer, and its abstraction takes the bytes left to write as the first `k` bytes,
whose first byte `first40` reads (`headD_take`, `first40_val`) and which a write moves with
`push40` (`tail_take_push`).  `answer_rel` gives the encoded answer and its delimiter, and their
count, from the encoder's state after the answer's bytes.
-/

namespace LeanExe.Requests

/-- The encoded answer and its delimiter from the encoder's state after the answer's bytes. -/
theorem answer_rel {e : CobsEnc} {A : List UInt8} (h : EncRel e (encBack A))
    (hA : A.length ≤ 38) :
    (encFinish e).bytes.take (e.dlen + 2).toNat = cobsEncode A ++ [0] ∧
      2 ≤ (e.dlen + 2).toNat ∧ (e.dlen + 2).toNat ≤ 40 := by
  have hc := encFinish_count h hA
  have hl := (encBack_bounds A).1
  have hd : (e.dlen + 2).toNat = e.dlen.toNat + 2 := by rw [hc, h.dlen, hl]
  rw [hd]
  exact ⟨encFinish_spec h hA, by omega, by rw [h.dlen, hl]; omega⟩

theorem drop40 (b : Bytes40) : b.bytes.drop 40 = [] :=
  List.drop_eq_nil_of_le (by rw [length_bytes])

theorem seg_store (seg : Bytes40) (len v : UInt64) :
    (if len < 36 then push40 seg v else seg).bytes.drop
        (40 - min (if len ≤ 36 then len + 1 else len).toNat 36) =
      if len < 36 then seg.bytes.drop (40 - min len.toNat 36) ++ [(v &&& 255).toUInt8]
      else seg.bytes.drop (40 - min len.toNat 36) := by
  by_cases h : len < 36
  · have h' := UInt64.lt_iff_toNat_lt.mp h
    have hl : len ≤ 36 := UInt64.le_iff_toNat_le.mpr (by simp at h' ⊢; omega)
    rw [ite_eq_left h, ite_eq_left hl, ite_eq_left h, toNat_add_one (by simp at h'; omega),
      toUInt8_and255]
    simp at h'
    rw [show min (len.toNat + 1) 36 = len.toNat + 1 by omega,
      show min len.toNat 36 = len.toNat by omega, push40_drop _ (by omega)]
  · have h' : ¬len.toNat < 36 := fun e => h (UInt64.lt_iff_toNat_lt.mpr (by simpa using e))
    rw [ite_eq_right h, ite_eq_right h]
    split
    · next hl =>
      have hl' := UInt64.le_iff_toNat_le.mp hl
      simp at hl'
      rw [toNat_add_one (by omega), show min (len.toNat + 1) 36 = min len.toNat 36 by omega]
    · rfl

theorem headD_take {B : List UInt8} {k : Nat} (hk : 1 ≤ k) : (B.take k).headD 0 = B.headD 0 := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  cases B with
  | nil => rfl
  | cons a t => rfl

theorem tail_take_push {B : List UInt8} (hB : B.length = 40) {k : Nat} (hk : 1 ≤ k)
    (hk' : k ≤ 40) : (B.tail ++ [0]).take (k - 1) = (B.take k).tail := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  cases B with
  | nil => simp at hB
  | cons a t =>
      simp only [List.length_cons] at hB
      rw [List.tail_cons, List.take_succ_cons, List.tail_cons, Nat.add_sub_cancel,
        List.take_append_of_le_length (by omega)]

theorem first40_val (b : Bytes40) : (b.bytes.headD 0).toUInt64 = first40 b := by
  rw [← first40_eq]
  apply UInt64.toNat_inj.mp
  rw [UInt8.toNat_toUInt64, UInt64.toNat_toUInt8]
  have := first40_lt b
  omega

end LeanExe.Requests
