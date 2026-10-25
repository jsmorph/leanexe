import Demos.StreamFold.Control

namespace Demos.StreamFold

open LeanExe LeanExe.Wasi

variable {Acc : Type}

def byteWords (bytes : Bytes) : List UInt64 :=
  bytes.data.data.toList.map UInt8.toUInt64

@[simp] theorem byteWords_length (bytes : Bytes) : (byteWords bytes).length = bytes.data.size := by
  change (bytes.data.data.toList.map UInt8.toUInt64).length = bytes.data.data.size
  rw [List.length_map, Array.length_toList]

@[simp] theorem byteWords_empty : byteWords Bytes.empty = [] := rfl

theorem byteWords_get (bytes : Bytes) (index : UInt64) (bound : index.toNat < bytes.data.size) :
    (byteWords bytes)[index.toNat]'(by simpa using bound) = bytes.get index := by
  simp only [byteWords, List.getElem_map, Array.getElem_toList, Bytes.get, bound, ↓reduceDIte]
  rfl

theorem byteWords_get_nat (bytes : Bytes) (bound : bytes.data.size < UInt64.size)
    (index : Nat) (inside : index < bytes.data.size) :
    (byteWords bytes)[index]'(by simpa using inside) = bytes.get index.toUInt64 := by
  have indexNat : index.toUInt64.toNat = index := UInt64.toNat_ofNat_of_lt' (by omega)
  simpa only [indexNat] using byteWords_get bytes index.toUInt64 (by omega)

theorem byteWords_build_get (count : UInt64) (element : UInt64 → UInt64) (index : Nat)
    (inside : index < count.toNat) :
    (byteWords (Bytes.build count element))[index]'(by simpa using inside) =
      (element (UInt64.ofNat index)).toUInt8.toUInt64 := by
  simp [byteWords, Bytes.build]

theorem bytes_get_narrow (bytes : Bytes) (index : UInt64) :
    (bytes.get index).toUInt8.toUInt64 = bytes.get index := by
  unfold Bytes.get
  split <;> simp

theorem remainingOutput_words {state : (BufferState Acc)}
    (size : state.output.data.size < UInt64.size)
    (written : state.written.toNat ≤ state.output.data.size) :
    byteWords (remainingOutput state) = (byteWords state.output).drop state.written.toNat := by
  have sizeNat : state.output.size.toNat = state.output.data.size := Bytes.size_toNat state.output size
  have writtenLe : state.written ≤ state.output.size := UInt64.le_iff_toNat_le.mpr (by
    rw [sizeNat]
    exact written)
  have countNat : (state.output.size - state.written).toNat =
      state.output.data.size - state.written.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ writtenLe, sizeNat]
  unfold remainingOutput
  apply List.ext_getElem
  · simp only [byteWords_length, Bytes.data_size_build, List.length_drop, countNat]
  · intro index left right
    have indexBound : index < state.output.data.size - state.written.toNat := by
      simpa only [byteWords_length, Bytes.data_size_build, countNat] using left
    have indexNat : (UInt64.ofNat index).toNat = index := UInt64.toNat_ofNat_of_lt' (by omega)
    have sumNat : (state.written + UInt64.ofNat index).toNat = state.written.toNat + index := by
      rw [UInt64.toNat_add, indexNat]
      exact Nat.mod_eq_of_lt (show state.written.toNat + index < UInt64.size by omega)
    rw [byteWords_build_get (state.output.size - state.written)
      (fun i => state.output.get (state.written + i)) index (by rw [countNat]; exact indexBound),
      bytes_get_narrow]
    rw [List.getElem_drop]
    simpa only [sumNat] using
      (byteWords_get state.output (state.written + UInt64.ofNat index) (by omega)).symm

theorem remainingOutput_words_safe {state : (BufferState Acc)} (safe : Safe state) :
    byteWords (remainingOutput state) = (byteWords state.output).drop state.written.toNat :=
  remainingOutput_words safe.outputSize safe.written_le

theorem afterWrite_error (state : (BufferState Acc)) (reply : WriteResult) (error : reply.errno ≠ 0) :
    afterWrite state reply = ⟨false, reply.errno, state⟩ := by
  simp [afterWrite, error]

theorem afterWrite_zero (state : (BufferState Acc)) (pending : state.written < state.output.size) :
    afterWrite state ⟨0, 0⟩ = ⟨true, 0, state⟩ := by
  have different : state.written ≠ state.output.size := by
    intro same
    rw [same, UInt64.lt_iff_toNat_lt] at pending
    omega
  simp [afterWrite, different]

theorem afterWrite_sum {state : (BufferState Acc)} (safe : Safe state) (count : UInt64)
    (bound : count.toNat ≤ (remainingOutput state).data.size) :
    (state.written + count).toNat = state.written.toNat + count.toNat ∧
      state.written.toNat + count.toNat ≤ state.output.data.size := by
  rw [remainingOutput_size safe] at bound
  have old := safe.written_le
  have total : state.written.toNat + count.toNat ≤ state.output.data.size := by omega
  exact ⟨by rw [UInt64.toNat_add, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt total safe.outputSize)], total⟩

theorem afterWrite_complete {state : (BufferState Acc)} (safe : Safe state) (count : UInt64)
    (complete : count.toNat = (remainingOutput state).data.size) :
    afterWrite state ⟨0, count⟩ =
      ⟨true, 0, { state with output := Bytes.empty, written := 0 }⟩ := by
  have sum := afterWrite_sum safe count (Nat.le_of_eq complete)
  have equals : state.written + count = state.output.size := by
    apply UInt64.toNat.inj
    rw [sum.1, safe.output_toNat, remainingOutput_size safe] at *
    have old := safe.written_le
    omega
  simp [afterWrite, equals]

theorem afterWrite_remaining {state : (BufferState Acc)} (safe : Safe state) (count : UInt64)
    (bound : count.toNat ≤ (remainingOutput state).data.size) :
    byteWords (remainingOutput (afterWrite state ⟨0, count⟩).state) =
      (byteWords (remainingOutput state)).drop count.toNat := by
  have sum := afterWrite_sum safe count bound
  have nextSafe := afterWrite_safe safe count bound
  rw [remainingOutput_words_safe nextSafe, remainingOutput_words_safe safe]
  simp only [afterWrite, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  split
  · rename_i complete
    have same : state.written + count = state.output.size := by simpa using complete
    have sameNat := congrArg UInt64.toNat same
    rw [sum.1, safe.output_toNat] at sameNat
    simp only [byteWords_empty, UInt64.toNat_zero, List.drop_zero, List.drop_drop]
    exact (List.drop_eq_nil_of_le (by rw [byteWords_length]; omega)).symm
  · simp only [sum.1, List.drop_drop]

theorem afterWrite_conservation {state : (BufferState Acc)} (safe : Safe state) (count : UInt64)
    (bound : count.toNat ≤ (remainingOutput state).data.size) (committed : List UInt64) :
    (committed ++ (byteWords (remainingOutput state)).take count.toNat) ++
        byteWords (remainingOutput (afterWrite state ⟨0, count⟩).state) =
      committed ++ byteWords (remainingOutput state) := by
  rw [afterWrite_remaining safe count bound, List.append_assoc, List.take_append_drop]

end Demos.StreamFold
