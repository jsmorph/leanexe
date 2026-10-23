import Library.Hashing.Sha2.Impl.SHA256
import Library.Hashing.Sha2.Equiv.SHA256.Lift
import Library.Hashing.Sha2.Equiv.SHA256.ToU32s
import Library.Hashing.Sha2.Equiv.Common.ByteArray
import Library.Hashing.Sha2.Equiv.Common.ArrayFold

/-! # SHA-256 padding: byte-level layout

Reifies the streaming pad inside `Impl.sha256` as `implPaddedBytes`
and its 64-byte block view `implPaddedBlocks`, then proves the
byte-by-byte layout in three cases:
- `complete`: a fully-data block (`k < data.size / 64`)
- `final<56`: one extra block holding data, `0x80`, zeros, length
- `final≥56`: two tail blocks — A holds data + `0x80` + zeros, B holds
  zeros + length. -/

open SHS.Equiv.ByteArray
open SHS.Equiv.ArrayFold
open SHS.Equiv.SHA256.Lift
open SHS.Equiv.SHA256.ToU32s

open SHS.SHA256

namespace SHS.Equiv.SHA256.Padding.Layout

open scoped SHS.SHA256

/-! ## Byte-level definitions -/

/-- Number of zero bytes the streaming pad emits between the `0x80`
separator and the 8-byte length tag.  Lifts the inline conditional out
of every `implPaddedBytes`-related signature. -/
def zerosCount (data : ByteArray) : Nat :=
  if data.size % 64 < 56 then 55 - data.size % 64 else 64 + 55 - data.size % 64

theorem zerosCount_lt56 (data : ByteArray) (h : data.size % 64 < 56) :
    zerosCount data = 55 - data.size % 64 := by
  unfold zerosCount; rw [if_pos h]

theorem zerosCount_ge56 (data : ByteArray) (h : ¬ data.size % 64 < 56) :
    zerosCount data = 64 + 55 - data.size % 64 := by
  unfold zerosCount; rw [if_neg h]

/-- The 64-bit big-endian length encoding (eight bytes), matching the
inline expansion in `Impl.sha256`'s final block. -/
def lengthBE64 (bits : UInt64) : ByteArray := Id.run do
  let mut bs : ByteArray := ByteArray.empty
  for i in [0:8] do
    bs := bs.push ((bits >>> ((7 - i) * 8).toUInt64) &&& 0xff).toUInt8
  return bs

/-- Reified streaming pad of `Impl.sha256`.  Mirrors the impl's logic
without unfolding `sha256`: append `data`, then `0x80`, then enough zeros
to land at 56 mod 64, then the 64-bit big-endian bit-length. -/
def implPaddedBytes (data : ByteArray) : ByteArray :=
  let totalBits : UInt64 := data.size.toUInt64 <<< 3
  appendZeros (data.push 0x80) (zerosCount data) ++ lengthBE64 totalBits

/-- Slice the padded byte sequence into 64-byte blocks. -/
def implPaddedBlocks (data : ByteArray) : Array (Vector UInt8 64) :=
  let padded := implPaddedBytes data
  let n := padded.size / 64
  Array.ofFn (n := n) fun i =>
    Vector.ofFn fun (j : Fin 64) =>
      padded.get! (i.val * 64 + j.val)

/-! ## Easy invariants -/

@[simp] theorem size_lengthBE64 (bits : UInt64) : (lengthBE64 bits).size = 8 := by
  unfold lengthBE64
  simp [Id.run]
  rfl

theorem size_implPaddedBytes_mod (data : ByteArray) :
    (implPaddedBytes data).size % 64 = 0 := by
  unfold implPaddedBytes zerosCount
  simp [ByteArray.size_append]
  split <;> omega

theorem size_implPaddedBytes_eq (data : ByteArray) :
    (implPaddedBytes data).size = data.size + 1 + zerosCount data + 8 := by
  unfold implPaddedBytes
  simp [ByteArray.size_append]

/-! ## Byte access on `implPaddedBytes` -/

theorem get!_implPaddedBytes_data (data : ByteArray) (i : Nat) (h : i < data.size) :
    (implPaddedBytes data).get! i = data.get! i := by
  unfold implPaddedBytes
  have hsz1 : i < (appendZeros (data.push 0x80) (zerosCount data)).size := by
    rw [size_appendZeros, ByteArray.size_push]; omega
  rw [get!_append_left _ _ _ hsz1]
  rw [get!_appendZeros_lt _ _ _ (by rw [ByteArray.size_push]; omega)]
  rw [get!_push_lt _ _ _ h]

theorem get!_implPaddedBytes_sep (data : ByteArray) :
    (implPaddedBytes data).get! data.size = 0x80 := by
  unfold implPaddedBytes
  have hsz1 : data.size <
      (appendZeros (data.push 0x80) (zerosCount data)).size := by
    rw [size_appendZeros, ByteArray.size_push]; omega
  rw [get!_append_left _ _ _ hsz1]
  rw [get!_appendZeros_lt _ _ _ (by rw [ByteArray.size_push]; omega)]
  exact get!_push_eq _ _

theorem get!_implPaddedBytes_zero (data : ByteArray) (i : Nat)
    (h1 : data.size + 1 ≤ i) (h2 : i < data.size + 1 + zerosCount data) :
    (implPaddedBytes data).get! i = 0 := by
  unfold implPaddedBytes
  have hsz1 : i < (appendZeros (data.push 0x80) (zerosCount data)).size := by
    rw [size_appendZeros, ByteArray.size_push]; omega
  rw [get!_append_left _ _ _ hsz1]
  apply get!_appendZeros_ge
  · rw [ByteArray.size_push]; omega
  · rw [ByteArray.size_push]; omega

theorem get!_implPaddedBytes_length (data : ByteArray) (i : Nat)
    (h1 : data.size + 1 + zerosCount data ≤ i)
    (h2 : i < (implPaddedBytes data).size) :
    (implPaddedBytes data).get! i =
      (lengthBE64 (data.size.toUInt64 <<< 3)).get!
        (i - (data.size + 1 + zerosCount data)) := by
  have hsz := size_implPaddedBytes_eq data
  unfold implPaddedBytes
  have heq_size : (appendZeros (data.push 0x80) (zerosCount data)).size
        = data.size + 1 + zerosCount data := by
    rw [size_appendZeros, ByteArray.size_push]
  rw [get!_append_right]
  · congr 1
    rw [heq_size]
  · rw [heq_size]; exact h1
  · rw [heq_size, size_lengthBE64]
    rw [hsz] at h2
    omega

/-! ## Positional byte rule

A single closed-form per-byte rule for `(implPaddedBytes data).get! pos`,
covering all four cases (data / 0x80 / zero-pad / length-tag) in one
statement.  The `paddedBlock_*` formulas below specialise it to the
relevant block (the `_complete` case bypasses it and unfolds
`get!_implPaddedBytes_data` directly). -/

/-- The byte at position `pos` of the padded data follows one of four
rules: the original data byte (`pos < data.size`), the `0x80` separator
(`pos = data.size`), a zero in the pad region, or a length-tag byte. -/
theorem get!_implPaddedBytes_eq (data : ByteArray) (pos : Nat)
    (h : pos < (implPaddedBytes data).size) :
    (implPaddedBytes data).get! pos =
      (if pos < data.size then data.get! pos
       else if pos = data.size then 0x80
       else if pos < data.size + 1 + zerosCount data then 0
       else (lengthBE64 (data.size.toUInt64 <<< 3)).get!
              (pos - (data.size + 1 + zerosCount data))) := by
  by_cases h1 : pos < data.size
  · simp only [h1, if_true, get!_implPaddedBytes_data _ _ h1]
  · simp only [h1, if_false]
    by_cases h2 : pos = data.size
    · simp only [h2, if_true, get!_implPaddedBytes_sep]
    · simp only [h2, if_false]
      by_cases h3 : pos < data.size + 1 + zerosCount data
      · simp only [h3, if_true, get!_implPaddedBytes_zero _ _ (by omega) h3]
      · simp only [h3, if_false, get!_implPaddedBytes_length _ _ (by omega) h]

/-! ## `lengthBE64` byte access -/

theorem lengthBE64_get!_eq (bits : UInt64) (i : Nat) (h : i < 8) :
    (lengthBE64 bits).get! i =
      ((bits >>> (((7 - i) * 8 : Nat).toUInt64)) &&& 0xff).toUInt8 := by
  unfold lengthBE64
  simp [Id.run]
  rcases i with _|_|_|_|_|_|_|_|_
  all_goals (first | rfl | omega)

/-! ## `implPaddedBlocks` block view -/

/-- The `i`-th block of `implPaddedBlocks data` written directly via
`padded.get!`. -/
def paddedBlock (data : ByteArray) (i : Nat) : Vector UInt8 64 :=
  Vector.ofFn fun (j : Fin 64) => (implPaddedBytes data).get! (i * 64 + j.val)

theorem implPaddedBlocks_foldl {β : Type*} (data : ByteArray)
    (f : β → Vector UInt8 64 → β) (init : β) :
    (implPaddedBlocks data).foldl f init =
      Fin.foldl ((implPaddedBytes data).size / 64)
        (fun b i => f b (paddedBlock data i.val)) init := by
  unfold implPaddedBlocks
  rw [array_foldl_ofFn_eq_fin_foldl]
  rfl

/-- Complete-block formula: for `k < data.size / 64`, the `k`-th padded block
equals the impl's `Vector.ofFn fun j => data.get! (k*64+j)`. -/
theorem paddedBlock_complete (data : ByteArray) (k : Nat) (h : k < data.size / 64) :
    paddedBlock data k = Vector.ofFn (fun j : Fin 64 => data.get! (k * 64 + j.val)) := by
  unfold paddedBlock
  congr 1
  funext j
  apply get!_implPaddedBytes_data
  have : k * 64 + 64 ≤ data.size := by
    have hd := Nat.div_add_mod data.size 64
    have : (k + 1) * 64 ≤ data.size / 64 * 64 := Nat.mul_le_mul_right 64 h
    omega
  omega

/-- Final block (case `remaining < 56`): one extra block holding data,
`0x80`, zeros, and the bit-length tag.  Specialisation of
`get!_implPaddedBytes_eq` at block index `data.size / 64` and `remaining
< 56` (so the data, separator, zeros, and length tag all fit). -/
theorem paddedBlock_final_lt56 (data : ByteArray) (h : data.size % 64 < 56) :
    paddedBlock data (data.size / 64) =
      Vector.ofFn (fun i : Fin 64 =>
        if i.val < 56 then
          (if i.val < data.size % 64 then data.get! (data.size / 64 * 64 + i.val)
           else if i.val = data.size % 64 then 0x80
           else 0)
        else
          ((data.size.toUInt64 <<< 3 >>> (((63 - i.val) * 8).toUInt64)) &&& 0xff).toUInt8) := by
  unfold paddedBlock; congr 1; funext j
  have hd : data.size = 64 * (data.size / 64) + data.size % 64 :=
    (Nat.div_add_mod data.size 64).symm
  have hjvalid : data.size / 64 * 64 + j.val < (implPaddedBytes data).size := by
    rw [size_implPaddedBytes_eq, zerosCount_lt56 _ h]; have := j.isLt; omega
  rw [get!_implPaddedBytes_eq _ _ hjvalid, zerosCount_lt56 _ h]
  by_cases hj56 : j.val < 56
  · have heq_data : (data.size / 64 * 64 + j.val < data.size)
        = (j.val < data.size % 64) :=
      propext ⟨fun _ => by omega, fun _ => by omega⟩
    have heq_sep : (data.size / 64 * 64 + j.val = data.size)
        = (j.val = data.size % 64) :=
      propext ⟨fun _ => by omega, fun _ => by omega⟩
    have hzero : data.size / 64 * 64 + j.val < data.size + 1 + (55 - data.size % 64) := by
      omega
    simp [hj56, heq_data, heq_sep, hzero]
  · have hge_data : ¬ data.size / 64 * 64 + j.val < data.size := by omega
    have hne_sep : ¬ data.size / 64 * 64 + j.val = data.size := by omega
    have hge_zero : ¬ data.size / 64 * 64 + j.val < data.size + 1 + (55 - data.size % 64) := by
      omega
    have hidx : data.size / 64 * 64 + j.val - (data.size + 1 + (55 - data.size % 64))
        = j.val - 56 := by omega
    have hk : j.val - 56 < 8 := by have := j.isLt; omega
    have h63 : 7 - (j.val - 56) = 63 - j.val := by omega
    simp [hj56, hge_data, hne_sep, hge_zero, hidx, lengthBE64_get!_eq _ _ hk, h63]

/-- Final block A (case `remaining ≥ 56`): data bytes, then `0x80`, then
zeros (no length tag — that's in block B).  Specialisation of
`get!_implPaddedBytes_eq` at block index `data.size / 64` when there's
no room for the length suffix. -/
theorem paddedBlock_finalA_ge56 (data : ByteArray) (h : ¬ data.size % 64 < 56) :
    paddedBlock data (data.size / 64) =
      Vector.ofFn (fun i : Fin 64 =>
        if i.val < data.size % 64 then data.get! (data.size / 64 * 64 + i.val)
        else if i.val = data.size % 64 then 0x80
        else 0) := by
  unfold paddedBlock; congr 1; funext j
  have hd : data.size = 64 * (data.size / 64) + data.size % 64 :=
    (Nat.div_add_mod data.size 64).symm
  have hr_lt : data.size % 64 < 64 := Nat.mod_lt _ (by decide)
  have hjvalid : data.size / 64 * 64 + j.val < (implPaddedBytes data).size := by
    rw [size_implPaddedBytes_eq, zerosCount_ge56 _ h]; have := j.isLt; omega
  rw [get!_implPaddedBytes_eq _ _ hjvalid, zerosCount_ge56 _ h]
  have heq_data : (data.size / 64 * 64 + j.val < data.size)
      = (j.val < data.size % 64) :=
    propext ⟨fun _ => by omega, fun _ => by omega⟩
  have heq_sep : (data.size / 64 * 64 + j.val = data.size)
      = (j.val = data.size % 64) :=
    propext ⟨fun _ => by omega, fun _ => by omega⟩
  have hzero : data.size / 64 * 64 + j.val < data.size + 1 + (64 + 55 - data.size % 64) := by
    have := j.isLt; omega
  simp [heq_data, heq_sep, hzero]

/-- Final block B (case `remaining ≥ 56`): all zeros except the length
tag in the last 8 bytes.  Specialisation of `get!_implPaddedBytes_eq`
at block index `data.size / 64 + 1`, which lies entirely past the
zero-pad cutoff. -/
theorem paddedBlock_finalB_ge56 (data : ByteArray) (h : ¬ data.size % 64 < 56) :
    paddedBlock data (data.size / 64 + 1) =
      Vector.ofFn (fun i : Fin 64 =>
        if i.val < 56 then (0 : UInt8)
        else ((data.size.toUInt64 <<< 3 >>> (((63 - i.val) * 8).toUInt64)) &&& 0xff).toUInt8) := by
  unfold paddedBlock; congr 1; funext j
  have hd : data.size = 64 * (data.size / 64) + data.size % 64 :=
    (Nat.div_add_mod data.size 64).symm
  have hr_lt : data.size % 64 < 64 := Nat.mod_lt _ (by decide)
  have hjlt : j.val < 64 := j.isLt
  have hpsize : (implPaddedBytes data).size = (data.size / 64 + 2) * 64 := by
    rw [size_implPaddedBytes_eq, zerosCount_ge56 _ h]; omega
  have hjvalid : (data.size / 64 + 1) * 64 + j.val < (implPaddedBytes data).size := by
    rw [hpsize]; omega
  rw [get!_implPaddedBytes_eq _ _ hjvalid, zerosCount_ge56 _ h]
  have hge_data : ¬ (data.size / 64 + 1) * 64 + j.val < data.size := by omega
  have hne_sep : ¬ (data.size / 64 + 1) * 64 + j.val = data.size := by omega
  by_cases hj56 : j.val < 56
  · have hzero : (data.size / 64 + 1) * 64 + j.val
        < data.size + 1 + (64 + 55 - data.size % 64) := by
      omega
    simp [hj56, hge_data, hne_sep, hzero]
  · have hge_zero : ¬ (data.size / 64 + 1) * 64 + j.val
        < data.size + 1 + (64 + 55 - data.size % 64) := by
      omega
    have hidx : (data.size / 64 + 1) * 64 + j.val
          - (data.size + 1 + (64 + 55 - data.size % 64))
        = j.val - 56 := by omega
    have hk : j.val - 56 < 8 := by omega
    have h63 : 7 - (j.val - 56) = 63 - j.val := by omega
    simp [hj56, hge_data, hne_sep, hge_zero, hidx, lengthBE64_get!_eq _ _ hk, h63]

/-! ## Total padded block count -/

theorem totalBlocks_lt56 (data : ByteArray) (h : data.size % 64 < 56) :
    (implPaddedBytes data).size / 64 = data.size / 64 + 1 := by
  rw [size_implPaddedBytes_eq, zerosCount_lt56 _ h]
  have hd : data.size = 64 * (data.size / 64) + data.size % 64 :=
    (Nat.div_add_mod data.size 64).symm
  omega

theorem totalBlocks_ge56 (data : ByteArray) (h : ¬ data.size % 64 < 56) :
    (implPaddedBytes data).size / 64 = data.size / 64 + 2 := by
  rw [size_implPaddedBytes_eq, zerosCount_ge56 _ h]
  have hd : data.size = 64 * (data.size / 64) + data.size % 64 :=
    (Nat.div_add_mod data.size 64).symm
  have hr_lt : data.size % 64 < 64 := Nat.mod_lt _ (by decide)
  omega

end SHS.Equiv.SHA256.Padding.Layout
