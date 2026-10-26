import Library.Hashing.Sha2.Impl.SHA512
import Library.Hashing.Sha2.Equiv.SHA512.Lift
import Library.Hashing.Sha2.Equiv.SHA512.ToU64s
import Library.Hashing.Sha2.Equiv.Common.ByteArray
import Library.Hashing.Sha2.Equiv.Common.ArrayFold

/-! # SHA-512 padding: byte-level layout

Parallel to `equiv/SHA256/Padding/Layout.lean` with 128-byte blocks
and a 16-byte length tag (high 8 bytes literal zero, low 8 bytes
big-endian `UInt64` bit-count).  The cutoff is `% 128 < 112` (128
minus 1 separator minus 16 length suffix).

Reifies the streaming pad inside `Impl.sha512` as `implPaddedBytes`
and its 128-byte block view `implPaddedBlocks`, then proves the
byte-by-byte layout in three cases:
- `complete`: a fully-data block (`k < data.size / 128`)
- `final<112`: one extra block holding data, `0x80`, zeros, length tag
- `final≥112`: two tail blocks — A holds data + `0x80` + zeros, B
  holds zeros + length tag. -/

open SHS.Equiv.ByteArray
open SHS.Equiv.ArrayFold
open SHS.Equiv.SHA512.Lift
open SHS.Equiv.SHA512.ToU64s

open SHS.SHA512

namespace SHS.Equiv.SHA512.Padding.Layout

open scoped SHS.SHA512

/-! ## Byte-level definitions -/

/-- Number of zero bytes between the `0x80` separator and the 16-byte
length tag.  Mirrors the SHA-256 definition at block size 128 and length
size 16. -/
def zerosCount (data : ByteArray) : Nat :=
  if data.size % 128 < 112 then 111 - data.size % 128
  else 128 + 111 - data.size % 128

theorem zerosCount_lt112 (data : ByteArray) (h : data.size % 128 < 112) :
    zerosCount data = 111 - data.size % 128 := by
  unfold zerosCount; rw [if_pos h]

theorem zerosCount_ge112 (data : ByteArray) (h : ¬ data.size % 128 < 112) :
    zerosCount data = 128 + 111 - data.size % 128 := by
  unfold zerosCount; rw [if_neg h]

/-- The 128-bit big-endian length encoding (sixteen bytes): high 8 bytes
literal zero, low 8 bytes big-endian `UInt64` of `bits`.  Matches the
inline expansion in `Impl.sha512`'s final block. -/
def lengthBE128 (bits : UInt64) : ByteArray := Id.run do
  let mut bs : ByteArray := ByteArray.empty
  for _ in [0:8] do
    bs := bs.push 0
  for i in [0:8] do
    bs := bs.push ((bits >>> ((7 - i) * 8).toUInt64) &&& 0xff).toUInt8
  return bs

/-- Reified streaming pad of `Impl.sha512`.  Mirrors the impl's logic
without unfolding `sha512`: append `data`, then `0x80`, then enough zeros
to land at 112 mod 128, then the 16-byte big-endian bit-length tag. -/
def implPaddedBytes (data : ByteArray) : ByteArray :=
  let totalBits : UInt64 := data.size.toUInt64 <<< 3
  appendZeros (data.push 0x80) (zerosCount data) ++ lengthBE128 totalBits

/-- Slice the padded byte sequence into 128-byte blocks. -/
def implPaddedBlocks (data : ByteArray) : Array (Vector UInt8 128) :=
  let padded := implPaddedBytes data
  let n := padded.size / 128
  Array.ofFn (n := n) fun i =>
    Vector.ofFn fun (j : Fin 128) =>
      padded.get! (i.val * 128 + j.val)

/-! ## Easy invariants -/

@[simp] theorem size_lengthBE128 (bits : UInt64) : (lengthBE128 bits).size = 16 := by
  unfold lengthBE128
  simp [Id.run]
  rfl

theorem size_implPaddedBytes_mod (data : ByteArray) :
    (implPaddedBytes data).size % 128 = 0 := by
  unfold implPaddedBytes zerosCount
  simp [ByteArray.size_append]
  split <;> omega

theorem size_implPaddedBytes_eq (data : ByteArray) :
    (implPaddedBytes data).size = data.size + 1 + zerosCount data + 16 := by
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
      (lengthBE128 (data.size.toUInt64 <<< 3)).get!
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
  · rw [heq_size, size_lengthBE128]
    rw [hsz] at h2
    omega

theorem get!_implPaddedBytes_eq (data : ByteArray) (pos : Nat)
    (h : pos < (implPaddedBytes data).size) :
    (implPaddedBytes data).get! pos =
      (if pos < data.size then data.get! pos
       else if pos = data.size then 0x80
       else if pos < data.size + 1 + zerosCount data then 0
       else (lengthBE128 (data.size.toUInt64 <<< 3)).get!
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

/-! ## `lengthBE128` byte access -/

/-- The first 8 bytes are literal zeros. -/
theorem lengthBE128_get!_zero (bits : UInt64) (i : Nat) (h : i < 8) :
    (lengthBE128 bits).get! i = 0 := by
  unfold lengthBE128
  simp [Id.run]
  rcases i with _|_|_|_|_|_|_|_|_
  all_goals (first | rfl | omega)

/-- The last 8 bytes are the BE encoding of `bits`. -/
theorem lengthBE128_get!_eq (bits : UInt64) (i : Nat) (h1 : 8 ≤ i) (h2 : i < 16) :
    (lengthBE128 bits).get! i =
      ((bits >>> (((15 - i) * 8 : Nat).toUInt64)) &&& 0xff).toUInt8 := by
  unfold lengthBE128
  simp [Id.run]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_
  all_goals (first | rfl | omega)

/-! ## `implPaddedBlocks` block view -/

/-- The `i`-th block of `implPaddedBlocks data` written directly via
`padded.get!`. -/
def paddedBlock (data : ByteArray) (i : Nat) : Vector UInt8 128 :=
  Vector.ofFn fun (j : Fin 128) => (implPaddedBytes data).get! (i * 128 + j.val)

theorem implPaddedBlocks_foldl {β : Type*} (data : ByteArray)
    (f : β → Vector UInt8 128 → β) (init : β) :
    (implPaddedBlocks data).foldl f init =
      Fin.foldl ((implPaddedBytes data).size / 128)
        (fun b i => f b (paddedBlock data i.val)) init := by
  unfold implPaddedBlocks
  rw [array_foldl_ofFn_eq_fin_foldl]
  rfl

/-- Complete-block formula: for `k < data.size / 128`, the `k`-th
padded block equals the impl's `Vector.ofFn fun j => data.get! (k*128+j)`. -/
theorem paddedBlock_complete (data : ByteArray) (k : Nat) (h : k < data.size / 128) :
    paddedBlock data k =
      Vector.ofFn (fun j : Fin 128 => data.get! (k * 128 + j.val)) := by
  unfold paddedBlock
  congr 1
  funext j
  apply get!_implPaddedBytes_data
  have : k * 128 + 128 ≤ data.size := by
    have hd := Nat.div_add_mod data.size 128
    have : (k + 1) * 128 ≤ data.size / 128 * 128 := Nat.mul_le_mul_right 128 h
    omega
  omega

/-- Final block (case `remaining < 112`): one extra block holding data,
`0x80`, zeros, and the 16-byte length tag (8 zero bytes + 8-byte BE
length).  Specialisation of `get!_implPaddedBytes_eq` at block index
`data.size / 128` and `remaining < 112` (so data, separator, zeros,
and length tag all fit in one block). -/
theorem paddedBlock_final_lt112 (data : ByteArray) (h : data.size % 128 < 112) :
    paddedBlock data (data.size / 128) =
      Vector.ofFn (fun i : Fin 128 =>
        if i.val < 112 then
          (if i.val < data.size % 128 then data.get! (data.size / 128 * 128 + i.val)
           else if i.val = data.size % 128 then 0x80
           else 0)
        else if i.val < 120 then (0 : UInt8)
        else ((data.size.toUInt64 <<< 3 >>> (((127 - i.val) * 8).toUInt64)) &&& 0xff).toUInt8) := by
  unfold paddedBlock; congr 1; funext j
  have hd : data.size = 128 * (data.size / 128) + data.size % 128 :=
    (Nat.div_add_mod data.size 128).symm
  have hjvalid : data.size / 128 * 128 + j.val < (implPaddedBytes data).size := by
    rw [size_implPaddedBytes_eq, zerosCount_lt112 _ h]; have := j.isLt; omega
  rw [get!_implPaddedBytes_eq _ _ hjvalid, zerosCount_lt112 _ h]
  by_cases hj112 : j.val < 112
  · have heq_data : (data.size / 128 * 128 + j.val < data.size)
        = (j.val < data.size % 128) :=
      propext ⟨fun _ => by omega, fun _ => by omega⟩
    have heq_sep : (data.size / 128 * 128 + j.val = data.size)
        = (j.val = data.size % 128) :=
      propext ⟨fun _ => by omega, fun _ => by omega⟩
    have hzero : data.size / 128 * 128 + j.val < data.size + 1 + (111 - data.size % 128) := by
      omega
    simp [hj112, heq_data, heq_sep, hzero]
  · have hge_data : ¬ data.size / 128 * 128 + j.val < data.size := by omega
    have hne_sep : ¬ data.size / 128 * 128 + j.val = data.size := by omega
    have hge_zero : ¬ data.size / 128 * 128 + j.val < data.size + 1 + (111 - data.size % 128) := by
      omega
    have hidx : data.size / 128 * 128 + j.val - (data.size + 1 + (111 - data.size % 128))
        = j.val - 112 := by omega
    have hk : j.val - 112 < 16 := by have := j.isLt; omega
    by_cases hj120 : j.val < 120
    · have hk8 : j.val - 112 < 8 := by omega
      simp [hj112, hge_data, hne_sep, hge_zero, hidx, lengthBE128_get!_zero _ _ hk8, hj120]
    · have hk_ge8 : 8 ≤ j.val - 112 := by omega
      have h127 : 15 - (j.val - 112) = 127 - j.val := by omega
      simp [hj112, hge_data, hne_sep, hge_zero, hidx,
        lengthBE128_get!_eq _ _ hk_ge8 hk, h127, hj120]

/-- Final block A (case `remaining ≥ 112`): data bytes, then `0x80`,
then zeros (no length tag — that's in block B).  Specialisation of
`get!_implPaddedBytes_eq` at block index `data.size / 128` when there's
no room for the 16-byte length suffix. -/
theorem paddedBlock_finalA_ge112 (data : ByteArray) (h : ¬ data.size % 128 < 112) :
    paddedBlock data (data.size / 128) =
      Vector.ofFn (fun i : Fin 128 =>
        if i.val < data.size % 128 then data.get! (data.size / 128 * 128 + i.val)
        else if i.val = data.size % 128 then 0x80
        else 0) := by
  unfold paddedBlock; congr 1; funext j
  have hd : data.size = 128 * (data.size / 128) + data.size % 128 :=
    (Nat.div_add_mod data.size 128).symm
  have hr_lt : data.size % 128 < 128 := Nat.mod_lt _ (by decide)
  have hjvalid : data.size / 128 * 128 + j.val < (implPaddedBytes data).size := by
    rw [size_implPaddedBytes_eq, zerosCount_ge112 _ h]; have := j.isLt; omega
  rw [get!_implPaddedBytes_eq _ _ hjvalid, zerosCount_ge112 _ h]
  have heq_data : (data.size / 128 * 128 + j.val < data.size)
      = (j.val < data.size % 128) :=
    propext ⟨fun _ => by omega, fun _ => by omega⟩
  have heq_sep : (data.size / 128 * 128 + j.val = data.size)
      = (j.val = data.size % 128) :=
    propext ⟨fun _ => by omega, fun _ => by omega⟩
  have hzero : data.size / 128 * 128 + j.val < data.size + 1 + (128 + 111 - data.size % 128) := by
    have := j.isLt; omega
  simp [heq_data, heq_sep, hzero]

/-- Final block B (case `remaining ≥ 112`): all zeros except the 16-byte
length tag in bytes 112..127.  Specialisation of `get!_implPaddedBytes_eq`
at block index `data.size / 128 + 1`, which lies entirely past the
zero-pad cutoff. -/
theorem paddedBlock_finalB_ge112 (data : ByteArray) (h : ¬ data.size % 128 < 112) :
    paddedBlock data (data.size / 128 + 1) =
      Vector.ofFn (fun i : Fin 128 =>
        if i.val < 120 then (0 : UInt8)
        else ((data.size.toUInt64 <<< 3 >>> (((127 - i.val) * 8).toUInt64)) &&& 0xff).toUInt8) := by
  unfold paddedBlock; congr 1; funext j
  have hd : data.size = 128 * (data.size / 128) + data.size % 128 :=
    (Nat.div_add_mod data.size 128).symm
  have hr_lt : data.size % 128 < 128 := Nat.mod_lt _ (by decide)
  have hjlt : j.val < 128 := j.isLt
  have hpsize : (implPaddedBytes data).size = (data.size / 128 + 2) * 128 := by
    rw [size_implPaddedBytes_eq, zerosCount_ge112 _ h]; omega
  have hjvalid : (data.size / 128 + 1) * 128 + j.val < (implPaddedBytes data).size := by
    rw [hpsize]; omega
  rw [get!_implPaddedBytes_eq _ _ hjvalid, zerosCount_ge112 _ h]
  have hge_data : ¬ (data.size / 128 + 1) * 128 + j.val < data.size := by omega
  have hne_sep : ¬ (data.size / 128 + 1) * 128 + j.val = data.size := by omega
  -- `paddedBlock` index `i = data.size / 128 + 1` is the freshly-allocated
  -- zero block carrying the 16-byte length tag.  `hj112` (whether `j` lies
  -- in the zero region or the length region) splits the cases but isn't
  -- needed as a `simp` arg because `hzero` / `hge_zero` already discharge
  -- the relevant branch in `get!_implPaddedBytes_eq`.
  by_cases hj112 : j.val < 112
  · have hzero : (data.size / 128 + 1) * 128 + j.val
        < data.size + 1 + (128 + 111 - data.size % 128) := by
      omega
    have hj120 : j.val < 120 := by omega
    simp [hge_data, hne_sep, hzero, hj120]
  · have hge_zero : ¬ (data.size / 128 + 1) * 128 + j.val
        < data.size + 1 + (128 + 111 - data.size % 128) := by
      omega
    have hidx : (data.size / 128 + 1) * 128 + j.val
          - (data.size + 1 + (128 + 111 - data.size % 128))
        = j.val - 112 := by omega
    have hk : j.val - 112 < 16 := by omega
    by_cases hj120 : j.val < 120
    · have hk8 : j.val - 112 < 8 := by omega
      simp [hge_data, hne_sep, hge_zero, hidx, lengthBE128_get!_zero _ _ hk8, hj120]
    · have hk_ge8 : 8 ≤ j.val - 112 := by omega
      have h127 : 15 - (j.val - 112) = 127 - j.val := by omega
      simp [hge_data, hne_sep, hge_zero, hidx,
        lengthBE128_get!_eq _ _ hk_ge8 hk, h127, hj120]

/-! ## Total padded block count -/

theorem totalBlocks_lt112 (data : ByteArray) (h : data.size % 128 < 112) :
    (implPaddedBytes data).size / 128 = data.size / 128 + 1 := by
  rw [size_implPaddedBytes_eq, zerosCount_lt112 _ h]
  have hd : data.size = 128 * (data.size / 128) + data.size % 128 :=
    (Nat.div_add_mod data.size 128).symm
  omega

theorem totalBlocks_ge112 (data : ByteArray) (h : ¬ data.size % 128 < 112) :
    (implPaddedBytes data).size / 128 = data.size / 128 + 2 := by
  rw [size_implPaddedBytes_eq, zerosCount_ge112 _ h]
  have hd : data.size = 128 * (data.size / 128) + data.size % 128 :=
    (Nat.div_add_mod data.size 128).symm
  have hr_lt : data.size % 128 < 128 := Nat.mod_lt _ (by decide)
  omega

end SHS.Equiv.SHA512.Padding.Layout
