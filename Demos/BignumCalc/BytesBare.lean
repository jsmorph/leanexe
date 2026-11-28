module

public import Demos.BignumCalc.Bare
public import LeanExe.A64.Proof.BytesRuns
public import Verified.ChargeFacts

@[expose] public section

/-!
# The calculator's AArch64 Image

The Image's entry reads a message from the UART and runs `calcBytes` on it, function 45 of
`messageCompiled.module`.  `output msg` is what the program writes before its status for the
message `msg`, and `output_eq` states that it is `calcSpec msg`, the message's line, for every
message of at most `imageMax`, 65,536 bytes.  `calc_runs` is the program's theorem in the form
`BytesRuns`, for the program that `genBytesProgram` generates at any base: it reads a length of
eight bytes and a message of that many bytes, at most `imageMax`, writes `output` of the message,
and returns with the exit status 0 in X0, and for a longer length or a byte with an error flag it
reaches the exit word with the exit status 64 or 65 in X0, after writing nothing.  Its trap
predicate is `False`: no trap and no overflow of the stack occurs, since the message's block and
the calculator's blocks, at most 27,000,000 bytes, fit the cap of 512 pages above the heap's `top`,
and the stack fits the room of 512 KiB.  The Image's startup and exit, which write the status as the
last byte, join it in `Image.lean`.
-/

namespace Demos.BignumCalc

open Library.Numerics.Bignum

open LeanExe LeanExe.A64 LeanExe.Dialect LeanExe.Pipeline
open Library.Numerics.Decimal.Shared.StrconvGrammar (ascii words)

/-! ## The Image's parameters -/

/-- The index of `calcBytes` among the functions of `messageCompiled.module`. -/
def imageEntry : Nat := 45

/-- The largest length of a message: 65,536 bytes, the calculator's limit. -/
def imageMax : UInt64 := 65536

/-- The stack's room in bytes. -/
def imageRoom : UInt64 := 0x80000

/-- The memory's cap in pages: 512 pages, 32 MiB. -/
def imageCap : Nat := 512

/-- The base in RAM at which QEMU places the Image. -/
def imageBase : UInt64 := 0x40200000

/-- The Image of `calcBytes`'s program at `imageBase`. -/
def image : Except String (List UInt8 × Layout) :=
  genBytesImage messageCompiled.module imageEntry imageMax imageRoom imageCap imageBase

/-- The bytes that the program writes for the message `msg`, before the status. -/
def output (msg : List UInt8) : List UInt8 := (calcBytes ⟨⟨msg.toArray⟩⟩).data.data.toList

/-! ## The entry on a message -/

theorem get_msg (msg : List UInt8) {i : Nat} (hi : i < msg.length) (h64 : i < 2 ^ 64) :
    Bytes.get ⟨⟨msg.toArray⟩⟩ (UInt64.ofNat i) = (msg[i]'hi).toUInt64 := by
  have hidx : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' h64
  unfold Bytes.get
  split
  · simp [hidx, ByteArray.getElem_eq_getElem_data]
  · rename_i h
    exact absurd (by rw [hidx]; simpa [ByteArray.size] using hi) h

theorem msg_size (msg : List UInt8) : Bytes.size ⟨⟨msg.toArray⟩⟩ = UInt64.ofNat msg.length := by
  show UInt64.ofNat msg.toArray.size = _
  rw [List.size_toArray]

/-- The entry's copy of a message's bytes, one to a word. -/
theorem build_msg (msg : List UInt8) (h : msg.length < 2 ^ 64) :
    LeanExe.build (Bytes.size ⟨⟨msg.toArray⟩⟩) (fun i => Bytes.get ⟨⟨msg.toArray⟩⟩ i) = words msg := by
  have hn : (UInt64.ofNat msg.length).toNat = msg.length := toNat64_of_lt h
  apply Array.ext
  · rw [build_size, msg_size, hn, words_size]
  · intro i h1 h2
    rw [build_size, msg_size, hn] at h1
    rw [← getElem!_pos _ i (by rw [build_size, msg_size, hn]; exact h1),
      build_get (by rw [msg_size, hn]; exact h1), get_msg msg h1 (by omega),
      ← getElem!_pos (words msg) i h2, words_get msg h1]

/-- The bytes that `Bytes.build` writes from words that hold one byte each. -/
theorem bytes_build_words (L : List UInt8) (h : L.length < 2 ^ 64) :
    (Bytes.build (words L).size.toUInt64 fun j => (words L)[j.toNat]!).data.data.toList = L := by
  have hn : (words L).size.toUInt64.toNat = L.length := by
    rw [size_toNat64 (by rw [words_size]; exact h), words_size]
  apply List.ext_getElem
  · simp [Bytes.build, hn]
  · intro i h1 h2
    simp only [Bytes.build, Array.toList_ofFn, List.getElem_ofFn]
    have hi : (UInt64.ofNat i).toNat = i := toNat64_of_lt (by omega)
    rw [hi, words_get L h2]
    simp

/-- For every message of at most `imageMax` bytes, `output` gives the message's line. -/
theorem output_eq (msg : List UInt8) (hlen : msg.length ≤ 65536) : output msg = calcSpec msg := by
  unfold output calcBytes
  dsimp only
  rw [build_msg msg (by omega), calcLine_eq msg (by omega),
    bytes_build_words _ (by have := calcSpec_length_le msg; omega)]

/-! ## The bound and the program's theorem -/

/-- The entry allocates at most 27,000,000 bytes on a message of at most 65,536 bytes: the words
of the message, the calculator's blocks, and the line's bytes. -/
theorem calcBytes_bound (b : Bytes) (hb : b.data.size ≤ 65536) :
    messageCompiled.calcBytes.bound b ≤ 27000000 := by
  obtain ⟨⟨arr⟩⟩ := b
  have hb' : arr.toList.length ≤ 65536 := by simpa [ByteArray.size] using hb
  have harr : (⟨⟨arr⟩⟩ : Bytes) = ⟨⟨arr.toList.toArray⟩⟩ := by simp
  rw [harr, messageCompiled.calcBytes.bound_eq, build_msg _ (by omega)]
  have hs : (Bytes.size ⟨⟨arr.toList.toArray⟩⟩).toNat = arr.toList.length := by
    rw [msg_size, toNat64_of_lt (by omega)]
  have hc := calcLine_bound_le (words arr.toList) (by rw [words_size]; omega)
  rw [words_size] at hc
  have hl : (calcLine (words arr.toList)).size ≤ arr.toList.length + 4 := by
    rw [calcLine_eq _ (by omega), words_size]
    exact calcSpec_length_le _
  have ha := Verified.allocationCost_le (calcLine (words arr.toList)).size.toUInt64.toNat
  have hz : (calcLine (words arr.toList)).size.toUInt64.toNat = (calcLine (words arr.toList)).size :=
    size_toNat64 (by omega)
  rw [hs, Verified.blockCost_eq]
  omega

/-- The payload of an allocation of `L` bytes exceeds `L` by at most 8 bytes. -/
theorem allocSize_le_add {L : Nat} (h : L ≤ 4294967296) :
    (allocSize (UInt64.ofNat L)).toNat ≤ L + 8 := by
  have hL : (UInt64.ofNat L).toNat = L := by
    rw [UInt64.toNat_ofNat']
    simp only [Nat.reducePow]
    omega
  have hRound : ((UInt64.ofNat L + 7) / 8 * 8).toNat = (L + 7) / 8 * 8 := by
    simp only [UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_add, UInt64.reduceToNat, hL]
    omega
  unfold allocSize
  split
  · simp only [UInt64.reduceToNat]
    omega
  · rw [hRound]
    omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The theorem of `calcBytes`'s program, at every base: for a message `msg` of at most `imageMax`
bytes that the receiver delivers, the program writes `output msg` and returns with the status 0,
and for a longer length or a byte with an error flag it reaches the exit word with the status 64
or 65 after writing nothing.  No trap and no overflow of the stack occurs. -/
theorem calc_runs :
    BytesRuns messageCompiled.module imageEntry imageMax imageRoom imageCap output
      fun _ _ => False := by
  have hAt := messageCompiled.initial.1
  refine bytes_runs_bounded messageCompiled.calcBytes.trapFree (typeIdx := 0) rfl hAt (by decide)
    (fun L hL => Heap.Within.room ?_ (by decide)) (fun b st hb hcap => ?_)
    (by decide +kernel) (by decide +kernel)
  · show _ + _ ≤ 65536 * imageCap
    have := allocSize_le_add (L := L) (by simp only [imageMax, UInt64.reduceToNat] at hL; omega)
    simp only [imageMax, UInt64.reduceToNat, imageCap] at hL ⊢
    rw [calc_initialHeap_top]
    omega
  · show _ + _ ≤ 65536 * st.memoryCap messageCompiled.module 0
    rw [hcap]
    simp only [imageMax, UInt64.reduceToNat] at hb
    have hfit : (Verified.initialHeap messageCompiled.tables).Fits
        (allocSize (UInt64.ofNat b.data.size)) := by
      intro _
      have := allocSize_le_add (L := b.data.size) (by omega)
      rw [calc_initialHeap_top]
      omega
    have htop := Heap.allocate_top hfit
    have := allocSize_le_add (L := b.data.size) (by omega)
    have := calcBytes_bound b hb
    simp only [Verified.allocCost, imageCap] at htop ⊢
    rw [calc_initialHeap_top] at htop
    omega

#print axioms output_eq
#print axioms calc_runs

end Demos.BignumCalc
