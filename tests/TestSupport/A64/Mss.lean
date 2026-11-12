import Library.Arrays.MaxSegmentSum.Proof
import Verified.Reflect.Command
import LeanExe.A64.Proof.BytesRuns
import LeanExe.Dialect.Lemmas
import TestSupport.A64.Programs
import TestSupport.A64.Flip

/-!
Kadane's maximum segment sum as a bare-metal program that reads its input from the UART.
`mssBytes` reads a message of `8 n` bytes as `n` words, each from its eight bytes with the lowest
first, takes the words as `Int64` values, and returns the eight bytes of the word of `mss` of
those values, the lowest first.  A message whose length is not a multiple of 8 gives no bytes.
`verified_compile` compiles `mss` of `Library.Arrays.MaxSegmentSum`, `wordAt`, and `mssBytes`.
The image of `genBytesImage` at `imageBase` reads a length of eight bytes and a message of that
many bytes, at most `inMax`, and writes `output` of the message and the status 0, the status 64
for a length above `inMax`, or the status 65 for a byte with an error flag.  `mss_runs` is its
theorem in the form `BytesRuns`: `compiled.mssBytes.trapFree` excludes every trap, since the
message's block, the array of its words, and the result's block, `mssBytes_bound`, fit the cap
`mssCap` above the heap's `top`, and the stack that the program uses is at most the room of
`TestSupport.A64.Programs`.  `output_spec` states that for the bytes of `Int64` words whose
absolute values sum to less than `2^63`, `output` gives the bytes of a word whose integer is the
maximum segment sum of the words.  `messages` lists the messages on which
`tests/baremetal/a64-uart.sh` runs the image under QEMU, and `overLengths` the lengths above `inMax`
on which it runs.
-/

namespace TestSupport.A64.Mss

open LeanExe LeanExe.A64 LeanExe.Dialect LeanExe.Pipeline Library.Arrays.MaxSegmentSum

/-- Word `i` of the buffer `b`: the sum over `j < 8` of byte `8 i + j` times `2^(8 j)`. -/
def wordAt (b : Bytes) (i : UInt64) : UInt64 :=
  LeanExe.loop 8 0 fun j w => w + (b.get (8 * i + j) <<< (8 * j))

/-- The eight bytes of the word of `mss` of the words of `b` read as `Int64` values, the lowest
first, when the length of `b` is a multiple of 8, and no bytes otherwise. -/
def mssBytes (b : Bytes) : Bytes :=
  if b.size % 8 = 0 then
    let r := (mss (LeanExe.build (b.size / 8) fun i => (wordAt b i).toInt64)).toUInt64
    Bytes.build 8 fun j => r >>> (8 * j)
  else Bytes.empty

verified_compile compiled := [mss, wordAt, mssBytes]

/-- The index of `mssBytes` among the functions of `compiled.module`, after the allocator, the
release, `mss`, and `wordAt`. -/
def entry : Nat := 4

/-- The largest length of a message: 8,800,000 bytes, 1,100,000 words. -/
def inMax : UInt64 := 8800000

/-- The memory's cap in pages: room above the heap's `top` for the blocks of a message of `inMax`
bytes, of the array of its words, and of the result. -/
def mssCap : Nat := 269

/-- The image of `mssBytes`'s program at `imageBase`. -/
def image : Except String (List UInt8 × Layout) :=
  genBytesImage compiled.module entry inMax room mssCap imageBase

/-- The bytes that the program writes for the message `msg`, before the status. -/
def output (msg : List UInt8) : List UInt8 := (mssBytes ⟨⟨msg.toArray⟩⟩).data.data.toList

/-- Byte `t` of word `i` of a buffer that holds the bytes of the words `ws` is the base-256 digit
`t` of `ws[i]`. -/
theorem get_words (ws : List UInt64) (hlen : 8 * ws.length < 2 ^ 64) {i t : Nat}
    (hi : i < ws.length) (ht : t < 8) :
    (Bytes.get ⟨⟨(ws.flatMap bytesOf).toArray⟩⟩ (8 * UInt64.ofNat i + UInt64.ofNat t)).toNat =
      ws[i].toNat / 2 ^ (8 * t) % 256 := by
  have hl := length_flatMap_bytesOf ws
  have hidx : (8 * UInt64.ofNat i + UInt64.ofNat t).toNat = 8 * i + t := by
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat', UInt64.reduceToNat]
    omega
  have hlt : 8 * i + t < (ws.flatMap bytesOf).length := by rw [hl]; omega
  have hget : Bytes.get ⟨⟨(ws.flatMap bytesOf).toArray⟩⟩ (8 * UInt64.ofNat i + UInt64.ofNat t) =
      ((ws.flatMap bytesOf)[8 * i + t]).toUInt64 := by
    unfold Bytes.get
    rw [dite_eq_left (by rw [hidx]; exact hlt)]
    simp [hidx, ByteArray.getElem_eq_getElem_data]
  rw [hget, UInt8.toNat_toUInt64, getElem_flatMap_bytesOf ws i t hi ht hlt, bytesOf_digit _ ht]

/-- `wordAt` reads word `i` of a buffer that holds the bytes of the words `ws`. -/
theorem wordAt_words (ws : List UInt64) (hlen : 8 * ws.length < 2 ^ 64) {i : Nat}
    (hi : i < ws.length) : wordAt ⟨⟨(ws.flatMap bytesOf).toArray⟩⟩ (UInt64.ofNat i) = ws[i] := by
  apply UInt64.toNat_inj.mp
  have h := loop_induction (n := 8) (init := (0 : UInt64))
    (f := fun j w =>
      w + (Bytes.get ⟨⟨(ws.flatMap bytesOf).toArray⟩⟩ (8 * UInt64.ofNat i + j) <<< (8 * j)))
    (P := fun k w => w.toNat = ws[i].toNat % 2 ^ (8 * k))
    (by simp only [UInt64.toNat_zero, Nat.mul_zero, Nat.pow_zero, Nat.mod_one])
    (fun k w hk ih => by
      have hk8 : k < 8 := hk
      have hd := get_words ws hlen hi hk8
      have hsh : (8 * UInt64.ofNat k).toNat = 8 * k := by
        simp only [UInt64.toNat_mul, UInt64.toNat_ofNat', UInt64.reduceToNat]
        omega
      rw [UInt64.toNat_add, UInt64.toNat_shiftLeft, hsh, hd, ih, Nat.shiftLeft_eq,
        Nat.mod_eq_of_lt (show 8 * k < 64 by omega)]
      have e1 := pow_8succ k
      have e2 : ws[i].toNat % 2 ^ (8 * (k + 1)) = ws[i].toNat % 2 ^ (8 * k) +
          2 ^ (8 * k) * (ws[i].toNat / 2 ^ (8 * k) % 256) := by
        rw [e1, Nat.mod_mul]
      have e3 : ws[i].toNat / 2 ^ (8 * k) % 256 * 2 ^ (8 * k) ≤ 255 * 2 ^ (8 * k) :=
        Nat.mul_le_mul_right _ (by omega)
      have e4 := Nat.mul_comm (2 ^ (8 * k)) (ws[i].toNat / 2 ^ (8 * k) % 256)
      have e5 : ws[i].toNat % 2 ^ (8 * k) < 2 ^ (8 * k) := Nat.mod_lt _ (Nat.two_pow_pos _)
      have e6 : 2 ^ (8 * (k + 1)) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
      omega)
  simp only [UInt64.reduceToNat] at h
  exact h.trans (Nat.mod_eq_of_lt (by have := ws[i].toNat_lt; omega))

/-- The eight bytes of `Bytes.build 8 fun j => r >>> (8 * j)` are `bytesOf r`. -/
theorem build_bytesOf (r : UInt64) :
    (Bytes.build 8 fun j => r >>> (8 * j)).data.data.toList = bytesOf r := by
  apply List.ext_getElem
  · simp [Bytes.build, bytesOf]
  · intro j h1 h2
    have hj : j < 8 := by simpa [bytesOf] using h2
    have e : (8 : UInt64) * UInt64.ofNat j = UInt64.ofNat (8 * j) := by
      apply UInt64.toNat_inj.mp
      simp only [UInt64.toNat_mul, UInt64.toNat_ofNat', UInt64.reduceToNat]
      omega
    simp only [Bytes.build, Array.toList_ofFn, List.getElem_ofFn, bytesOf, List.getElem_map,
      List.getElem_range, e]

/-- On the bytes of the words `ws`, `mssBytes` gives the bytes of the word of `mss` of the words
read as `Int64` values. -/
theorem mssBytes_words (ws : List UInt64) (hlen : 8 * ws.length < 2 ^ 64) :
    (mssBytes ⟨⟨(ws.flatMap bytesOf).toArray⟩⟩).data.data.toList =
      bytesOf (mss (ws.map UInt64.toInt64).toArray).toUInt64 := by
  have hl := length_flatMap_bytesOf ws
  have hsize : Bytes.size ⟨⟨(ws.flatMap bytesOf).toArray⟩⟩ = UInt64.ofNat (8 * ws.length) := by
    show UInt64.ofNat (ws.flatMap bytesOf).toArray.size = _
    rw [List.size_toArray, hl]
  have hmod : Bytes.size ⟨⟨(ws.flatMap bytesOf).toArray⟩⟩ % 8 = 0 := by
    rw [hsize]
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_mod, UInt64.toNat_ofNat', UInt64.reduceToNat]
    omega
  have hdiv : Bytes.size ⟨⟨(ws.flatMap bytesOf).toArray⟩⟩ / 8 = UInt64.ofNat ws.length := by
    rw [hsize]
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_div, UInt64.toNat_ofNat', UInt64.reduceToNat]
    omega
  have harr : LeanExe.build (UInt64.ofNat ws.length)
      (fun i => (wordAt ⟨⟨(ws.flatMap bytesOf).toArray⟩⟩ i).toInt64) =
        (ws.map UInt64.toInt64).toArray := by
    have hn : (UInt64.ofNat ws.length).toNat = ws.length :=
      UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
    apply Array.ext
    · simp [LeanExe.build, hn]
    · intro j h1 h2
      have hj : j < ws.length := by simpa using h2
      simp only [LeanExe.build, Array.getElem_ofFn, List.getElem_toArray, List.getElem_map]
      rw [wordAt_words ws hlen hj]
  unfold mssBytes
  rw [ite_eq_left hmod, hdiv, harr]
  exact build_bytesOf _

/-- For the bytes of `Int64` words `ws` whose absolute values sum to less than `2^63`, `output`
gives the bytes of a word whose integer is the maximum segment sum of `ws` read as integers. -/
theorem output_spec (ws : List Int64) (hlen : 8 * ws.length < 2 ^ 64)
    (hb : (ws.map fun w => w.toInt.natAbs).sum < 2 ^ 63) :
    ∃ y : Int64, output ((ws.map Int64.toUInt64).flatMap bytesOf) = bytesOf y.toUInt64 ∧
      y.toInt = maxSegmentSum (ws.map Int64.toInt) := by
  have hw : (ws.map Int64.toUInt64).map UInt64.toInt64 = ws := by
    simp [Function.comp_def]
  refine ⟨mss ws.toArray, ?_, ?_⟩
  · rw [output, mssBytes_words _ (by simpa using hlen), hw]
  · rw [mss_toInt ws.toArray (by simpa using hb), List.toList_toArray]

/-- The block of the array of a message's words takes at most 56 bytes more than the message, and
the result's block 56 bytes. -/
theorem mssBytes_bound (b : Bytes) : compiled.mssBytes.bound b ≤ b.data.size + 112 := by
  rw [compiled.mssBytes.bound_eq]
  split
  · rw [Verified.blockCost_eq]
    have h : (b.size / 8).toNat ≤ b.data.size / 8 := by
      simp only [UInt64.toNat_div, Bytes.size, UInt64.toNat_ofNat', UInt64.reduceToNat]
      omega
    have h8 : Verified.Bytes.allocationCost (UInt64.toNat 8) = 56 := by decide
    omega
  · omega

/-- The heap's `top` at the module's start. -/
theorem top_eq : (Verified.initialHeap compiled.tables).top.toNat = 4096 := by decide +kernel

/-- The theorem of `mssBytes`'s program: for a message `msg` of at most `inMax` bytes, the program
writes `output msg` and returns 0. -/
theorem mss_runs : BytesRuns compiled.module entry inMax room mssCap output fun _ _ => False := by
  have hAt := compiled.initial.1
  refine bytes_runs_bounded compiled.mssBytes.trapFree (typeIdx := 0) rfl hAt (by decide)
    (fun L hL => Heap.Within.room ?_ (by decide)) (fun b st hb hcap => ?_)
    (by decide +kernel) (by decide +kernel)
  · show _ + _ ≤ 65536 * mssCap
    have := Flip.allocSize_le_add (L := L) (by simp only [inMax, UInt64.reduceToNat] at hL; omega)
    simp only [inMax, UInt64.reduceToNat, mssCap] at hL ⊢
    rw [top_eq]
    omega
  · show _ + _ ≤ 65536 * st.memoryCap compiled.module 0
    rw [hcap]
    simp only [inMax, UInt64.reduceToNat] at hb
    have hfit : (Verified.initialHeap compiled.tables).Fits
        (allocSize (UInt64.ofNat b.data.size)) := by
      intro _
      have := Flip.allocSize_le_add (L := b.data.size) (by omega)
      rw [top_eq]
      omega
    have htop := Heap.allocate_top hfit
    have := Flip.allocSize_le_add (L := b.data.size) (by omega)
    have := mssBytes_bound b
    simp only [Verified.allocCost, mssCap] at htop ⊢
    rw [top_eq] at htop
    omega

/-- Pseudo-random words. -/
def rand (i : Nat) : UInt64 := UInt64.ofNat (i * 0x9E3779B97F4A7C15 + 12345)

/-- The words of the runs' messages: none, one, two, the list `[-2, 1, -3, 4, -1, 2, 1, -5, 4]`,
50 pseudo-random words in `[-2^20, 2^20)`, 100 pseudo-random words of any value, the words `2^62`,
`-1`, and `2^62 - 2`, whose absolute values sum to `2^63 - 1`, the largest word, the least word
above `Int64.minValue`, and 30 negative words. -/
def wordCases : List (List Int64) :=
  [[], [5], [-3, 7], [-2, 1, -3, 4, -1, 2, 1, -5, 4],
    (List.range 50).map (fun i => (rand i % 2097152).toInt64 - 1048576),
    (List.range 100).map (fun i => (rand (i + 50)).toInt64),
    [4611686018427387904, -1, 4611686018427387902], [Int64.maxValue], [Int64.minValue + 1],
    (List.range 30).map fun i => -Int64.ofNat (1000003 * (i + 1))]

/-- The messages of the runs: the bytes of the words of `wordCases`, and 13 bytes, a length that
is not a multiple of 8. -/
def messages : List (List UInt8) :=
  wordCases.map (fun ws => (ws.map Int64.toUInt64).flatMap bytesOf) ++
    [(List.range 13).map fun i => UInt8.ofNat (37 * i + 1)]

/-- The lengths above `inMax` of the runs: `inMax + 1` and the largest word. -/
def overLengths : List UInt64 := [inMax + 1, 0xFFFFFFFFFFFFFFFF]

/-- The bytes that the UART receives for the message `msg`: its length, the lowest byte first, and
the message. -/
def input (msg : List UInt8) : List UInt8 := bytesOf (UInt64.ofNat msg.length) ++ msg

/-- The bytes that the UART must show for the message `msg`: `output msg` and the status 0. -/
def expected (msg : List UInt8) : List UInt8 := output msg ++ [0]

end TestSupport.A64.Mss
