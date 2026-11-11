import Verified.Reflect.Command
import LeanExe.A64.Proof.BytesRuns
import TestSupport.A64.Programs

/-!
A function over bytes as a bare-metal program that reads its input from the UART: `flipBit5`
flips bit 5 of each byte of a buffer, which swaps the case of an ASCII letter, and
`verified_compile` compiles it.  The image of `genBytesImage` at `imageBase` reads a length of eight
bytes, the lowest first, and a message of that many bytes, at most `inMax`, and writes the bytes of
`flipBit5` of the message and the status 0, the status 64 for a length above `inMax`, or the status
65 for a byte with an error flag.  `flip_runs` is its theorem in the form `BytesRuns`, with the
output `msg.map (· ^^^ 32)`: `compiled.flipBit5.trapFree` excludes every trap, since the message's
block and the result's block, `flip_bound`, fit the cap `flipCap` above the heap's `top`, and the
stack that the program uses is at most the room of `TestSupport.A64.Programs`.  `cases` lists the
lengths of the messages on which `tests/baremetal/a64-uart.sh` runs the image under QEMU, and
`overLengths` the lengths above `inMax` on which it runs.
-/

namespace TestSupport.A64.Flip

open LeanExe LeanExe.A64 LeanExe.Pipeline

/-- The bytes of `b` with bit 5 of each byte flipped. -/
def flipBit5 (b : Bytes) : Bytes := Bytes.build b.size fun i => b.get i ^^^ 32

verified_compile compiled := [flipBit5]

/-- The index of `flipBit5` among the functions of `compiled.module`, after the allocator and the
release. -/
def entry : Nat := 2

/-- The largest length of a message: 8,800,000 bytes. -/
def inMax : UInt64 := 8800000

/-- The memory's cap in pages: room above the heap's `top` for the blocks of a message of `inMax`
bytes and of its result. -/
def flipCap : Nat := 269

/-- The image of `flipBit5`'s program at `imageBase`. -/
def image : Except String (List UInt8 × Layout) :=
  genBytesImage compiled.module entry inMax room flipCap imageBase

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

/-- The result's block takes at most 56 bytes more than the message. -/
theorem flip_bound (b : Bytes) : compiled.flipBit5.bound b ≤ b.data.size + 56 := by
  rw [compiled.flipBit5.bound_eq]
  have h : b.size.toNat ≤ b.data.size := by
    simp only [Bytes.size, UInt64.toNat_ofNat']
    exact Nat.mod_le _ _
  unfold Verified.Bytes.allocationCost
  split
  · omega
  · rcases Nat.le_total 1 ((b.size.toNat + 7) / 8) with h1 | h1
    · rw [Nat.max_eq_right h1]
      omega
    · rw [Nat.max_eq_left h1]
      omega

/-- The heap's `top` at the module's start. -/
theorem top_eq : (Verified.initialHeap compiled.tables).top.toNat = 4096 := by decide +kernel

/-- Each byte of `flipBit5` of a message of fewer than `2 ^ 64` bytes is the message's byte with
bit 5 flipped. -/
theorem flip_toList (msg : List UInt8) (h : msg.length < 2 ^ 64) :
    (flipBit5 ⟨⟨msg.toArray⟩⟩).data.data.toList = msg.map (· ^^^ 32) := by
  have hn : (UInt64.ofNat msg.length).toNat = msg.length := by
    rw [UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt h
  apply List.ext_getElem
  · simp [flipBit5, Bytes.build, Bytes.size, ByteArray.size, hn]
  · intro i h1 h2
    have hi : i < msg.length := by simpa using h2
    have hi64 : (UInt64.ofNat i).toNat = i := by
      rw [UInt64.toNat_ofNat']
      exact Nat.mod_eq_of_lt (by omega)
    have hget : Bytes.get ⟨⟨msg.toArray⟩⟩ (UInt64.ofNat i) = msg[i].toUInt64 := by
      unfold Bytes.get
      rw [dite_eq_left (by rw [hi64]; exact hi)]
      simp [hi64, ByteArray.getElem_eq_getElem_data]
    simp [flipBit5, Bytes.build, hget]

/-- The theorem of `flipBit5`'s program: for a message `msg` of at most `inMax` bytes, the program
writes `msg` with bit 5 of each byte flipped and returns 0. -/
theorem flip_runs :
    BytesRuns compiled.module entry inMax room flipCap (fun msg => msg.map (· ^^^ 32))
      fun _ _ => False := by
  have hAt := compiled.initial.1
  refine (bytes_runs_bounded compiled.flipBit5.trapFree (typeIdx := 0) rfl hAt (by decide)
    (fun L hL => Heap.Within.room ?_ (by decide)) (fun b st hb hcap => ?_)
    (by decide +kernel) (by decide +kernel)).congr fun msg hlen => flip_toList msg (by
      simp only [inMax, UInt64.reduceToNat] at hlen
      omega)
  · show _ + _ ≤ 65536 * flipCap
    have := allocSize_le_add (L := L) (by simp only [inMax, UInt64.reduceToNat] at hL; omega)
    simp only [inMax, UInt64.reduceToNat, flipCap] at hL ⊢
    rw [top_eq]
    omega
  · show _ + _ ≤ 65536 * st.memoryCap compiled.module 0
    rw [hcap]
    simp only [inMax, UInt64.reduceToNat] at hb
    have hfit : (Verified.initialHeap compiled.tables).Fits
        (allocSize (UInt64.ofNat b.data.size)) := by
      intro _
      have := allocSize_le_add (L := b.data.size) (by omega)
      rw [top_eq]
      omega
    have htop := Heap.allocate_top hfit
    have := allocSize_le_add (L := b.data.size) (by omega)
    have := flip_bound b
    simp only [Verified.allocCost, flipCap] at htop ⊢
    rw [top_eq] at htop
    omega

/-- The lengths of the messages of the runs. -/
def cases : List Nat := [0, 1, 4095, 4096, 65536, 1000000]

/-- The lengths above `inMax` of the runs: `inMax + 1` and the largest word. -/
def overLengths : List UInt64 := [inMax + 1, 0xFFFFFFFFFFFFFFFF]

/-- The message of `n` bytes of a run, which takes every byte value. -/
def message (n : Nat) : List UInt8 := (List.range n).map fun i => UInt8.ofNat (i * 131 + i / 251)

/-- The bytes that the UART receives for a message of `n` bytes: its length, the lowest byte
first, and the message. -/
def input (n : Nat) : List UInt8 := bytesOf (UInt64.ofNat n) ++ message n

/-- The bytes that the UART must show for a message of `n` bytes: the message with bit 5 of each
byte flipped and the status 0. -/
def expected (n : Nat) : List UInt8 := (message n).map (· ^^^ 32) ++ [0]

end TestSupport.A64.Flip
