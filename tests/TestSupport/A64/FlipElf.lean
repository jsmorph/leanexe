import TestSupport.A64.Flip
import LeanExe.A64.Proof.LinuxImage

/-!
`flipBit5` of `TestSupport.A64.Flip` as a Linux executable: `elf` is the file that `genSysElf`
writes for the function, with the limit `inMax` of 8,800,000 bytes, the stack's room of
`TestSupport.A64.Programs`, and the cap `flipCap`.  The executable reads standard input to its end
and writes the input with bit 5 of each byte flipped to standard output.  `flip_elf_runs_any` is
the program's theorem in the form `SysBytesRunsAny`, for every kernel, and `flip_elf_runs` in the
form `SysBytesRuns`, with the output `msg.map (· ^^^ 32)`: `compiled.flipBit5.trapFree` excludes
every trap, since the block of `inMax + 1` bytes that the
program allocates before it reads and the result's block, `flip_bound`, fit the cap above the
heap's `top`, and the stack that the program uses is at most the room.  `cases` lists the lengths
of the messages of the runs of `tests/linux/a64-elf.sh`, and `overLengths` the lengths above
`inMax`, on which the run must end with status 64 and no output.
-/

namespace TestSupport.A64.FlipElf

open LeanExe LeanExe.A64 LeanExe.Pipeline TestSupport.A64.Flip

/-- The executable of `flipBit5`. -/
def elf : Except String (List UInt8 × ElfLayout) :=
  genSysElf compiled.module entry inMax room flipCap

/-- The theorem of `flipBit5`'s program in the executable for every kernel: for standard input of
at most `inMax` bytes, the program writes the input with bit 5 of each byte flipped and returns 0,
unless a call fails. -/
theorem flip_elf_runs_any :
    SysBytesRunsAny compiled.module entry inMax room flipCap (fun msg => msg.map (· ^^^ 32))
      fun _ _ => False := by
  have hAt := compiled.initial.1
  have hN : inMax + 1 = UInt64.ofNat 8800001 := rfl
  have hA := allocSize_le_add (L := 8800001) (by omega)
  rw [← hN] at hA
  refine (sys_bytes_runs_bounded_any compiled.flipBit5.trapFree (typeIdx := 0) rfl hAt (by decide)
    (Heap.Within.room ?_ (by decide)) (fun b st hb hcap => ?_)
    (by decide +kernel) (by decide +kernel)).congr fun msg hlen => flip_toList msg (by
      simp only [inMax, UInt64.reduceToNat] at hlen
      omega)
  · show _ + _ ≤ 65536 * flipCap
    simp only [flipCap]
    rw [top_eq]
    omega
  · show _ + _ ≤ 65536 * st.memoryCap compiled.module 0
    rw [hcap]
    simp only [inMax, UInt64.reduceToNat] at hb
    have hfit : (Verified.initialHeap compiled.tables).Fits (allocSize (inMax + 1)) := by
      intro _
      rw [top_eq]
      omega
    have htop := Heap.allocate_top hfit
    have := flip_bound b
    simp only [Verified.allocCost, flipCap] at htop ⊢
    rw [top_eq] at htop
    omega

/-- The theorem of `flipBit5`'s program in the executable: for standard input of at most `inMax`
bytes, the program writes the input with bit 5 of each byte flipped and returns 0. -/
theorem flip_elf_runs :
    SysBytesRuns compiled.module entry inMax room flipCap (fun msg => msg.map (· ^^^ 32))
      fun _ _ => False :=
  flip_elf_runs_any.sysBytesRuns

/-- The lengths of the messages of the runs. -/
def cases : List Nat := [0, 1, 4095, 4096, 65536, 1000000, 8800000]

/-- The lengths above `inMax` of the runs. -/
def overLengths : List Nat := [8800001]

/-- The message of `n` bytes of a run, `TestSupport.A64.Flip.message n`, as a byte array. -/
def messageArray (n : Nat) : ByteArray := Id.run do
  let mut a := ByteArray.emptyWithCapacity n
  for i in [0:n] do
    a := a.push (UInt8.ofNat (i * 131 + i / 251))
  return a

/-- The message `b` with bit 5 of each byte flipped. -/
def flipArray (b : ByteArray) : ByteArray := Id.run do
  let mut a := ByteArray.emptyWithCapacity b.size
  for i in [0:b.size] do
    a := a.push (b.get! i ^^^ 32)
  return a

end TestSupport.A64.FlipElf
