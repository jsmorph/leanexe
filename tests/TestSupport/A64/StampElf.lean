import TestSupport.A64.Flip
import LeanExe.A64.Stamp
import LeanExe.A64.Proof.StampRuns

/-!
`flipBit5` of `TestSupport.A64.Flip` as the stamp program: `stampElf` is the file that
`genStampElf` writes for the function, with the limit `stampInMax` of 8,799,968 bytes of the input
file, so that the function's input of the clock's 16 bytes, 16 random bytes, and the file's bytes
holds at most 8,800,000 bytes, the stack's room of `TestSupport.A64.Programs`, the cap `flipCap`,
and the paths `stamp.in` and `stamp.out`.  `stamp_elf_runs_any` is the program's theorem in the
form `StampRunsAny`, for every set of replies, with the result `D.map (· ^^^ 32)` of the function's
input `D`: `compiled.flipBit5.trapFree` excludes every trap, since the block of `stampInMax + 33`
bytes that the program allocates and the result's block fit the cap above the heap's `top`, and the
stack that the program uses is at most the room.
-/

namespace TestSupport.A64.StampElf

open LeanExe LeanExe.A64 LeanExe.Pipeline TestSupport.A64.Flip

/-- The most bytes of the input file. -/
def stampInMax : UInt64 := 8799968

/-- The input path, `stamp.in`. -/
def inPath : List UInt8 := "stamp.in".toUTF8.toList

/-- The output path, `stamp.out`. -/
def outPath : List UInt8 := "stamp.out".toUTF8.toList

/-- The stamp executable of `flipBit5`. -/
def stampElf : Except String (List UInt8 × ElfLayout) :=
  genStampElf compiled.module entry stampInMax room flipCap inPath outPath

/-- The theorem of `flipBit5`'s stamp program in the executable for every set of replies: the
result is the function's input with bit 5 of each byte flipped, and no trap occurs. -/
theorem stamp_elf_runs_any :
    StampRunsAny compiled.module entry stampInMax room flipCap inPath outPath
      (fun D => D.map (· ^^^ 32)) fun _ _ => False := by
  have hAt := compiled.initial.1
  have hN : stampInMax + 33 = UInt64.ofNat 8800001 := rfl
  have hA := allocSize_le_add (L := 8800001) (by omega)
  rw [← hN] at hA
  refine stamp_runs_bounded_any compiled.flipBit5.trapFree (typeIdx := 0) rfl hAt (by decide)
    (Heap.Within.room ?_ (by decide)) (fun b st hb hcap => ?_)
    (by decide +kernel) (by decide +kernel) fun D hlen => flip_toList D (by
      simp only [stampInMax, UInt64.reduceToNat] at hlen
      omega)
  · show _ + _ ≤ 65536 * flipCap
    simp only [flipCap]
    rw [top_eq]
    omega
  · show _ + _ ≤ 65536 * st.memoryCap compiled.module 0
    rw [hcap]
    simp only [stampInMax, UInt64.reduceToNat] at hb
    have hfit : (Verified.initialHeap compiled.tables).Fits (allocSize (stampInMax + 33)) := by
      intro _
      rw [top_eq]
      omega
    have htop := Heap.allocate_top hfit
    have := flip_bound b
    simp only [Verified.allocCost, flipCap] at htop ⊢
    rw [top_eq] at htop
    omega

end TestSupport.A64.StampElf
