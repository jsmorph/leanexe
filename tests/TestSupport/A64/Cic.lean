import TestSupport.A64.CicTable
import Library.Numerics.Filters.Cic.Proof
import Library.Numerics.Filters.Cic.Exact
import LeanExe.Dialect.Lemmas
import LeanExe.A64.Proof.ProgramRuns
import LeanExe.Native.Bare
import Verified.Bare

/-!
The theorems of the CIC filter's bare-metal program for AArch64.  `check_toInt` states that the
words of `cicCheck 64`, read as signed 64-bit integers, are the outputs of the specification
`outputs 3 8 1` over ℤ on the table's samples read as integers: `cicFirst_toList` and `cic_toList`
give the block cascade at `UInt64` of the table, and `toInt_cascade_of_width` reads it exactly,
since every sample lies in `[−2^15, 2^15)` and `(8·1)^3 · 2^15 = 2^24 ≤ 2^63`.  `runs` is the
program's theorem in the form `ProgramRuns`, for every room and cap: `main` calls entry 7 of
`compiled.module`, the wrapper `cicCheck`, on 64, and the machine writes the array's length word and
its elements, `encodeArray (cicCheck 64)`, to the UART and returns 0.
-/

namespace TestSupport.A64.Cic

open LeanExe.A64 Library.Numerics.Filters.Cic

/-- The table's samples as integers. -/
theorem input_toInt : input.toList.map (fun w => w.toBitVec.toInt) =
    List.replicate 24 (-32768) ++ List.replicate 24 32767 ++
      (List.replicate 4 16384 ++ List.replicate 4 (-16384)) ++
      (List.replicate 4 16384 ++ List.replicate 4 (-16384)) := by
  decide +kernel

theorem cicFirst_toList (xs : Array UInt64) (n : UInt64) (h : n.toNat ≤ xs.size) :
    (cicFirst xs n).toList = cascade 3 8 1 (xs.toList.take n.toNat) := by
  rw [cicFirst, cic_toList]
  congr 1
  apply List.ext_getElem
  · simp [LeanExe.build, h]
  · intro i h1 h2
    have hi : i < n.toNat := by simpa [LeanExe.build] using h1
    have e : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hi n.toNat_lt)
    simp only [LeanExe.build, Array.toList_ofFn, List.getElem_ofFn, List.getElem_take,
      Array.getElem_toList]
    rw [e]
    exact getElem!_pos xs i (Nat.lt_of_lt_of_le hi h)

/-- The program's result is the block cascade of the table at `UInt64`. -/
theorem check_toList : (cicCheck 64).toList = cascade 3 8 1 input.toList := by
  rw [cicCheck, cicFirst_toList input 64 (by decide),
    List.take_of_length_le (show input.toList.length ≤ (64 : UInt64).toNat by decide)]

/-- The program's outputs, read as signed 64-bit integers, are the outputs of the specification over
ℤ on the table's samples read as integers. -/
theorem check_toInt : (cicCheck 64).toList.map (fun w => w.toBitVec.toInt) =
    outputs 3 8 1 (input.toList.map fun w => w.toBitVec.toInt) := by
  rw [check_toList]
  exact toInt_cascade_of_width 3 8 1 16 input.toList (by decide +kernel) (by decide)

/-- The heap's `top` at the end of the table, plus the allocations of `cicCheck 64`, fits the
initial pages of the memory of `compiled.module`. -/
theorem heap_room : (Verified.initialHeap compiled.tables).top.toNat +
    compiled.cicCheck.bound 64 ≤ 65536 * initialPages compiled.module := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The theorem of the CIC filter's program.  `compiled.cicCheck.trapFree` excludes the trap at
`unreachable`, since the allocations fit the memory and the table is a borrowed array of the
module's initial store, and `stackBound` excludes an overflow of the stack. -/
theorem runs (room : UInt64) (cap : Nat) :
    ProgramRuns compiled.module 7 [64] room cap .array
      (LeanExe.Native.encodeArray (cicCheck 64)) fun _ => False :=
  program_runs_bounded compiled.cicCheck.trapFree.implementsA 64 compiled.initial.1
    (fun hp => ⟨room_initStore heap_room hp, List.forall_mem_singleton.mpr
      (Verified.borrowed_nativeStore (compiled.initial.2.2 0 (by decide)) cap)⟩)
    writes_array (.inl (by decide +kernel))

end TestSupport.A64.Cic
