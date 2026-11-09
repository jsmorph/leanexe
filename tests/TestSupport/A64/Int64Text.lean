import Library.Numerics.Decimal.Int64Text.Compiled
import LeanExe.A64.Proof.ProgramRuns
import LeanExe.Native.Bare

/-!
The theorem of the bare-metal program of `Library.Numerics.Decimal.Int64Text` for AArch64, in the
form `ProgramRuns`, for every room and cap: `main` calls entry 4 of `compiled.module`,
`printInt64`, on the word of an `Int64`, and the machine writes the length word and the words of
the text, `encodeArray (printInt64 x)`, to the UART and returns 0.  `compiled.printInt64.trapFree`
excludes the trap at `unreachable`, since the text's block of at most 216 bytes
(`printInt64_bound_le`) fits the module's initial pages above the heap's `top`, and `stackBound`
gives at most 4096 bytes.
-/

namespace TestSupport.A64.Int64Text

open LeanExe.A64 Library.Numerics.Decimal.Int64Text

/-- The heap's `top` at the module's start, plus the block of any text, fits the initial pages of
the memory of `compiled.module`. -/
theorem heap_room (x : Int64) : (Verified.initialHeap compiled.tables).top.toNat +
    compiled.printInt64.bound x ≤ 65536 * initialPages compiled.module := by
  have hb := printInt64_bound_le x
  have hr : (Verified.initialHeap compiled.tables).top.toNat + 216 ≤
      65536 * initialPages compiled.module := by decide +kernel
  omega

/-- The fact about entry 4 of `compiled.module` that `genProgram` leaves unchecked, for one
argument of type `i64` and a result written as an array. -/
theorem entry4_ok : entryOk compiled.module 4 [.i64] 1 .array = true := by decide +kernel

/-- The theorem of `printInt64`'s program on the word `w` of `x`. -/
theorem printInt64_runs (x : Int64) {w : UInt64} (hw : x.toUInt64 = w) (room : UInt64)
    (cap : Nat) :
    ProgramRuns compiled.module 4 [w] room cap .array
      (LeanExe.Native.encodeArray (printInt64 x)) fun _ => False := by
  subst hw
  exact program_runs_bounded compiled.printInt64.trapFree x compiled.initial.1
    (fun hp => room_initStore (heap_room x) hp) writes_array (.inl (by decide +kernel)) [.i64]
    rfl entry4_ok

end TestSupport.A64.Int64Text
