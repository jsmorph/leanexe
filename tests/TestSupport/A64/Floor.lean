import Examples.Floor.Compiled
import LeanExe.A64.Proof.ProgramRuns
import LeanExe.Native.Bare

/-!
The theorems of the bare-metal programs of `Examples.Floor` for AArch64, in the form
`ProgramRuns`, for every room and cap.  `main` calls entry 2 of `compiled.module`, `floorDiv`, or
entry 3, `average`, on the words of two `Int64` values, and the machine writes the eight bytes of
the result's word to the UART and returns 0.  The compiler's theorems of the entries,
`compiled.floorDiv.implements` and `compiled.average.implements`, exclude every trap, and
`stackBound` gives at most 4096 bytes.  An `Int64` result is its word, so `writes_int64` gives its
bytes.
-/

namespace TestSupport.A64.Floor

open LeanExe.A64 Examples.Floor

/-- An owned result of type `Int64` gives the eight bytes of its word. -/
theorem writes_int64 (heap : LeanExe.Pipeline.Heap) (st : Wasm.Store Unit) (vs : List Wasm.Value)
    (y : Int64) (h : LeanExe.Pipeline.Represent.owned heap st vs y) :
    Writes .word st vs (LeanExe.Native.encodeWord y.toUInt64) :=
  ⟨.i64 y.toUInt64, y.toUInt64, h, rfl, rfl⟩

/-- The facts about entries 2 and 3 of `compiled.module` that `genProgram` leaves unchecked, for
two arguments of type `i64` and a result written as a word. -/
theorem entry2_ok : entryOk compiled.module 2 [.i64, .i64] 2 .word = true := by decide +kernel

theorem entry3_ok : entryOk compiled.module 3 [.i64, .i64] 2 .word = true := by decide +kernel

/-- The theorem of `floorDiv`'s program on the words `wa` and `wb` of `a` and `b`. -/
theorem floorDiv_runs (a b : Int64) {wa wb : UInt64} (ha : a.toUInt64 = wa)
    (hb : b.toUInt64 = wb) (room : UInt64) (cap : Nat) :
    ProgramRuns compiled.module 2 [wa, wb] room cap .word
      (LeanExe.Native.encodeWord (floorDiv a b).toUInt64) fun _ => False := by
  subst ha hb
  exact program_runs_bounded compiled.floorDiv.implements (a, b) compiled.initial.1
    (fun _ => trivial) writes_int64 (.inl (by decide +kernel)) [.i64, .i64] rfl entry2_ok

/-- The theorem of `average`'s program on the words `wa` and `wb` of `a` and `b`. -/
theorem average_runs (a b : Int64) {wa wb : UInt64} (ha : a.toUInt64 = wa)
    (hb : b.toUInt64 = wb) (room : UInt64) (cap : Nat) :
    ProgramRuns compiled.module 3 [wa, wb] room cap .word
      (LeanExe.Native.encodeWord (average a b).toUInt64) fun _ => False := by
  subst ha hb
  exact program_runs_bounded compiled.average.implements (a, b) compiled.initial.1
    (fun _ => trivial) writes_int64 (.inl (by decide +kernel)) [.i64, .i64] rfl entry3_ok

end TestSupport.A64.Floor
