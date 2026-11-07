import Library.Numerics.Float64.Exp.ExpTheorem
import LeanExe.A64.Proof.ProgramRuns
import LeanExe.Native.Bare
import Verified.Bare

/-!
The theorem of the exponential's bare-metal program for AArch64, in the form `ProgramRuns`, for
every room and cap: `main` calls entry 5 of `Exp.compiled.module`, `Exp.exp`, which takes an `f64`,
on the word `w` of a double `x`, and the machine writes the eight bytes of the word of `Exp.exp x`
to the UART and returns 0.  The compiler's theorem of the entry, `Exp.compiled.exp.implements`,
excludes every trap, given that the table of `2 ^ (j/128)` is a borrowed array of the module's
initial store, and `stackBound` gives at most 4096 bytes, which the room holds.  `one_step` restates
`ExpTheorem.exp_one_step`, the accuracy theorem, for a word whose real value is a given number.
-/

namespace TestSupport.A64.Exp

open LeanExe.A64 Library.Numerics.Float64

/-- The facts about entry 5 of `Exp.compiled.module` that `genProgram` leaves unchecked, for one
argument of type `f64` and a result written as a word. -/
theorem entry_ok : entryOk Exp.compiled.module 5 [.f64] 1 .word = true := by decide +kernel

/-- The stack of the calls from entry 5 needs at most 4096 bytes. -/
theorem stack_ok : stackBound Exp.compiled.module 5 ≤ 4096 := by decide +kernel

theorem table_addr : Verified.tableAddr Exp.compiled.tables 0 = 4096 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The table of `2 ^ (j/128)` is a borrowed array of the store in which the program's function
starts. -/
theorem table_borrowed (cap : Nat) : (Verified.initialHeap Exp.compiled.tables).Borrowed
    (initStore Exp.compiled.module cap) 4096 Exp.expTable := by
  have h := Verified.borrowed_nativeStore (Exp.compiled.initial.2.2 0 (by decide)) cap
  rw [table_addr] at h
  exact h

/-- The compiler's theorem of entry 5 with the table in the precondition. -/
theorem implements : LeanExe.Pipeline.ImplementsA false Exp.compiled.module 5
    (fun x => Exp.exp x)
    (fun x heap store => (fun _ _ _ => True) x heap store ∧
      ∀ t ∈ [((4096 : UInt64), Exp.expTable)], heap.Borrowed store t.1 t.2)
    (fun _ _ _ _ _ => True) :=
  Exp.compiled.exp.implements.implementsA

theorem writes (heap : LeanExe.Pipeline.Heap) (st : Wasm.Store Unit) (vs : List Wasm.Value)
    (y : Float) (h : LeanExe.Pipeline.Represent.owned heap st vs y) :
    Writes .word st vs ((fun y => LeanExe.Native.encodeWord y.toBits) y) :=
  writes_float heap st vs y h

set_option maxRecDepth 100000 in
/-- The theorem of the exponential's program on the word `w` of `x`. -/
theorem runs (x : Float) {w : UInt64} (hw : x.toBits = w) (room : UInt64) (cap : Nat) :
    ProgramRuns Exp.compiled.module 5 [w] room cap .word
      (LeanExe.Native.encodeWord (Exp.exp x).toBits) fun _ => False := by
  have hargs : argValues [.f64] [w] = LeanExe.Pipeline.Scalar.values x := by
    rw [← hw]
    rfl
  have hpre : initialPages Exp.compiled.module ≤ cap →
      ((fun _ _ _ => True) x (Verified.initialHeap Exp.compiled.tables)
          (initStore Exp.compiled.module cap) ∧ ∀ t ∈ [((4096 : UInt64), Exp.expTable)],
        (Verified.initialHeap Exp.compiled.tables).Borrowed (initStore Exp.compiled.module cap)
          t.1 t.2) :=
    fun _ => ⟨trivial, List.forall_mem_singleton.mpr (table_borrowed cap)⟩
  exact program_runs_bounded (room := room) implements x Exp.compiled.initial.1 hpre writes
    (.inl stack_ok) [.f64] hargs entry_ok

/-- A word whose scaled value is `q` units of `2 ^ 1074` has the real value `q`. -/
theorem value_of_scaled {w : UInt64} {q : Int}
    (h : Wasm.IEEE64.scaledValue w = q * 2 ^ 1074) : CodeLib.IEEE64.value w = q := by
  rw [CodeLib.IEEE64.value, h, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, mul_div_assoc,
    div_self (pow_ne_zero _ two_ne_zero), mul_one]

/-- `ExpTheorem.exp_one_step` for a finite `x` whose word has the real value `a`: the word of
`Exp.exp x` is at most that of positive infinity and lies within one representable step of the
nonnegative nearest-even rounding of `exp a`. -/
theorem one_step (x : Float) (a : ℝ) (hf : CodeLib.IEEE64.Finite x.toBits)
    (ha : CodeLib.IEEE64.value x.toBits = a) :
    (Exp.exp x).toBits.toNat ≤ 0x7FF0000000000000 ∧
      (Exp.exp x).toBits.toNat ≤
        (LeanExe.ProofKit.F64PositiveRounding.roundNearestEven (Real.exp a)).toNat + 1 ∧
      (LeanExe.ProofKit.F64PositiveRounding.roundNearestEven (Real.exp a)).toNat ≤
        (Exp.exp x).toBits.toNat + 1 := by
  have h := Exp.ExpTheorem.exp_one_step x hf
  rw [ha] at h
  exact h

end TestSupport.A64.Exp
