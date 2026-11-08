import Library.Numerics.Float64.Trig.TrigTheorem
import LeanExe.A64.Proof.ProgramRuns
import LeanExe.Native.Bare
import Verified.Bare

/-!
The theorem of the sine's bare-metal program for AArch64, in the form `ProgramRuns`, for every
room and cap: `main` calls entry 15 of `Trig.compiled.module`, `Trig.sin`, which takes an `f64`, on
the word `w` of a double `x`, and the machine writes the eight bytes of the word of `Trig.sin x` to
the UART and returns 0.  The compiler's theorem of the entry, `Trig.compiled.sin.implements`,
excludes every trap, given that the tables of the bits of `2/π` and of `π/2` are borrowed arrays
of the module's initial store, and `stackBound` gives at most 4096 bytes, which the room holds.
`within_one` restates `TrigSinCos.sin_within`, the accuracy theorem, for a word whose real value
is a given number.
-/

namespace TestSupport.A64.Sin

open LeanExe LeanExe.A64 Library.Numerics.Float64

/-- The facts about entry 15 of `Trig.compiled.module` that `genProgram` leaves unchecked, for one
argument of type `f64` and a result written as a word. -/
theorem entry_ok : entryOk Trig.compiled.module 15 [.f64] 1 .word = true := by decide +kernel

/-- The stack of the calls from entry 15 needs at most 4096 bytes. -/
theorem stack_ok : stackBound Trig.compiled.module 15 ≤ 4096 := by decide +kernel

theorem inv_addr : Verified.tableAddr Trig.compiled.tables 0 = 4096 := by decide +kernel

theorem half_addr : Verified.tableAddr Trig.compiled.tables 1 = 4264 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The table of the bits of `2/π` is a borrowed array of the store in which the program's
function starts. -/
theorem inv_borrowed (cap : Nat) : (Verified.initialHeap Trig.compiled.tables).Borrowed
    (initStore Trig.compiled.module cap) 4096 Trig.invPi := by
  have h := Verified.borrowed_nativeStore (Trig.compiled.initial.2.2 0 (by decide)) cap
  rw [inv_addr] at h
  exact h

set_option maxRecDepth 100000 in
/-- The table of the bits of `π/2` is a borrowed array of the store in which the program's
function starts. -/
theorem half_borrowed (cap : Nat) : (Verified.initialHeap Trig.compiled.tables).Borrowed
    (initStore Trig.compiled.module cap) 4264 Trig.halfPi := by
  have h := Verified.borrowed_nativeStore (Trig.compiled.initial.2.2 1 (by decide)) cap
  rw [half_addr] at h
  exact h

/-- The compiler's theorem of entry 15 with the tables in the precondition. -/
theorem implements : LeanExe.Pipeline.ImplementsA false Trig.compiled.module 15
    (fun x => Trig.sin x)
    (fun x heap store => (fun _ _ _ => True) x heap store ∧
      ∀ t ∈ [((4096 : UInt64), Trig.invPi), ((4264 : UInt64), Trig.halfPi)],
        heap.Borrowed store t.1 t.2)
    (fun _ _ _ _ _ => True) :=
  Trig.compiled.sin.implements.implementsA

theorem writes (heap : LeanExe.Pipeline.Heap) (st : Wasm.Store Unit) (vs : List Wasm.Value)
    (y : Float) (h : LeanExe.Pipeline.Represent.owned heap st vs y) :
    Writes .word st vs ((fun y => LeanExe.Native.encodeWord y.toBits) y) :=
  writes_float heap st vs y h

set_option maxRecDepth 100000 in
/-- The theorem of the sine's program on the word `w` of `x`. -/
theorem runs (x : Float) {w : UInt64} (hw : x.toBits = w) (room : UInt64) (cap : Nat) :
    ProgramRuns Trig.compiled.module 15 [w] room cap .word
      (LeanExe.Native.encodeWord (Trig.sin x).toBits) fun _ => False := by
  have hargs : argValues [.f64] [w] = LeanExe.Pipeline.Scalar.values x := by
    rw [← hw]
    rfl
  have hpre : initialPages Trig.compiled.module ≤ cap →
      ((fun _ _ _ => True) x (Verified.initialHeap Trig.compiled.tables)
          (initStore Trig.compiled.module cap) ∧
        ∀ t ∈ [((4096 : UInt64), Trig.invPi), ((4264 : UInt64), Trig.halfPi)],
          (Verified.initialHeap Trig.compiled.tables).Borrowed (initStore Trig.compiled.module cap)
            t.1 t.2) := by
    intro _
    refine ⟨trivial, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨inv_borrowed cap, half_borrowed cap⟩
  exact program_runs_bounded (room := room) implements x Trig.compiled.initial.1 hpre writes
    (.inl stack_ok) [.f64] hargs entry_ok

/-- A word whose scaled value is `q` units of `2 ^ 1074` has the real value `q`. -/
theorem value_of_scaled {w : UInt64} {q : Int}
    (h : Wasm.IEEE64.scaledValue w = q * 2 ^ 1074) : CodeLib.IEEE64.value w = q := by
  rw [CodeLib.IEEE64.value, h, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, mul_div_assoc,
    div_self (pow_ne_zero _ two_ne_zero), mul_one]

/-- `TrigSinCos.sin_within` for a finite `x` whose word has the real value `a`: the word of
`Trig.sin x` lies within one representable step of the nearest-even rounding of `sin a`. -/
theorem within_one (x : Float) (a : ℝ) (hf : CodeLib.IEEE64.Finite x.toBits)
    (ha : CodeLib.IEEE64.value x.toBits = a) :
    LeanExe.ProofKit.F64SignedRounding.WithinSteps 1 (Real.sin a) (Trig.sin x).toBits := by
  have h := Trig.TrigSinCos.sin_within x hf
  rw [ha] at h
  exact h

end TestSupport.A64.Sin
