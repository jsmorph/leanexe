import Library.Numerics.Float64.Pow.PowBytes
import Verified.Master

namespace Library.Numerics.Float64.Pow

open CodeLib.IEEE64 (value Finite)
open LeanExe.ProofKit

/-- A float that is not a NaN is not a signaling NaN. -/
theorem issignaling_eq_false (x : Float) (h : Wasm.IEEE64.isNaN x.toBits = false) :
    issignaling x = false := by
  cases hs : issignaling x
  · rfl
  · rw [PowSpecial.signaling_nan x hs] at h
    exact absurd h (by decide)

set_option maxRecDepth 100000 in
/-- The export `pow`, called on a pair of floats `(x, y)`, returns a float within one
representable step of the nearest-even rounding of the real power `x ^ y` for finite `x` and `y`
with `x > 0`, with `x < 0` and integer `y`, or with `x = 0` and `y ≥ 0`.  The other results are
those of C's Annex F: `1` at `y = ±0` or `x = 1` when the other input is not a NaN; at an infinite
`y` and an `x` other than `1` or a NaN, `1` for `|x| = 1`, `+0` or `+∞` otherwise, as `|x|` lies on
the side of `1` that the sign of `y` selects; the canonical NaN at a finite `x < 0` and a finite
non-integer `y`, at a NaN `x` with `y ≠ ±0`, and at a NaN `y` with `x ≠ 1`. -/
theorem pow_master :
    Verified.Master compiled.module compiled.tables "pow" compiled.pow.bound (fun _ => True)
      (fun (p : Float × Float) (r : Float) =>
        (Finite p.1.toBits → Finite p.2.toBits →
          0 < value p.1.toBits ∨ (value p.1.toBits < 0 ∧ ∃ n : ℤ, value p.2.toBits = n) ∨
            (value p.1.toBits = 0 ∧ 0 ≤ value p.2.toBits) →
          F64SignedRounding.WithinSteps 1 (value p.1.toBits ^ value p.2.toBits) r.toBits) ∧
        (p.2.toBits = 0 ∨ p.2.toBits = 0x8000000000000000 →
          Wasm.IEEE64.isNaN p.1.toBits = false → r.toBits = 0x3FF0000000000000) ∧
        (p.1.toBits = 0x3FF0000000000000 → Wasm.IEEE64.isNaN p.2.toBits = false →
          r.toBits = 0x3FF0000000000000) ∧
        (p.2.toBits = 0x7FF0000000000000 ∨ p.2.toBits = 0xFFF0000000000000 →
          Wasm.IEEE64.isNaN p.1.toBits = false → p.1.toBits ≠ 0x3FF0000000000000 →
          r.toBits = if p.1.toBits.toNat % 2 ^ 63 = 0x3FF0000000000000 then 0x3FF0000000000000
            else if p.1.toBits.toNat % 2 ^ 63 < 0x3FF0000000000000 then
              (if Wasm.IEEE64.sign p.2.toBits then 0x7FF0000000000000 else 0)
            else if Wasm.IEEE64.sign p.2.toBits then 0 else 0x7FF0000000000000) ∧
        ((Finite p.1.toBits ∧ value p.1.toBits < 0 ∧ Finite p.2.toBits ∧
            ∀ n : ℤ, value p.2.toBits ≠ n) ∨
          (Wasm.IEEE64.isNaN p.1.toBits = true ∧ p.2.toBits ≠ 0 ∧
            p.2.toBits ≠ 0x8000000000000000) ∨
          (Wasm.IEEE64.isNaN p.2.toBits = true ∧ p.1.toBits ≠ 0x3FF0000000000000) →
          r.toBits = Wasm.IEEE64.canonicalNaN)) :=
  .of_trapFree compiled.pow.trapFree (Verified.tables_at [0, 1] (by decide) rfl)
    PowBytes.pow_export (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ p _ _ => by
      refine ⟨PowTheorem.pow_within p.1 p.2, fun hy hx => ?_, fun hx hy => ?_,
        PowSpecial.inf_exp p.1 p.2, fun h => ?_⟩
      · exact PowSpecial.zero_exp_one p.1 p.2 (by rcases hy with h | h <;> rw [h] <;> decide)
          (issignaling_eq_false p.1 hx)
      · rw [PowSpecial.one_base p.1 p.2 hx, issignaling_eq_false p.2 hy, ite_eq_right Bool.false_ne_true]
      · rcases h with ⟨hxf, hx, hyf, hy⟩ | ⟨hx, h0, h1⟩ | ⟨hy, hx⟩
        · exact PowSpecial.neg_nonint p.1 p.2 hxf hx hyf hy
        · exact PowSpecial.nan_base p.1 p.2 hx fun h => (PowSpecial.two_mul_zero _ h).elim h0 h1
        · exact PowSpecial.nan_exp p.1 p.2 hy hx

#print axioms issignaling_eq_false
#print axioms pow_master

end Library.Numerics.Float64.Pow
