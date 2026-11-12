import Library.Numerics.Float64.Bessel.BesselBytes
import Library.Numerics.Float64.Bessel.BesselNSpecial
import Verified.Master

namespace Library.Numerics.Float64.Bessel

open CodeLib.IEEE64 (value Finite)
open LeanExe.ProofKit
open LeanExe.ProofKit.Bessel (J0 J1 Y0 Y1)
open BesselOrderN (Jn Yn JZ YZ)

/-- The order of `jn` and `yn`, the signed integer in the low 32 bits of the word `n`, is the
balanced residue of `n` modulo `2 ^ 32`. -/
theorem orderZ_eq (n : UInt64) : BesselJnTheorem.orderZ n = Int.bmod n.toNat (2 ^ 32) := by
  have h : (n &&& 0xFFFFFFFF).toNat = n.toNat % 2 ^ 32 := by
    rw [UInt64.toNat_and, show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  unfold BesselJnTheorem.orderZ
  rw [h, Int.bmod_def]
  have := n.toNat_lt
  push_cast
  simp only [Nat.reducePow] at *
  split_ifs <;> omega

set_option maxRecDepth 100000 in
/-- The export `j0`, called on a float `x`, returns for finite `x` a float within
`10 · 2 ^ -53 · M₀(|x|)` of `J₀(x)`, where `M₀ = √(J₀² + Y₀²)` is the modulus, so that the bound is
in units of the modulus; it returns `+0` at either infinity and the canonical NaN at a NaN. -/
theorem j0_master :
    Verified.Master compiled.module compiled.tables "j0" compiled.j0.bound (fun _ => True)
      (fun x (y : Float) =>
        (Finite x.toBits →
          |value y.toBits - J0 (value x.toBits)| ≤
            10 / 2 ^ 53 * √(J0 |value x.toBits| ^ 2 + Y0 |value x.toBits| ^ 2)) ∧
        (x.toBits = 0x7FF0000000000000 ∨ x.toBits = 0xFFF0000000000000 → y.toBits = 0) ∧
        (Wasm.IEEE64.isNaN x.toBits = true → y.toBits = Wasm.IEEE64.canonicalNaN)) :=
  .of_trapFree compiled.j0.trapFree (Verified.tables_at [0, 1, 2] (by decide) rfl)
    BesselBytes.j0_export (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ =>
      ⟨BesselJ0Theorem.j0_accuracy x, BesselSpecial.j0_infinity x, BesselSpecial.j0_nan x⟩

set_option maxRecDepth 100000 in
/-- The export `j1`, called on a float `x`, returns for finite `x` a float within
`12 · 2 ^ -53 · M₁(|x|)` of `J₁(x)`, where `M₁ = √(J₁² + Y₁²)` is the modulus, so that the bound is
in units of the modulus; it returns `+0` at `+∞`, `-0` at `-∞`, and the canonical NaN at a NaN. -/
theorem j1_master :
    Verified.Master compiled.module compiled.tables "j1" compiled.j1.bound (fun _ => True)
      (fun x (y : Float) =>
        (Finite x.toBits →
          |value y.toBits - J1 (value x.toBits)| ≤
            12 / 2 ^ 53 * √(J1 |value x.toBits| ^ 2 + Y1 |value x.toBits| ^ 2)) ∧
        (x.toBits = 0x7FF0000000000000 → y.toBits = 0) ∧
        (x.toBits = 0xFFF0000000000000 → y.toBits = 0x8000000000000000) ∧
        (Wasm.IEEE64.isNaN x.toBits = true → y.toBits = Wasm.IEEE64.canonicalNaN)) :=
  .of_trapFree compiled.j1.trapFree (Verified.tables_at [0, 1, 3] (by decide) rfl)
    BesselBytes.j1_export (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ =>
      ⟨BesselJ1Theorem.j1_accuracy x, BesselSpecial.j1_pos_infinity x,
        BesselSpecial.j1_neg_infinity x, BesselSpecial.j1_nan x⟩

set_option maxRecDepth 100000 in
/-- The export `y0`, called on a float `x`, returns for finite `x > 0`, a word below `2 ^ 63` other
than 0, a float within `11 · 2 ^ -53 · M₀(x)` of `Y₀(x)`, where `M₀ = √(J₀² + Y₀²)` is the
modulus, so that the bound is in units of the modulus; it returns `+0` at `+∞`, `-∞` at either
zero, and the canonical NaN at a NaN and at a word with the sign bit set other than `-0`. -/
theorem y0_master :
    Verified.Master compiled.module compiled.tables "y0" compiled.y0.bound (fun _ => True)
      (fun x (y : Float) =>
        (Finite x.toBits → x.toBits.toNat < 2 ^ 63 → x.toBits.toNat ≠ 0 →
          |value y.toBits - Y0 (value x.toBits)| ≤
            11 / 2 ^ 53 * √(J0 (value x.toBits) ^ 2 + Y0 (value x.toBits) ^ 2)) ∧
        (x.toBits = 0x7FF0000000000000 → y.toBits = 0) ∧
        (x.toBits = 0 ∨ x.toBits = 0x8000000000000000 → y.toBits = 0xFFF0000000000000) ∧
        (Wasm.IEEE64.isNaN x.toBits = true ∨
            (Wasm.IEEE64.sign x.toBits = true ∧ x.toBits ≠ 0x8000000000000000) →
          y.toBits = Wasm.IEEE64.canonicalNaN)) :=
  .of_trapFree compiled.y0.trapFree (Verified.tables_at [0, 1, 4, 5, 2] (by decide) rfl)
    BesselBytes.y0_export (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ =>
      ⟨BesselY0Theorem.y0_accuracy x, BesselSpecial.y0_pos_infinity x, BesselSpecial.y0_zero x,
        BesselSpecial.y0_nan x⟩

set_option maxRecDepth 100000 in
/-- The export `y1`, called on a float `x`, returns for finite `x ≥ 2 ^ -1022`, a word from
`0x0010000000000000` to below `2 ^ 63`, a float within `12 · 2 ^ -53 · M₁(x)` of `Y₁(x)`, where
`M₁ = √(J₁² + Y₁²)` is the modulus, so that the bound is in units of the modulus, and for
`0 < x < 2 ^ -54 (1 + 2 ^ -20)` a float within one representable step of the nearest-even rounding
of `Y₁(x)`; it returns `+0` at `+∞`, `-∞` at either zero, and the canonical NaN at a NaN and at a
word with the sign bit set other than `-0`. -/
theorem y1_master :
    Verified.Master compiled.module compiled.tables "y1" compiled.y1.bound (fun _ => True)
      (fun x (y : Float) =>
        (Finite x.toBits → x.toBits.toNat < 2 ^ 63 → 0x0010000000000000 ≤ x.toBits.toNat →
          |value y.toBits - Y1 (value x.toBits)| ≤
            12 / 2 ^ 53 * √(J1 (value x.toBits) ^ 2 + Y1 (value x.toBits) ^ 2)) ∧
        (Finite x.toBits → 0 < x.toBits.toNat → x.toBits.toNat < 0x3C90000100000000 →
          F64SignedRounding.WithinSteps 1 (Y1 (value x.toBits)) y.toBits) ∧
        (x.toBits = 0x7FF0000000000000 → y.toBits = 0) ∧
        (x.toBits = 0 ∨ x.toBits = 0x8000000000000000 → y.toBits = 0xFFF0000000000000) ∧
        (Wasm.IEEE64.isNaN x.toBits = true ∨
            (Wasm.IEEE64.sign x.toBits = true ∧ x.toBits ≠ 0x8000000000000000) →
          y.toBits = Wasm.IEEE64.canonicalNaN)) :=
  .of_trapFree compiled.y1.trapFree (Verified.tables_at [0, 1, 4, 5, 3] (by decide) rfl)
    BesselBytes.y1_export (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ =>
      ⟨BesselY1Theorem.y1_accuracy x,
        fun hf h0 ht => (BesselY1Theorem.y1_positive x hf (Nat.lt_trans ht (by decide))
          (Nat.pos_iff_ne_zero.mp h0)).2 ht,
        BesselSpecial.y1_pos_infinity x, BesselSpecial.y1_zero x, BesselSpecial.y1_nan x⟩

set_option maxRecDepth 100000 in
/-- The export `jn`, called on a word `n` and a float `x`, with `N` the signed integer in the low 32
bits of `n`, returns for finite `x` outside the range `2 ≤ |x| < 2 ^ 302` with `|x| < 2 |N|` a
float within `(23 + 12 |N|) · 2 ^ -53 · M_|N|(|x|)` of `J_N(x)`, where `M_k = √(J_k² + Y_k²)` is
the modulus, so that the bound is in units of the modulus; at an infinity it returns a zero, `-0`
when `|N|` is odd and the sign bit of `x` is set exactly when `N ≥ 0`, and at a NaN the canonical
NaN. -/
theorem jn_master :
    Verified.Master compiled.module compiled.tables "jn" compiled.jn.bound (fun _ => True)
      (fun (p : UInt64 × Float) (r : Float) =>
        let N := Int.bmod p.1.toNat (2 ^ 32)
        (Finite p.2.toBits →
          ¬ (2 ≤ |value p.2.toBits| ∧ |value p.2.toBits| < 2 ^ 302 ∧
            |value p.2.toBits| < 2 * (N.natAbs : ℝ)) →
          |value r.toBits - JZ N (value p.2.toBits)| ≤
            (23 + 12 * (N.natAbs : ℝ)) / 2 ^ 53 *
              √(Jn N.natAbs |value p.2.toBits| ^ 2 + Yn |value p.2.toBits| N.natAbs ^ 2)) ∧
        (p.2.toBits = 0x7FF0000000000000 ∨ p.2.toBits = 0xFFF0000000000000 →
          r.toBits = if N.natAbs % 2 = 1 ∧ (2 ^ 63 ≤ p.2.toBits.toNat ↔ 0 ≤ N) then
            0x8000000000000000 else 0) ∧
        (Wasm.IEEE64.isNaN p.2.toBits = true → r.toBits = Wasm.IEEE64.canonicalNaN)) :=
  .of_trapFree compiled.jn.trapFree (Verified.tables_at [0, 1, 4, 5, 2, 3] (by decide) rfl)
    BesselBytes.jn_export (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ p _ _ => by
      intro N
      have hN : BesselJnTheorem.orderZ p.1 = N := orderZ_eq p.1
      have hu : CodeLib.IEEE64.unitRoundoff64 = 1 / 2 ^ 53 := rfl
      refine ⟨fun hf hopen => ?_, fun h => ?_, BesselNSpecial.jn_nan p.1 p.2⟩
      · have h := BesselJnTheorem.jn_accuracy p.1 p.2 hf (by rw [hN]; exact hopen)
        rw [hN, hu] at h
        refine h.trans (le_of_eq ?_)
        unfold BesselRecur.modn
        ring
      · have h := BesselNSpecial.jn_infinity p.1 p.2 h
        rw [hN] at h
        exact h

set_option maxRecDepth 100000 in
/-- The export `yn`, called on a word `n` and a float `x`, with `N` the signed integer in the low 32
bits of `n`, returns for finite `x > 0`, a word below `2 ^ 63` other than 0, outside the range
`2 ≤ x < 2 ^ 302` with `x < 2 |N|`, either a finite float within
`(250 + 12 |N|) · 2 ^ -53 · M_|N|(x)` of `Y_N(x)`, where `M_k = √(J_k² + Y_k²)` is the modulus, so
that the bound is in units of the modulus, or, when `|Y_N(x)| > 2 ^ 1023`, the infinity of the sign
of `Y_N(x)`, which it returns when `|Y_N(x)| ≥ 2 ^ 1025`; it returns `+0` at `+∞` except `-0` for
`N = -1`, `-∞` at either zero, and the canonical NaN at a NaN and at a word with the sign bit set
other than `-0`. -/
theorem yn_master :
    Verified.Master compiled.module compiled.tables "yn" compiled.yn.bound (fun _ => True)
      (fun (p : UInt64 × Float) (r : Float) =>
        let N := Int.bmod p.1.toNat (2 ^ 32)
        (Finite p.2.toBits → p.2.toBits.toNat < 2 ^ 63 → p.2.toBits.toNat ≠ 0 →
          ¬ (2 ≤ value p.2.toBits ∧ value p.2.toBits < 2 ^ 302 ∧
            value p.2.toBits < 2 * (N.natAbs : ℝ)) →
          ((Finite r.toBits ∧
              |value r.toBits - YZ N (value p.2.toBits)| ≤
                (250 + 12 * (N.natAbs : ℝ)) / 2 ^ 53 *
                  √(Jn N.natAbs (value p.2.toBits) ^ 2 + Yn (value p.2.toBits) N.natAbs ^ 2)) ∨
            (r.toBits = Wasm.IEEE64.infinity (decide (YZ N (value p.2.toBits) < 0)) ∧
              2 ^ 1023 < |YZ N (value p.2.toBits)|)) ∧
          (2 ^ 1025 ≤ |YZ N (value p.2.toBits)| →
            r.toBits = Wasm.IEEE64.infinity (decide (YZ N (value p.2.toBits) < 0)))) ∧
        (p.2.toBits = 0x7FF0000000000000 →
          r.toBits = if N = -1 then 0x8000000000000000 else 0) ∧
        (p.2.toBits = 0 ∨ p.2.toBits = 0x8000000000000000 → r.toBits = 0xFFF0000000000000) ∧
        (Wasm.IEEE64.isNaN p.2.toBits = true ∨
            (Wasm.IEEE64.sign p.2.toBits = true ∧ p.2.toBits ≠ 0x8000000000000000) →
          r.toBits = Wasm.IEEE64.canonicalNaN)) :=
  .of_trapFree compiled.yn.trapFree (Verified.tables_at [0, 1, 4, 5, 2, 3] (by decide) rfl)
    BesselBytes.yn_export (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ p _ _ => by
      intro N
      have hN : BesselJnTheorem.orderZ p.1 = N := orderZ_eq p.1
      have hu : CodeLib.IEEE64.unitRoundoff64 = 1 / 2 ^ 53 := rfl
      refine ⟨fun hf hpos hnz hopen => ⟨?_, fun hbig => ?_⟩, fun h => ?_,
        BesselNSpecial.yn_zero p.1 p.2, fun h => ?_⟩
      · have h := BesselYnTheorem.yn_accuracy p.1 p.2 hf hpos hnz (by rw [hN]; exact hopen)
        rw [hN, hu] at h
        unfold BesselYnOrderOne.YBound at h
        rcases h with ⟨hrf, hb⟩ | h
        · refine Or.inl ⟨hrf, hb.trans (le_of_eq ?_)⟩
          unfold BesselRecur.modn
          ring
        · exact Or.inr h
      · have h := BesselYnTheorem.yn_overflow p.1 p.2 hf hpos hnz (by rw [hN]; exact hopen)
          (by rw [hN]; exact hbig)
        rw [hN] at h
        exact h
      · have h := BesselNSpecial.yn_pos_infinity p.1 p.2 h
        rw [hN] at h
        exact h
      · rcases h with h | ⟨hs, hz⟩
        · exact BesselNSpecial.yn_nan p.1 p.2 h
        · cases hn : Wasm.IEEE64.isNaN p.2.toBits
          · exact BesselNSpecial.yn_negative p.1 p.2 hs hz hn
          · exact BesselNSpecial.yn_nan p.1 p.2 hn

#print axioms orderZ_eq
#print axioms j0_master
#print axioms j1_master
#print axioms y0_master
#print axioms y1_master
#print axioms jn_master
#print axioms yn_master

end Library.Numerics.Float64.Bessel
