import Library.Numerics.Float64.Tgamma.TgammaLogdCheck
import Library.Numerics.Float64.Tgamma.TgammaFloor
import LeanExe.ProofKit.F64ExactProduct
import LeanExe.ProofKit.F64Convert
import LeanExe.ProofKit.F64GridExact
import LeanExe.ProofKit.F64Exact

/-!
The word checks of `Tgamma.logdTable` and the exact operations that `Tgamma.asLogd` uses.  `tabOK`
checks that each reduction factor `r1` has the exponent field 1022 or 1023 and its low 36 bits zero,
and each `r2` the same with its low 35 bits zero, so that `r1 r2` has at most 35 significant bits.
It also checks that the high parts of the tables of `-log r1` and `-log r2` are multiples of
`2^-34` below `0.6932` and `0.021` in magnitude and that their low parts are below `2^-35`.  `ltOK`
checks, for the exponents -1, 0, and 1, that every sum `l1h + l2h + E ln2h` is zero or at least
`1/1475` in magnitude.  The kernel evaluates both checks for `logdTable`.  `add_exact`,
`fadd_exact`, and `fsub_exact` show a sum or difference exact when a finite word holds its exact
value, and `grid_word` gives that word for each multiple of `2^-34` up to `2^19`.
-/

namespace Library.Numerics.Float64.Tgamma.TgammaLogdTab
open CodeLib.IEEE64 LeanExe.ProofKit TgammaFloor

set_option exponentiation.threshold 4096

/-! ### Word checks -/

def sv (w : UInt64) : ℤ := Wasm.IEEE64.scaledValue w

/-- A reduction factor: exponent `1022` or `1023` and the low `k` bits zero. -/
def rWord (k : ℕ) (w : UInt64) : Bool :=
  decide (w.toNat / 2 ^ 52 = 1022 ∨ w.toNat / 2 ^ 52 = 1023) && decide (w.toNat % 2 ^ k = 0)

/-- A finite word on the grid of `2^-34` below `B 2^-1074` in magnitude. -/
def hiWord (B : ℤ) (w : UInt64) : Bool :=
  decide (w.toNat % 2 ^ 63 < 0x7FF0000000000000) && decide (sv w % 2 ^ 1040 = 0) &&
    decide (|sv w| ≤ B)

/-- A finite word below `2^-35` in magnitude. -/
def loWord (w : UInt64) : Bool :=
  decide (w.toNat % 2 ^ 63 < 0x7FF0000000000000) && decide (|sv w| ≤ 2 ^ 1039)

/-- `lt` on the grid of `2^-34`, for the exponents `-1`, `0`, `1`: zero or at least `1/1475`. -/
def ltWord (h1 h2 : UInt64) (E : ℤ) : Bool :=
  let z := sv h1 / 2 ^ 1040 + sv h2 / 2 ^ 1040 + E * (sv 0x3FE62E42FEF80000 / 2 ^ 1040)
  decide (z = 0 ∨ 2 ^ 34 ≤ 1475 * |z|)

def tabOK (tab : Array UInt64) : Bool :=
  (List.range 33).all (fun i => rWord 36 tab[64 + i]!) &&
    (List.range 32).all (fun i => rWord 35 tab[97 + i]!) &&
    (List.range 33).all (fun i => hiWord (6932 * 2 ^ 1074 / 10000) tab[131 + 2 * i]!) &&
    (List.range 32).all (fun i => hiWord (21 * 2 ^ 1074 / 1000) tab[197 + 2 * i]!) &&
    (List.range 33).all (fun i => loWord tab[130 + 2 * i]!) &&
    (List.range 32).all (fun i => loWord tab[196 + 2 * i]!)

def ltOK (tab : Array UInt64) (E : ℤ) : Bool :=
  (List.range 33).all fun a => (List.range 32).all fun b => ltWord tab[131 + 2 * a]! tab[197 + 2 * b]! E

theorem tabOK_logd : tabOK Tgamma.logdTable = true := by decide +kernel
theorem ltOK_m1 : ltOK Tgamma.logdTable (-1) = true := by decide +kernel
theorem ltOK_0 : ltOK Tgamma.logdTable 0 = true := by decide +kernel
theorem ltOK_1 : ltOK Tgamma.logdTable 1 = true := by decide +kernel

/-! ### Exact operations -/

theorem value_eq (w : UInt64) : value w = (sv w : ℝ) / 2 ^ 1074 := rfl

theorem mag_eq_natAbs (w : UInt64) : Wasm.IEEE64.scaledMagnitude w = (sv w).natAbs := by
  unfold sv Wasm.IEEE64.scaledValue
  split <;> simp

/-- The value of a rounded word equals its exact value when a word holds that value. -/
theorem rounded_exact (c w : UInt64) (S : ℝ) (hc : F64RoundNearest.Rounded c S)
    (hw : value w = S) : value c = S := by
  have h := hc.2.2.2 w
  rw [hw, sub_self, abs_zero] at h
  have habs : |value c| = |S| := by
    have := abs_nonpos_iff.mp h; linarith
  rcases lt_trichotomy S 0 with hS | hS | hS
  · have := F64TwoSum.value_nonpos_of_sign c (hc.2.1 hS)
    rw [abs_of_nonpos this, abs_of_neg hS] at habs; linarith
  · rw [hS, abs_zero] at habs; rw [hS]; exact abs_eq_zero.mp habs
  · have := F64TwoSum.value_nonneg_of_sign c (hc.2.2.1 hS)
    rw [abs_of_nonneg this, abs_of_pos hS] at habs; exact habs

/-- A sum whose exact value a finite word holds is exact. -/
theorem add_exact (a b w : UInt64) (ha : Finite a) (hb : Finite b) (_hw : Finite w)
    (hv : value w = value a + value b) (hlim : |value a + value b| < 2 ^ 1023) :
    Finite (Wasm.IEEE64.add a b) ∧ value (Wasm.IEEE64.add a b) = value a + value b := by
  by_cases h0 : value a + value b = 0
  · have hs : Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b = 0 * 2 ^ 0 := by
      have h1 : ((Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b : ℤ) : ℝ) = 0 := by
        rw [Int.cast_add]
        have := h0; rw [value_eq, value_eq, ← add_div, div_eq_zero_iff] at this
        rcases this with h | h
        · exact h
        · exact absurd h (by positivity)
      have h2 : Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b = 0 := by exact_mod_cast h1
      rw [h2]; ring
    obtain ⟨hf, hv'⟩ := F64GridExact.grid_add_exact a b ha hb 0 0 hs (by norm_num) (by norm_num)
    refine ⟨hf, ?_⟩
    rw [h0, value, hv']
    have : ((Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b : ℤ) : ℝ) = 0 := by
      rw [hs]; simp
    rw [this]; simp
  · have hR := F64RoundNearest.add_rounded a b ha hb h0 hlim
    exact ⟨hR.1, rounded_exact _ w _ hR hv⟩

theorem fadd_exact (a b w : Float) (ha : Finite a.toBits) (hb : Finite b.toBits)
    (hw : Finite w.toBits) (hv : value w.toBits = value a.toBits + value b.toBits)
    (hlim : |value a.toBits + value b.toBits| < 2 ^ 1023) :
    Finite (a + b).toBits ∧ value (a + b).toBits = value a.toBits + value b.toBits := by
  rw [F64Bits.toBits_add]; exact add_exact _ _ _ ha hb hw hv hlim

theorem fsub_exact (a b w : Float) (ha : Finite a.toBits) (hb : Finite b.toBits)
    (hw : Finite w.toBits) (hv : value w.toBits = value a.toBits - value b.toBits)
    (hlim : |value a.toBits - value b.toBits| < 2 ^ 1023) :
    Finite (a - b).toBits ∧ value (a - b).toBits = value a.toBits - value b.toBits := by
  rw [F64Bits.toBits_sub]
  obtain ⟨hnf, hnv⟩ := F64Magnitude.negate_value b.toBits hb
  have h := add_exact a.toBits (Wasm.IEEE64.negate b.toBits) w.toBits ha hnf hw
    (by rw [hnv, hv]; ring) (by rw [hnv, ← sub_eq_add_neg]; exact hlim)
  rw [hnv, ← sub_eq_add_neg] at h
  exact h

/-- A finite word for each multiple of `2^-34` below `2^19`. -/
theorem grid_word (z : ℤ) (hz : z.natAbs ≤ 2 ^ 53) :
    ∃ w : Float, Finite w.toBits ∧ value w.toBits = z / 2 ^ 34 := by
  obtain ⟨hf, hv⟩ := F64GridExact.signed_grid_packing_exact z 1040 hz (by norm_num)
  refine ⟨Float.ofBits (Wasm.IEEE64.roundScaledMagnitude (decide (z < 0)) (z.natAbs * 2 ^ 1040)),
    ?_, ?_⟩
  · rw [F64Bits.toBits_ofBits, not_nan_of_finite hf]
    simp only [Bool.false_eq_true, ite_false]
    exact hf
  · rw [F64Bits.toBits_ofBits, not_nan_of_finite hf]
    simp only [Bool.false_eq_true, ite_false]
    rewrite [value, hv, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
      div_eq_div_iff (by positivity) (by positivity), mul_assoc, ← pow_add]
    norm_num

/-- A double of an integer below `2^53`. -/
theorem toFloat_value (n : UInt64) (hn : n.toNat ≤ 2 ^ 53) :
    Finite n.toFloat.toBits ∧ sv n.toFloat.toBits = n.toNat * 2 ^ 1074 := by
  rw [F64Convert.toBits_toFloat]
  unfold Wasm.IEEE64.convertI64U Wasm.IEEE64.fromInt
  exact F64GridExact.signed_grid_packing_exact (n.toNat : ℤ) 1074 (by simpa using hn) (by norm_num)

#print axioms add_exact
#print axioms grid_word
#print axioms toFloat_value

#print axioms tabOK_logd
#print axioms ltOK_m1

end Library.Numerics.Float64.Tgamma.TgammaLogdTab
