module

public import Library.Numerics.Interval.Proof

@[expose] public section

/-!
`Encloses i x` states that the interval `i` contains the real `x` when it is accepted.  Each
`encloses_*` theorem derives the relation for the result of an operation of `Program.lean` from
the relation for its operands, and the `Contains` lemmas turn a comparison of an endpoint with 0 or
1 into a bound on every point.  The module imports no trigonometric module, so a proof that states
arithmetic enclosures does not depend on the trigonometric library.
-/

namespace Library.Numerics.Interval

open LeanExe.ProofKit Library.Numerics.Bounds
open CodeLib.IEEE64 (value Finite)

set_option exponentiation.threshold 4096

/-- The interval `i` contains `x` when it is accepted. -/
def Encloses (i : Interval) (x : ℝ) : Prop := i.status = 0 → Contains i x

/-! ### Arithmetic -/

theorem encloses_add {a b : Interval} {x y : ℝ} (ha : Encloses a x) (hb : Encloses b y) :
    Encloses (add a b) (x + y) := fun h => by
  obtain ⟨sa, sb, hc⟩ := add_sound h
  exact hc x y (ha sa) (hb sb)

theorem encloses_sub {a b : Interval} {x y : ℝ} (ha : Encloses a x) (hb : Encloses b y) :
    Encloses (sub a b) (x - y) := fun h => by
  obtain ⟨sa, sb, hc⟩ := sub_sound h
  exact hc x y (ha sa) (hb sb)

theorem encloses_mul {a b : Interval} {x y : ℝ} (ha : Encloses a x) (hb : Encloses b y) :
    Encloses (mul a b) (x * y) := fun h => by
  obtain ⟨sa, sb, hc⟩ := mul_sound h
  exact hc x y (ha sa) (hb sb)

theorem encloses_div {a b : Interval} {x y : ℝ} (ha : Encloses a x) (hb : Encloses b y) :
    Encloses (div a b) (x / y) := fun h => by
  obtain ⟨sa, sb, hc⟩ := div_sound h
  exact (hc x y (ha sa) (hb sb)).2

theorem encloses_neg {a : Interval} {x : ℝ} (ha : Encloses a x) : Encloses (neg a) (-x) :=
  fun h => by
    obtain ⟨sa, hc⟩ := neg_sound h
    exact hc x (ha sa)

theorem encloses_abs {a : Interval} {x : ℝ} (ha : Encloses a x) : Encloses (abs a) |x| :=
  fun h => by
    obtain ⟨sa, hc⟩ := abs_sound h
    exact hc x (ha sa)

theorem encloses_sqrt {a : Interval} {x : ℝ} (ha : Encloses a x) :
    Encloses (sqrt a) (Real.sqrt x) := fun h => by
  obtain ⟨sa, hc⟩ := sqrt_sound h
  exact (hc x (ha sa)).2

/-! ### Literals -/

theorem zero_lit_bits : (0.0 : Float).toBits = 0 := by decide +kernel

theorem zero_lit_value : Finite (0.0 : Float).toBits ∧ value (0.0 : Float).toBits = 0 := by
  have hs : Wasm.IEEE64.scaledValue 0 = 0 := by decide +kernel
  refine ⟨?_, ?_⟩
  · rw [zero_lit_bits]; unfold CodeLib.IEEE64.Finite; decide +kernel
  · simp only [zero_lit_bits, value, hs]; norm_num

theorem one_bits : (1.0 : Float).toBits = 0x3FF0000000000000 := by decide +kernel

theorem one_value : Finite (1.0 : Float).toBits ∧ value (1.0 : Float).toBits = 1 := by
  have hs : Wasm.IEEE64.scaledValue 0x3FF0000000000000 = 2 ^ 1074 := by decide +kernel
  refine ⟨?_, ?_⟩
  · rw [one_bits]; unfold CodeLib.IEEE64.Finite; decide +kernel
  · simp only [one_bits, value, hs]; push_cast; norm_num

/-! ### Signs of the points of an interval -/

theorem Contains.pos_of_lo {i : Interval} {x : ℝ} (c : Contains i x) (h : 0 < i.lo) : 0 < x := by
  obtain ⟨z0, zv⟩ := zero_value
  have := (lt_iff_value z0 c.2.1).mp h
  rw [zv] at this
  exact lt_of_lt_of_le this c.2.2.2.1

theorem Contains.nonneg_of_lo {i : Interval} {x : ℝ} (c : Contains i x) (h : 0 ≤ i.lo) :
    0 ≤ x := by
  obtain ⟨z0, zv⟩ := zero_value
  have := (le_iff_value z0 c.2.1).mp h
  rw [zv] at this
  exact this.trans c.2.2.2.1

theorem Contains.neg_of_hi {i : Interval} {x : ℝ} (c : Contains i x) (h : i.hi < 0) : x < 0 := by
  obtain ⟨z0, zv⟩ := zero_value
  have := (lt_iff_value c.2.2.1 z0).mp h
  rw [zv] at this
  exact lt_of_le_of_lt c.2.2.2.2 this

theorem Contains.nonpos_of_hi {i : Interval} {x : ℝ} (c : Contains i x) (h : i.hi ≤ 0) :
    x ≤ 0 := by
  obtain ⟨z0, zv⟩ := zero_value
  have := (le_iff_value c.2.2.1 z0).mp h
  rw [zv] at this
  exact c.2.2.2.2.trans this

theorem Contains.lt_one_of_hi {i : Interval} {x : ℝ} (c : Contains i x) (h : i.hi < 1.0) :
    x < 1 := by
  have := (lt_iff_value c.2.2.1 one_value.1).mp h
  rw [one_value.2] at this
  exact lt_of_le_of_lt c.2.2.2.2 this

theorem Contains.one_le_of_lo {i : Interval} {x : ℝ} (c : Contains i x) (h : 1.0 ≤ i.lo) :
    1 ≤ x := by
  have := (le_iff_value one_value.1 c.2.1).mp h
  rw [one_value.2] at this
  exact this.trans c.2.2.2.1

end Library.Numerics.Interval
