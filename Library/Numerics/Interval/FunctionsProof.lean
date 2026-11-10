import Library.Numerics.Interval.Functions
import Library.Numerics.Interval.Proof
import Library.Numerics.Float64.Trig.TrigSinCos
import LeanExe.ProofKit.Signed64Value
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
Soundness of the operations of `Functions.lean`.  `Encloses i x` states that the interval `i`
contains the real `x` when it is accepted.  Each `encloses_*` theorem derives the relation for a
result from the relation for the operands, so a proof about a chain of operations applies one
theorem for each operation and needs no case analysis on acceptance.
-/

namespace Library.Numerics.Interval

open LeanExe.ProofKit Library.Numerics.Bounds Library.Numerics.Float64
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

theorem encloses_sq {a : Interval} {x : ℝ} (ha : Encloses a x) : Encloses (sq a) (x * x) := by
  have h := encloses_mul (encloses_abs ha) (encloses_abs ha)
  rwa [abs_mul_abs_self] at h

/-! ### Constants -/

theorem encloses_ofInt {n : Int64} {q : ℝ} (hn : n.toInt.natAbs ≤ 2 ^ 53)
    (hq : (n.toInt : ℝ) = q) : Encloses (ofInt n) q := fun h => by
  unfold ofInt at h ⊢
  have hc := (point_sound h).2
  rwa [(Signed64Value.toFloat_exact n hn).2, hq] at hc

theorem encloses_ratio {n d : Int64} {q : ℝ} (hn : n.toInt.natAbs ≤ 2 ^ 53)
    (hd : d.toInt.natAbs ≤ 2 ^ 53) (hq : (n.toInt : ℝ) / (d.toInt : ℝ) = q) :
    Encloses (ratio n d) q := by
  have h := encloses_div (encloses_ofInt hn rfl) (encloses_ofInt hd rfl)
  rwa [hq] at h

/-- The form of `encloses_ofInt` for a literal: `m` is the integer of the word `n`. -/
theorem encloses_ofInt' {n : Int64} {m : ℤ} {q : ℝ} (hm : n.toInt = m)
    (hb : m.natAbs ≤ 2 ^ 53) (hq : (m : ℝ) = q) : Encloses (ofInt n) q :=
  encloses_ofInt (by rw [hm]; exact hb) (by rw [hm]; exact hq)

/-- The form of `encloses_ratio` for literals. -/
theorem encloses_ratio' {n d : Int64} {m k : ℤ} {q : ℝ} (hn : n.toInt = m) (hd : d.toInt = k)
    (hbn : m.natAbs ≤ 2 ^ 53) (hbd : k.natAbs ≤ 2 ^ 53) (hq : (m : ℝ) / (k : ℝ) = q) :
    Encloses (ratio n d) q :=
  encloses_ratio (by rw [hn]; exact hbn) (by rw [hd]; exact hbd) (by rw [hn, hd]; exact hq)

theorem one_bits : (1.0 : Float).toBits = 0x3FF0000000000000 := by decide +kernel

theorem one_value : Finite (1.0 : Float).toBits ∧ value (1.0 : Float).toBits = 1 := by
  have hs : Wasm.IEEE64.scaledValue 0x3FF0000000000000 = 2 ^ 1074 := by decide +kernel
  refine ⟨?_, ?_⟩
  · rw [one_bits]; unfold CodeLib.IEEE64.Finite; decide +kernel
  · simp only [one_bits, value, hs]; push_cast; norm_num

/-! ### Maximum and selection -/

theorem imax_sound {a b : Interval} (h : (imax a b).status = 0) :
    a.status = 0 ∧ b.status = 0 ∧
      ∀ x y, Contains a x → Contains b y → Contains (imax a b) (max x y) := by
  unfold imax at h ⊢
  by_cases hc : (a.status == 0 && b.status == 0) = true
  · simp only [hc, ite_true]
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    refine ⟨hc.1, hc.2, fun x y hx hy => ?_⟩
    obtain ⟨f1, v1⟩ := fmax_value hx.2.1 hy.2.1
    obtain ⟨f2, v2⟩ := fmax_value hx.2.2.1 hy.2.2.1
    exact ⟨rfl, f1, f2, by rw [v1]; exact max_le_max hx.2.2.2.1 hy.2.2.2.1,
      by rw [v2]; exact max_le_max hx.2.2.2.2 hy.2.2.2.2⟩
  · simp only [hc, Bool.false_eq_true, ite_false] at h
    exact absurd h (by decide)

theorem encloses_imax {a b : Interval} {x y : ℝ} (ha : Encloses a x) (hb : Encloses b y) :
    Encloses (imax a b) (max x y) := fun h => by
  obtain ⟨sa, sb, hc⟩ := imax_sound h
  exact hc x y (ha sa) (hb sb)

/-- An accepted selection takes the branch that the sign of every point of `c` selects. -/
theorem encloses_ifPos {c p q : Interval} {z x y : ℝ} (hc : Encloses c z) (hp : Encloses p x)
    (hq : Encloses q y) : Encloses (ifPos c p q) (if 0 < z then x else y) := by
  intro h
  unfold ifPos at h ⊢
  by_cases hs : (c.status == 0) = true
  · simp only [hs, ite_true] at h ⊢
    obtain ⟨-, fl, fh, h1, h2⟩ := hc (beq_iff_eq.mp hs)
    obtain ⟨z0, zv⟩ := zero_value
    by_cases hlo : 0 < c.lo
    · simp only [hlo, ite_true] at h ⊢
      have hv : 0 < value c.lo.toBits := by
        have := (lt_iff_value z0 fl).mp hlo
        rwa [zv] at this
      rw [ite_eq_left (lt_of_lt_of_le hv h1)]
      exact hp h
    · simp only [hlo, ite_false] at h ⊢
      by_cases hhi : c.hi ≤ 0
      · simp only [hhi, ite_true] at h ⊢
        have hv : value c.hi.toBits ≤ 0 := by
          have := (le_iff_value fh z0).mp hhi
          rwa [zv] at this
        rw [ite_eq_right (not_lt.mpr (h2.trans hv))]
        exact hq h
      · simp only [hhi, ite_false] at h
        exact absurd h (by decide)
  · simp only [hs, Bool.false_eq_true, ite_false] at h
    exact absurd h (by decide)

/-- The selection on `x < y`, computed from the sign of `b - a`. -/
theorem encloses_ifLt {a b p q : Interval} {x y u v : ℝ} (ha : Encloses a x) (hb : Encloses b y)
    (hp : Encloses p u) (hq : Encloses q v) :
    Encloses (ifPos (sub b a) p q) (if x < y then u else v) := by
  have h := encloses_ifPos (encloses_sub hb ha) hp hq
  simpa only [sub_pos] using h

/-- The relation of two pairs whose components are related. -/
@[reducible] def prodRel {α β α' β' : Type} (R : α → α' → Prop) (S : β → β' → Prop)
    (p : α × β) (q : α' × β') : Prop := R p.1 q.1 ∧ S p.2 q.2

/-! ### Functions with the Lipschitz constant 1 -/

theorem reach_sound {a : Interval} {m : Float} (h : (reach a m).status = 0) :
    Finite m.toBits ∧ Finite (reach a m).value.toBits ∧
      ∀ x, value a.lo.toBits ≤ x → x ≤ value a.hi.toBits →
        |x - value m.toBits| ≤ value (reach a m).value.toBits := by
  simp only [reach] at h ⊢
  by_cases hc : ((outSub true a.hi m).status == 0 && (outSub true m a.lo).status == 0) = true
  · simp only [hc, ite_true]
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨-, fm, su⟩ := outSub_accepted hc.1
    obtain ⟨-, -, sd⟩ := outSub_accepted hc.2
    obtain ⟨fu, bu⟩ := upper su
    obtain ⟨fd, bd⟩ := upper sd
    obtain ⟨f, v⟩ := fmax_value fu fd
    refine ⟨fm, f, fun x h1 h2 => ?_⟩
    rw [v, abs_le]
    constructor
    · linarith [le_max_right (value (outSub true a.hi m).value.toBits)
        (value (outSub true m a.lo).value.toBits)]
    · linarith [le_max_left (value (outSub true a.hi m).value.toBits)
        (value (outSub true m a.lo).value.toBits)]
  · simp only [hc, Bool.false_eq_true, ite_false] at h
    exact absurd h (by decide)

theorem lipschitz_sound {a : Interval} {m fm : Float} {f : ℝ → ℝ}
    (h : (lipschitz a m fm).status = 0) (hf : ∀ x y, |f x - f y| ≤ |x - y|)
    (hm : Finite m.toBits → F64SignedRounding.WithinSteps 1 (f (value m.toBits)) fm.toBits) :
    a.status = 0 ∧ ∀ x, Contains a x → Contains (lipschitz a m fm) (f x) := by
  simp only [lipschitz] at h ⊢
  by_cases hc : ((reach a m).status == 0 && (outward2 false fm).status == 0 &&
      (outward2 true fm).status == 0) = true
  · simp only [hc, ite_true] at h ⊢
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨hok, hl, hh, he⟩ := join_accepted h
    obtain ⟨fm', -, hr⟩ := reach_sound hc.1.1
    obtain ⟨-, wl⟩ := outward2_lower (hm fm') hc.1.2
    obtain ⟨-, wu⟩ := outward2_upper (hm fm') hc.2
    obtain ⟨-, -, sl⟩ := outSub_accepted hl
    obtain ⟨-, -, sh⟩ := outAdd_accepted hh
    obtain ⟨fl, bl⟩ := lower sl
    obtain ⟨fh, bh⟩ := upper sh
    refine ⟨beq_iff_eq.mp hok, fun x hx => ?_⟩
    rw [he]
    have hd := abs_le.mp ((hf x (value m.toBits)).trans (hr x hx.2.2.2.1 hx.2.2.2.2))
    exact ⟨rfl, fl, fh, by linarith [hd.1], by linarith [hd.2]⟩
  · simp only [hc, Bool.false_eq_true, ite_false] at h
    exact absurd h (by decide)

theorem unit_bounds : value (-1.0 : Float).toBits = -1 ∧ value (1.0 : Float).toBits = 1 :=
  ⟨by rw [(neg_value one_value.1).2, one_value.2], one_value.2⟩

theorem sinI_sound {a : Interval} (h : (sinI Trig.invPi Trig.halfPi a).status = 0) :
    a.status = 0 ∧ ∀ x, Contains a x → Contains (sinI Trig.invPi Trig.halfPi a) (Real.sin x) := by
  simp only [sinI] at h ⊢
  obtain ⟨hs, hc⟩ := clamp_sound h
  obtain ⟨sa, hl⟩ := lipschitz_sound hs Real.abs_sin_sub_sin_le
    (fun hm => Trig.TrigSinCos.sin_within (mid a) hm)
  refine ⟨sa, fun x hx => hc _ (hl x hx) ?_ ?_⟩
  · rw [unit_bounds.1]; exact Real.neg_one_le_sin x
  · rw [unit_bounds.2]; exact Real.sin_le_one x

theorem cosI_sound {a : Interval} (h : (cosI Trig.invPi Trig.halfPi a).status = 0) :
    a.status = 0 ∧ ∀ x, Contains a x → Contains (cosI Trig.invPi Trig.halfPi a) (Real.cos x) := by
  simp only [cosI] at h ⊢
  obtain ⟨hs, hc⟩ := clamp_sound h
  obtain ⟨sa, hl⟩ := lipschitz_sound hs Real.abs_cos_sub_cos_le
    (fun hm => Trig.TrigSinCos.cos_within (mid a) hm)
  refine ⟨sa, fun x hx => hc _ (hl x hx) ?_ ?_⟩
  · rw [unit_bounds.1]; exact Real.neg_one_le_cos x
  · rw [unit_bounds.2]; exact Real.cos_le_one x

theorem encloses_sinI {a : Interval} {x : ℝ} (ha : Encloses a x) :
    Encloses (sinI Trig.invPi Trig.halfPi a) (Real.sin x) := fun h => by
  obtain ⟨sa, hc⟩ := sinI_sound h
  exact hc x (ha sa)

theorem encloses_cosI {a : Interval} {x : ℝ} (ha : Encloses a x) :
    Encloses (cosI Trig.invPi Trig.halfPi a) (Real.cos x) := fun h => by
  obtain ⟨sa, hc⟩ := cosI_sound h
  exact hc x (ha sa)

/-! ### Powers -/

theorem outward4_finite {up : Bool} {g : Float} (h : (outward4 up g).status = 0) :
    Finite (outward4 up g).value.toBits := by
  simp only [outward4] at h ⊢
  by_cases he : ((outward2 up g).status == 0) = true
  · simp only [he, ite_true] at h ⊢
    obtain ⟨-, -, f, hv⟩ := outward2_bits h
    rw [hv]
    exact f
  · simp only [he, Bool.false_eq_true, ite_false] at h
    exact absurd h (by decide)

theorem cubeEnd_upper {g : Float} (h : (cubeEnd true g).status = 0)
    (hg : 0 < value g.toBits) : value g.toBits ^ 3 ≤ value (cubeEnd true g).value.toBits := by
  simp only [cubeEnd] at h ⊢
  by_cases hs : ((outMul true g g).status == 0) = true
  · simp only [hs, ite_true] at h ⊢
    obtain ⟨-, -, s1⟩ := outMul_accepted (beq_iff_eq.mp hs)
    obtain ⟨-, -, s2⟩ := outMul_accepted h
    obtain ⟨-, b1⟩ := upper s1
    obtain ⟨-, b2⟩ := upper s2
    nlinarith [mul_le_mul_of_nonneg_right b1 hg.le]
  · simp only [hs, Bool.false_eq_true, ite_false] at h
    exact absurd h (by decide)

theorem cubeEnd_lower {g : Float} (h : (cubeEnd false g).status = 0)
    (hg : 0 < value g.toBits) : value (cubeEnd false g).value.toBits ≤ value g.toBits ^ 3 := by
  simp only [cubeEnd] at h ⊢
  by_cases hs : ((outMul false g g).status == 0) = true
  · simp only [hs, ite_true] at h ⊢
    obtain ⟨-, -, s1⟩ := outMul_accepted (beq_iff_eq.mp hs)
    obtain ⟨-, -, s2⟩ := outMul_accepted h
    obtain ⟨-, b1⟩ := lower s1
    obtain ⟨-, b2⟩ := lower s2
    nlinarith [mul_le_mul_of_nonneg_right b1 hg.le]
  · simp only [hs, Bool.false_eq_true, ite_false] at h
    exact absurd h (by decide)

theorem cube_two_thirds {x : ℝ} (hx : 0 < x) : (x ^ (2 / 3 : ℝ)) ^ 3 = x ^ 2 := by
  have e : (2 / 3 : ℝ) * ((3 : ℕ) : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le, e, Real.rpow_natCast]

theorem le_two_thirds {g x : ℝ} (hg : 0 < g) (hx : 0 < x) (h : g ^ 3 ≤ x ^ 2) :
    g ≤ x ^ (2 / 3 : ℝ) := by
  rw [← cube_two_thirds hx] at h
  exact (pow_le_pow_iff_left₀ hg.le (Real.rpow_nonneg hx.le _) (by norm_num)).mp h

theorem two_thirds_le {g x : ℝ} (hg : 0 < g) (hx : 0 < x) (h : x ^ 2 ≤ g ^ 3) :
    x ^ (2 / 3 : ℝ) ≤ g := by
  rw [← cube_two_thirds hx] at h
  exact (pow_le_pow_iff_left₀ (Real.rpow_nonneg hx.le _) hg.le (by norm_num)).mp h

theorem twoThirds_sound {logTab expTab : Array UInt64} {a : Interval}
    (h : (twoThirds logTab expTab a).status = 0) :
    a.status = 0 ∧ ∀ x, Contains a x →
      0 < x ∧ Contains (twoThirds logTab expTab a) (x ^ (2 / 3 : ℝ)) := by
  simp only [twoThirds] at h ⊢
  obtain ⟨z0, zv⟩ := zero_value
  by_cases hs : (a.status == 0) = true
  · by_cases hlo : 0 < a.lo
    · simp only [hs, hlo, ite_true] at h ⊢
      generalize Pow.powWith logTab expTab a.lo (2.0 / 3.0) = pl at h ⊢
      generalize Pow.powWith logTab expTab a.hi (2.0 / 3.0) = ph at h ⊢
      by_cases hc : ((outward4 false pl).status == 0 && (outward4 true ph).status == 0 &&
          (cubeEnd true (outward4 false pl).value).status == 0 &&
          (outMul false a.lo a.lo).status == 0 &&
          (cubeEnd false (outward4 true ph).value).status == 0 &&
          (outMul true a.hi a.hi).status == 0) = true
      · by_cases hgl : 0 < (outward4 false pl).value
        · by_cases hgh : 0 < (outward4 true ph).value
          · by_cases h1 : (cubeEnd true (outward4 false pl).value).value ≤
                (outMul false a.lo a.lo).value
            · by_cases h2 : (outMul true a.hi a.hi).value ≤
                  (cubeEnd false (outward4 true ph).value).value
              · simp only [hc, hgl, hgh, h1, h2, ite_true]
                simp only [Bool.and_eq_true, beq_iff_eq] at hc
                obtain ⟨⟨⟨⟨⟨sgl, sgh⟩, scl⟩, ssl⟩, sch⟩, ssh⟩ := hc
                have fgl := outward4_finite sgl
                have fgh := outward4_finite sgh
                obtain ⟨fa, -, s1⟩ := outMul_accepted ssl
                obtain ⟨fb, -, s2⟩ := outMul_accepted ssh
                obtain ⟨fsl, bsl⟩ := lower s1
                obtain ⟨fsh, bsh⟩ := upper s2
                have vgl : 0 < value (outward4 false pl).value.toBits := by
                  have := (lt_iff_value z0 fgl).mp hgl
                  rwa [zv] at this
                have vgh : 0 < value (outward4 true ph).value.toBits := by
                  have := (lt_iff_value z0 fgh).mp hgh
                  rwa [zv] at this
                have vlo : 0 < value a.lo.toBits := by
                  have := (lt_iff_value z0 fa).mp hlo
                  rwa [zv] at this
                have cu := cubeEnd_upper scl vgl
                have cd := cubeEnd_lower sch vgh
                have fcl : Finite (cubeEnd true (outward4 false pl).value).value.toBits := by
                  simp only [cubeEnd] at scl ⊢
                  by_cases hq : ((outMul true (outward4 false pl).value
                      (outward4 false pl).value).status == 0) = true
                  · simp only [hq, ite_true] at scl ⊢
                    exact (upper (outMul_accepted scl).2.2).1
                  · simp only [hq, Bool.false_eq_true, ite_false] at scl
                    exact absurd scl (by decide)
                have fch : Finite (cubeEnd false (outward4 true ph).value).value.toBits := by
                  simp only [cubeEnd] at sch ⊢
                  by_cases hq : ((outMul false (outward4 true ph).value
                      (outward4 true ph).value).status == 0) = true
                  · simp only [hq, ite_true] at sch ⊢
                    exact (lower (outMul_accepted sch).2.2).1
                  · simp only [hq, Bool.false_eq_true, ite_false] at sch
                    exact absurd sch (by decide)
                have v1 := (le_iff_value fcl fsl).mp h1
                have v2 := (le_iff_value fsh fch).mp h2
                refine ⟨beq_iff_eq.mp hs, fun x hx => ?_⟩
                obtain ⟨-, -, -, x1, x2⟩ := hx
                have xp : 0 < x := lt_of_lt_of_le vlo x1
                refine ⟨xp, rfl, fgl, fgh, le_two_thirds vgl xp ?_, two_thirds_le vgh xp ?_⟩
                · nlinarith [mul_le_mul x1 x1 vlo.le xp.le]
                · nlinarith [mul_le_mul x2 x2 xp.le (xp.le.trans x2)]
              · simp only [hc, hgl, hgh, h1, h2, ite_true, ite_false] at h
                exact absurd h (by decide)
            · simp only [hc, hgl, hgh, h1, ite_true, ite_false] at h
              exact absurd h (by decide)
          · simp only [hc, hgl, hgh, ite_true, ite_false] at h
            exact absurd h (by decide)
        · simp only [hc, hgl, ite_true, ite_false] at h
          exact absurd h (by decide)
      · simp only [hc, Bool.false_eq_true, ite_false] at h
        exact absurd h (by decide)
    · simp only [hs, hlo, ite_true, ite_false] at h
      exact absurd h (by decide)
  · simp only [hs, Bool.false_eq_true, ite_false] at h
    exact absurd h (by decide)

theorem encloses_twoThirds {logTab expTab : Array UInt64} {a : Interval} {x : ℝ}
    (ha : Encloses a x) : Encloses (twoThirds logTab expTab a) (x ^ (2 / 3 : ℝ)) := fun h => by
  obtain ⟨sa, hc⟩ := twoThirds_sound h
  exact (hc x (ha sa)).2

theorem rpow_three_halves {x : ℝ} (hx : 0 ≤ x) : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  have e : (3 / 2 : ℝ) = 1 + 1 / 2 := by norm_num
  rw [e, Real.rpow_add' hx (by norm_num), Real.rpow_one, ← Real.sqrt_eq_rpow]

theorem rpow_seven_halves {x : ℝ} (hx : 0 ≤ x) :
    x ^ (7 / 2 : ℝ) = x * x * x * Real.sqrt x := by
  have e : (7 / 2 : ℝ) = ((3 : ℕ) : ℝ) + 1 / 2 := by norm_num
  rw [e, Real.rpow_add' hx (by norm_num), Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  ring

theorem encloses_threeHalves {a : Interval} {x : ℝ} (ha : Encloses a x) :
    Encloses (threeHalves a) (x ^ (3 / 2 : ℝ)) := fun h => by
  unfold threeHalves at h ⊢
  obtain ⟨sa, ss, hc⟩ := mul_sound h
  obtain ⟨-, hq⟩ := sqrt_sound ss
  obtain ⟨x0, cs⟩ := hq x (ha sa)
  rw [rpow_three_halves x0]
  exact hc x _ (ha sa) cs

theorem encloses_sevenHalves {a : Interval} {x : ℝ} (ha : Encloses a x) :
    Encloses (sevenHalves a) (x ^ (7 / 2 : ℝ)) := fun h => by
  unfold sevenHalves at h ⊢
  obtain ⟨sp, ss, hc⟩ := mul_sound h
  obtain ⟨sa, hq⟩ := sqrt_sound ss
  obtain ⟨x0, cs⟩ := hq x (ha sa)
  obtain ⟨s2, -, hc3⟩ := mul_sound sp
  obtain ⟨-, -, hc2⟩ := mul_sound s2
  rw [rpow_seven_halves x0]
  exact hc _ _ (hc3 _ _ (hc2 x x (ha sa) (ha sa)) (ha sa)) cs

end Library.Numerics.Interval
