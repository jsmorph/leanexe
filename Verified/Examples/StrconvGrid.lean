import Verified.Examples.FmaGrid

/-!
The grid of a binary format with precision `p` and infinity exponent field `F`, in units of the
least subnormal: 53 and 2047 for binary64 (units `2 ^ -1074`), 24 and 255 for binary32 (units
`2 ^ -149`).  `mag f n` is the magnitude of the finite nonnegative encoding `n < limit f`, so that
`mag` of a word's encoding is Talos's `scaledMagnitude`.  The doubles of exponent field `E ≥ 1`
are spaced `2 ^ (E - 1)` units apart, the subnormal ones with `E = 1`.

`RoundsTo f y E Q` states that the real `y ≥ 0`, in units, lies in binade `E` and that `Q` is the
integer nearest to `y / 2 ^ (E - 1)`, the even one at a tie; it generalizes `FmaGrid.RoundsTo`
from naturals in units of `2 ^ -2400` to reals and to any format.  `nearest_even_pack` proves that
the encoding `(E - 1) · 2 ^ (p - 1) + Q` is then nearest to `y` with the even choice at a tie,
following `FmaNearestEven.nearest_even`: every encoding at or above the start of the binade is a
multiple of the spacing (`mag_dvd`), and every one below lies at least half a spacing below the
start (`mag_below`).  `nearest_even_unique` shows that two nearest encodings differ by at most one,
so the even one is unique.  `exists_roundsTo` gives `E` and `Q` for every `y ≥ 0`, and
`positive_reference` evaluates the reference `refPos`, which is `limit f`, the encoding of
infinity, from the overflow threshold `(2 ^ (p + 1) - 1) · 2 ^ (F - 3)` on.  `FmaGrid` and
`FmaNearestEven` could become instances of this module.
-/

namespace Verified.Examples.StrconvGrid

set_option exponentiation.threshold 4096

/-- A binary format: the precision `p` and the exponent field `F` of the infinities. -/
structure Fmt where
  p : ℕ
  F : ℕ
  hp : 2 ≤ p
  hF : 3 ≤ F

def b64 : Fmt := ⟨53, 2047, by norm_num, by norm_num⟩
def b32 : Fmt := ⟨24, 255, by norm_num, by norm_num⟩

variable (f : Fmt)

/-- `2 ^ (p - 1)`, the least normal significand. -/
def half : ℕ := 2 ^ (f.p - 1)

/-- The magnitude of the finite nonnegative encoding `n`, in units of the least subnormal. -/
def mag (n : ℕ) : ℕ :=
  if n < half f then n else (half f + n % half f) * 2 ^ (n / half f - 1)

/-- The encoding of positive infinity, past every finite nonnegative encoding. -/
def limit : ℕ := f.F * half f

/-- The encoding of significand `Q` in binade `E`. -/
def pack (E Q : ℕ) : ℕ := (E - 1) * half f + Q

/-- The overflow threshold in units, halfway between the largest finite value
`(2 ^ p - 1) · 2 ^ (F - 2)` and `2 ^ p · 2 ^ (F - 2)`. -/
noncomputable def threshold : ℝ := (2 ^ (f.p + 1) - 1) * (2 : ℝ) ^ (f.F - 3)

def Nearest (y : ℝ) (n : ℕ) : Prop :=
  n < limit f ∧ ∀ m, m < limit f → |(mag f n : ℝ) - y| ≤ |(mag f m : ℝ) - y|

def NearestEven (y : ℝ) (n : ℕ) : Prop :=
  Nearest f y n ∧ ∀ m, Nearest f y m → n % 2 ≤ m % 2

/-- `y` lies in binade `E`, and `Q` is the integer nearest to `y / 2 ^ (E - 1)`, even at a tie. -/
def RoundsTo (y : ℝ) (E Q : ℕ) : Prop :=
  1 ≤ E ∧ y < (2 : ℝ) ^ f.p * 2 ^ (E - 1) ∧
    (E = 1 ∨ (2 : ℝ) ^ (f.p - 1) * 2 ^ (E - 1) ≤ y) ∧
    2 * y ≤ (2 * Q + 1) * (2 : ℝ) ^ (E - 1) ∧ 2 * Q * (2 : ℝ) ^ (E - 1) ≤ 2 * y + 2 ^ (E - 1) ∧
    (2 * y = (2 * Q + 1) * (2 : ℝ) ^ (E - 1) ∨ 2 * y + 2 ^ (E - 1) = 2 * Q * (2 : ℝ) ^ (E - 1) →
      Q % 2 = 0)

theorem half_pos : 0 < half f := by unfold half; positivity

theorem half_even : half f % 2 = 0 := by
  unfold half
  obtain ⟨k, hk⟩ : ∃ k, f.p - 1 = k + 1 := ⟨f.p - 2, by have := f.hp; omega⟩
  rw [hk, pow_succ]; simp

theorem two_half : 2 * half f = 2 ^ f.p := by
  unfold half
  rw [← pow_succ']
  congr 1
  have := f.hp; omega

/-! ### Magnitudes -/

theorem mag_succ (n : ℕ) : mag f (n + 1) = mag f n + 2 ^ (n / half f - 1) := by
  have hB := half_pos f
  have hq : n / half f * half f + n % half f = n := Nat.div_add_mod' n (half f)
  have hr := Nat.mod_lt n hB
  unfold mag
  by_cases h1 : n + 1 < half f
  · have h0 : n < half f := by omega
    have hd : n / half f = 0 := Nat.div_eq_of_lt h0
    rw [if_pos h1, if_pos h0, hd]
    simp
  · rw [if_neg h1]
    by_cases h0 : n < half f
    · have hn : n + 1 = half f := by omega
      rw [if_pos h0, hn, Nat.mod_self, Nat.div_self hB, Nat.div_eq_of_lt h0]
      simp only [add_zero, Nat.sub_self, pow_zero, mul_one]
      omega
    · rw [if_neg h0]
      have hpos : 1 ≤ n / half f := (Nat.le_div_iff_mul_le hB).mpr (by omega)
      by_cases hm : n % half f + 1 < half f
      · have hn1 : n + 1 = (n % half f + 1) + n / half f * half f := by omega
        have e1 : (n + 1) / half f = n / half f := by
          rw [hn1, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hm, zero_add]
        have e2 : (n + 1) % half f = n % half f + 1 := by
          rw [hn1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hm]
        rw [e1, e2]
        ring
      · have hm' : n % half f + 1 = half f := by omega
        have hn1 : n + 1 = (n / half f + 1) * half f := by
          rw [Nat.add_mul, one_mul]; omega
        have e1 : (n + 1) / half f = n / half f + 1 := by
          rw [hn1, Nat.mul_div_cancel _ hB]
        have e2 : (n + 1) % half f = 0 := by
          rw [hn1, Nat.mul_mod_left]
        obtain ⟨k, hk⟩ : ∃ k, n / half f = k + 1 := ⟨n / half f - 1, by omega⟩
        rw [e1, e2, hk, show k + 1 + 1 - 1 = k + 1 by omega, show k + 1 - 1 = k by omega,
          pow_succ]
        have h3 : half f + n % half f + 1 = 2 * half f := by omega
        have h2 : (half f + n % half f) * 2 ^ k + 2 ^ k = (half f + n % half f + 1) * 2 ^ k := by
          ring
        rw [h2, h3]
        ring

theorem mag_lt_succ (n : ℕ) : mag f n < mag f (n + 1) := by
  rw [mag_succ]; have := Nat.two_pow_pos (n / half f - 1); omega

theorem mag_strict {m n : ℕ} (h : m < n) : mag f m < mag f n := by
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
    · exact (ih h').trans (mag_lt_succ f k)
    · rw [h']; exact mag_lt_succ f k

theorem mag_le_iff {m n : ℕ} : mag f m ≤ mag f n ↔ m ≤ n := by
  constructor
  · intro h; by_contra h'; exact absurd h (not_le.mpr (mag_strict f (not_le.mp h')))
  · intro h
    rcases Nat.lt_or_eq_of_le h with h' | h'
    · exact (mag_strict f h').le
    · rw [h']

theorem mag_inj {m n : ℕ} (h : mag f m = mag f n) : m = n :=
  le_antisymm ((mag_le_iff f).mp h.le) ((mag_le_iff f).mp h.ge)

/-- The magnitude of the significand `Q` in binade `E`. -/
theorem mag_pack (E Q : ℕ) (hE : 1 ≤ E) (hQ : Q ≤ 2 * half f) (hQ1 : E = 1 ∨ half f ≤ Q) :
    mag f (pack f E Q) = Q * 2 ^ (E - 1) := by
  have hB := half_pos f
  obtain ⟨k, rfl⟩ : ∃ k, E = k + 1 := ⟨E - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hQ1 ⊢
  unfold mag pack
  simp only [Nat.add_sub_cancel]
  by_cases h1 : k * half f + Q < half f
  · rw [if_pos h1]
    have hk : k = 0 := by
      rcases hQ1 with h | h
      · omega
      · by_contra hk
        have : half f ≤ k * half f := Nat.le_mul_of_pos_left _ (by omega)
        omega
    subst hk; simp
  · rw [if_neg h1]
    have hQB : half f ≤ Q := by
      rcases hQ1 with h | h
      · have hk : k = 0 := by omega
        subst hk; simp at h1; exact h1
      · exact h
    by_cases h2 : Q < 2 * half f
    · have hn1 : k * half f + Q = (Q - half f) + (k + 1) * half f := by
        rw [Nat.add_mul, one_mul]; omega
      have hd : (k * half f + Q) / half f = k + 1 := by
        rw [hn1, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt (by omega), zero_add]
      have hm : (k * half f + Q) % half f = Q - half f := by
        rw [hn1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      rw [hd, hm, Nat.add_sub_cancel]
      congr 1; omega
    · have hQe : Q = 2 * half f := by omega
      subst hQe
      have hn1 : k * half f + 2 * half f = (k + 2) * half f := by ring
      rw [hn1, Nat.mul_div_cancel _ hB, Nat.mul_mod_left,
        show k + 2 - 1 = k + 1 by omega, pow_succ]
      ring

/-- The start of binade `E`. -/
theorem mag_start (E : ℕ) (hE : 1 ≤ E) : mag f (E * half f) = half f * 2 ^ (E - 1) := by
  have := mag_pack f E (half f) hE (by omega) (Or.inr le_rfl)
  rw [pack, show (E - 1) * half f + half f = E * half f by
    rw [show E = (E - 1) + 1 by omega, Nat.add_mul, one_mul]; simp] at this
  exact this

/-- At or above the start of binade `E`, a magnitude is a multiple of the spacing. -/
theorem mag_dvd (E n : ℕ) (hE : 1 ≤ E) (h : E * half f ≤ n) : 2 ^ (E - 1) ∣ mag f n := by
  have hB := half_pos f
  unfold mag
  have hn : ¬ n < half f := by
    have : half f ≤ E * half f := Nat.le_mul_of_pos_left _ (by omega)
    omega
  rw [if_neg hn]
  have hq : E ≤ n / half f := (Nat.le_div_iff_mul_le hB).mpr h
  apply Dvd.dvd.mul_left
  exact Nat.pow_dvd_pow 2 (by omega)

/-- Below the start of a normal binade `E ≥ 2`, a magnitude lies at least half a spacing below the
start. -/
theorem mag_below (E n : ℕ) (hE : 2 ≤ E) (h : n < E * half f) :
    mag f n + 2 ^ (E - 2) ≤ half f * 2 ^ (E - 1) := by
  have hB := half_pos f
  have hs := mag_succ f (E * half f - 1)
  have h1 : E * half f - 1 + 1 = E * half f := by
    have : half f ≤ E * half f := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have h2 : (E * half f - 1) / half f = E - 1 := by
    apply Nat.div_eq_of_lt_le
    · rw [Nat.sub_mul, one_mul]
      have : half f ≤ E * half f := Nat.le_mul_of_pos_left _ (by omega)
      omega
    · rw [show E - 1 + 1 = E by omega]; omega
  rw [h1, h2, mag_start f E (by omega), show E - 1 - 1 = E - 2 by omega] at hs
  have hle : mag f n ≤ mag f (E * half f - 1) := (mag_le_iff f).mpr (by omega)
  omega

/-! ### Rounding to the grid -/

/-- The significand of a rounding lies in `[2 ^ (p - 1), 2 ^ p]` in a normal binade. -/
theorem significand_bounds (y : ℝ) (E Q : ℕ) (h : RoundsTo f y E Q) :
    Q ≤ 2 * half f ∧ (E = 1 ∨ half f ≤ Q) := by
  obtain ⟨_, hy1, hy2, hr1, hr2, _⟩ := h
  have hS : (0 : ℝ) < 2 ^ (E - 1) := by positivity
  have hp : (2 : ℝ) ^ f.p = 2 * half f := by exact_mod_cast (two_half f).symm
  have hph : (2 : ℝ) ^ (f.p - 1) = half f := by unfold half; push_cast; ring
  constructor
  · have : (2 * Q : ℝ) < 2 * (2 * half f) + 1 := by
      have h3 : 2 * Q * (2 : ℝ) ^ (E - 1) < (2 * (2 * half f) + 1) * 2 ^ (E - 1) := by
        rw [hp] at hy1; nlinarith
      exact lt_of_mul_lt_mul_right h3 hS.le
    have : (2 * Q : ℕ) < 2 * (2 * half f) + 1 := by exact_mod_cast this
    omega
  · rcases hy2 with h1 | h1
    · exact Or.inl h1
    · right
      rw [hph] at h1
      have : (2 * half f : ℝ) ≤ 2 * Q + 1 := by
        have h3 : (2 * half f : ℝ) * 2 ^ (E - 1) ≤ (2 * Q + 1) * 2 ^ (E - 1) := by nlinarith
        exact le_of_mul_le_mul_right h3 hS
      have : (2 * half f : ℕ) ≤ 2 * Q + 1 := by exact_mod_cast this
      omega

theorem pack_mod_two (E Q : ℕ) : pack f E Q % 2 = Q % 2 := by
  unfold pack
  have := half_even f
  rw [Nat.add_mod, Nat.mul_mod, this]
  simp

/-- The encoding `pack f E Q` is nearest-even to `y` when it is finite. -/
theorem nearest_even_pack (y : ℝ) (E Q : ℕ) (h : RoundsTo f y E Q)
    (hL : pack f E Q < limit f) : NearestEven f y (pack f E Q) := by
  obtain ⟨hQ, hQ1⟩ := significand_bounds f y E Q h
  obtain ⟨hE, hy1, hy2, hr1, hr2, htie⟩ := h
  have hmag := mag_pack f E Q hE hQ hQ1
  set s : ℝ := (2 : ℝ) ^ (E - 1) with hsdef
  have hs : 0 < s := by positivity
  have hph : (2 : ℝ) ^ (f.p - 1) = half f := by unfold half; push_cast; ring
  have hw : (mag f (pack f E Q) : ℝ) = Q * s := by rw [hmag]; push_cast; ring
  -- every finite encoding is at least as far as `pack`, and farther unless at a tie
  have key : ∀ m, m < limit f →
      |(Q : ℝ) * s - y| ≤ |(mag f m : ℝ) - y| ∧
      (¬ (2 * y = (2 * Q + 1) * s ∨ 2 * y + s = 2 * Q * s) →
        |(mag f m : ℝ) - y| ≤ |(Q : ℝ) * s - y| → m = pack f E Q) := by
    intro m _
    by_cases hm : E = 1 ∨ E * half f ≤ m
    · obtain ⟨j, hj⟩ : 2 ^ (E - 1) ∣ mag f m := by
        rcases hm with h1 | h1
        · subst h1; simp
        · exact mag_dvd f E m hE h1
      have hjs : (mag f m : ℝ) = j * s := by rw [hj]; push_cast; ring
      rw [hjs]
      refine ⟨FmaGrid.grid_near y s Q j hs hr1 hr2, fun hnt hle => ?_⟩
      have m1 : 2 * y < (2 * Q + 1) * s := lt_of_le_of_ne hr1 (fun h => hnt (Or.inl h))
      have m2 : 2 * Q * s < 2 * y + s := lt_of_le_of_ne hr2 (fun h => hnt (Or.inr h.symm))
      have hjQ := FmaGrid.grid_unique y s Q j hs m1 m2 hle
      apply mag_inj f
      rw [hmag, hj, hjQ, mul_comm]
    · push Not at hm
      obtain ⟨hE2, hmE⟩ := hm
      have hE2' : 2 ≤ E := by omega
      have hb := mag_below f E m hE2' hmE
      have hb' : 2 * (mag f m : ℝ) + s ≤ 2 * ((half f : ℝ) * s) := by
        have : (2 * mag f m + 2 ^ (E - 1) : ℕ) ≤ 2 * (half f * 2 ^ (E - 1)) := by
          have e : (2 : ℕ) ^ (E - 1) = 2 * 2 ^ (E - 2) := by
            rw [← pow_succ']; congr 1; omega
          omega
        rw [hsdef]; exact_mod_cast this
      have hy2' : (half f : ℝ) * s ≤ y := by
        rcases hy2 with h1 | h1
        · omega
        · rw [hph] at h1; exact h1
      have hQB : (half f : ℝ) * s ≤ Q * s := by
        apply mul_le_mul_of_nonneg_right _ hs.le
        rcases hQ1 with h1 | h1
        · omega
        · exact_mod_cast h1
      have r2' : 2 * ((Q : ℝ) * s) ≤ 2 * y + s := by rw [← mul_assoc]; exact hr2
      obtain ⟨f1, f2⟩ := FmaGrid.below_far y s _ _ _ hs hb' hy2' hQB r2'
      refine ⟨f1, fun hnt hle => ?_⟩
      exfalso
      have m1 : 2 * y < (2 * Q + 1) * s := lt_of_le_of_ne hr1 (fun h => hnt (Or.inl h))
      have m2 : 2 * Q * s < 2 * y + s := lt_of_le_of_ne hr2 (fun h => hnt (Or.inr h.symm))
      have hq : |(Q : ℝ) * s - y| < s / 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
      exact lt_irrefl _ (lt_of_le_of_lt (f2.trans hle) hq)
  have hnear : Nearest f y (pack f E Q) := by
    refine ⟨hL, fun m hm => ?_⟩
    rw [hw]; exact (key m hm).1
  refine ⟨hnear, fun m hm => ?_⟩
  by_cases ht : 2 * y = (2 * Q + 1) * s ∨ 2 * y + s = 2 * Q * s
  · rw [pack_mod_two, htie ht]; exact Nat.zero_le _
  · have hle := hm.2 (pack f E Q) hL
    rw [hw] at hle
    rw [(key m hm.1).2 ht hle]

/-- Two nearest encodings differ by at most one. -/
theorem nearest_adjacent (y : ℝ) (a b : ℕ) (ha : Nearest f y a) (hb : Nearest f y b) :
    a ≤ b + 1 := by
  by_contra hn
  push Not at hn
  have hm1 : mag f b < mag f (b + 1) := mag_strict f (by omega)
  have hm2 : mag f (b + 1) < mag f a := mag_strict f (by omega)
  have hlim : b + 1 < limit f := by have := ha.1; omega
  have h1 := ha.2 (b + 1) hlim
  have h2 := hb.2 (b + 1) hlim
  have r1 : (mag f b : ℝ) < mag f (b + 1) := by exact_mod_cast hm1
  have r2 : (mag f (b + 1) : ℝ) < mag f a := by exact_mod_cast hm2
  rcases le_or_gt y (mag f (b + 1)) with hy | hy
  · rw [abs_of_pos (by linarith : (0 : ℝ) < mag f a - y),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ mag f (b + 1) - y)] at h1
    linarith
  · rw [abs_of_neg (by linarith : (mag f b : ℝ) - y < 0),
      abs_of_neg (by linarith : (mag f (b + 1) : ℝ) - y < 0)] at h2
    linarith

theorem nearest_even_unique (y : ℝ) (a b : ℕ) (ha : NearestEven f y a)
    (hb : NearestEven f y b) : a = b := by
  have h1 := nearest_adjacent f y a b ha.1 hb.1
  have h2 := nearest_adjacent f y b a hb.1 ha.1
  have hp : a % 2 = b % 2 := le_antisymm (ha.2 b hb.1) (hb.2 a ha.1)
  omega

/-! ### Existence -/

/-- Every nonnegative real has a nearest integer with the even choice at a tie. -/
theorem exists_round (z : ℝ) (hz : 0 ≤ z) :
    ∃ Q : ℕ, 2 * z ≤ 2 * Q + 1 ∧ 2 * (Q : ℝ) ≤ 2 * z + 1 ∧
      (2 * z = 2 * Q + 1 ∨ 2 * z + 1 = 2 * Q → Q % 2 = 0) := by
  set k := ⌊z⌋₊ with hk
  have h1 : (k : ℝ) ≤ z := Nat.floor_le hz
  have h2 : z < k + 1 := Nat.lt_floor_add_one z
  rcases lt_trichotomy (2 * (z - k)) 1 with h | h | h
  · refine ⟨k, by linarith, by linarith, fun ht => ?_⟩
    rcases ht with ht | ht <;> linarith
  · rcases Nat.mod_two_eq_zero_or_one k with hp | hp
    · refine ⟨k, by linarith, by linarith, fun _ => hp⟩
    · refine ⟨k + 1, by push_cast; linarith, by push_cast; linarith, fun _ => by omega⟩
  · refine ⟨k + 1, by push_cast; linarith, by push_cast; linarith, fun ht => ?_⟩
    push_cast at ht
    rcases ht with ht | ht <;> linarith

theorem exists_roundsTo (y : ℝ) (hy : 0 ≤ y) : ∃ E Q, RoundsTo f y E Q := by
  have hph : (2 : ℝ) ^ f.p = 2 * (2 : ℝ) ^ (f.p - 1) := by
    rw [← pow_succ']; congr 1; have := f.hp; omega
  obtain ⟨E, hE, hy1, hy2⟩ : ∃ E : ℕ, 1 ≤ E ∧ y < (2 : ℝ) ^ f.p * 2 ^ (E - 1) ∧
      (E = 1 ∨ (2 : ℝ) ^ (f.p - 1) * 2 ^ (E - 1) ≤ y) := by
    by_cases hsmall : y < (2 : ℝ) ^ f.p
    · exact ⟨1, le_rfl, by simpa using hsmall, Or.inl rfl⟩
    · push Not at hsmall
      set n := ⌊y⌋₊ with hn
      have hn1 : (n : ℝ) ≤ y := Nat.floor_le hy
      have hn2 : y < n + 1 := Nat.lt_floor_add_one y
      have hpn : 2 ^ f.p ≤ n := by
        apply Nat.le_floor; exact_mod_cast hsmall
      have hn0 : n ≠ 0 := by have := Nat.two_pow_pos f.p; omega
      set L := Nat.log 2 n with hL
      have hL1 : 2 ^ L ≤ n := Nat.pow_log_le_self 2 hn0
      have hL2 : n < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
      have hpL : f.p ≤ L := by
        by_contra h
        push Not at h
        have : 2 ^ (L + 1) ≤ 2 ^ f.p := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      refine ⟨L - f.p + 2, by omega, ?_, Or.inr ?_⟩
      · have e : f.p + (L - f.p + 2 - 1) = L + 1 := by omega
        rw [← pow_add, e]
        have : ((n + 1 : ℕ) : ℝ) ≤ ((2 ^ (L + 1) : ℕ) : ℝ) := by exact_mod_cast hL2
        push_cast at this
        linarith
      · have e : f.p - 1 + (L - f.p + 2 - 1) = L := by have := f.hp; omega
        rw [← pow_add, e]
        have : ((2 ^ L : ℕ) : ℝ) ≤ n := by exact_mod_cast hL1
        push_cast at this
        linarith
  set s : ℝ := (2 : ℝ) ^ (E - 1) with hs
  have hs0 : 0 < s := by positivity
  obtain ⟨Q, q1, q2, q3⟩ := exists_round (y / s) (div_nonneg hy hs0.le)
  have e1 : 2 * (y / s) * s = 2 * y := by field_simp
  refine ⟨E, Q, hE, hy1, hy2, ?_, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_right q1 hs0.le
    rw [e1] at this; linarith
  · have := mul_le_mul_of_nonneg_right q2 hs0.le
    rw [add_mul, e1] at this; linarith
  · intro ht
    apply q3
    rcases ht with ht | ht
    · left
      have : 2 * (y / s) * s = (2 * Q + 1) * s := by rw [e1]; exact ht
      exact mul_right_cancel₀ hs0.ne' this
    · right
      have : (2 * (y / s) + 1) * s = 2 * Q * s := by rw [add_mul, e1]; linarith
      exact mul_right_cancel₀ hs0.ne' this

/-! ### The reference -/

theorem exists_nearest (y : ℝ) : ∃ n, Nearest f y n := by
  classical
  have hL : 0 < limit f := by unfold limit; have := half_pos f; have := f.hF; positivity
  obtain ⟨n, hn, hm⟩ := Finset.exists_min_image (Finset.range (limit f))
    (fun n : ℕ => |(mag f n : ℝ) - y|) ⟨0, Finset.mem_range.mpr hL⟩
  exact ⟨n, Finset.mem_range.mp hn, fun m hm' => hm m (Finset.mem_range.mpr hm')⟩

theorem exists_nearest_even (y : ℝ) : ∃ n, NearestEven f y n := by
  classical
  obtain ⟨v, hv⟩ := exists_nearest f y
  let s := (Finset.range (limit f)).filter (fun n => Nearest f y n)
  have hsv : v ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hv.1, hv⟩
  obtain ⟨n, hn, hm⟩ := Finset.exists_min_image s (fun n : ℕ => n % 2) ⟨v, hsv⟩
  have hn' := Finset.mem_filter.mp hn
  exact ⟨n, hn'.2, fun m hm' =>
    hm m (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hm'.1, hm'⟩)⟩

/-- The nearest-even encoding of a nonnegative `y` in units, `limit f` from the overflow
threshold on. -/
noncomputable def refPos (y : ℝ) : ℕ :=
  if threshold f ≤ y then limit f else Classical.choose (exists_nearest_even f y)

/-- The encoding of significand `Q` in binade `E`, or infinity when it is past the finite
encodings. -/
def packInf (E Q : ℕ) : ℕ := if f.F ≤ E ∨ limit f ≤ pack f E Q then limit f else pack f E Q

theorem threshold_eq : threshold f = (4 * half f - 1 : ℝ) * 2 ^ (f.F - 3) := by
  unfold threshold
  have : (2 : ℝ) ^ (f.p + 1) = 4 * half f := by
    unfold half; push_cast
    rw [show f.p + 1 = (f.p - 1) + 2 by have := f.hp; omega, pow_add]; ring
  rw [this]

theorem positive_reference (y : ℝ) (E Q : ℕ) (h : RoundsTo f y E Q) :
    refPos f y = packInf f E Q := by
  obtain ⟨hQ, hQ1⟩ := significand_bounds f y E Q h
  have h' := h
  obtain ⟨hE, hy1, hy2, hr1, hr2, htie⟩ := h'
  have hB := half_pos f
  have hF := f.hF
  have hph : (2 : ℝ) ^ (f.p - 1) = half f := by unfold half; push_cast; ring
  have hp : (2 : ℝ) ^ f.p = 2 * half f := by exact_mod_cast (two_half f).symm
  have hT := threshold_eq f
  have hBr : (1 : ℝ) ≤ half f := by exact_mod_cast hB
  unfold packInf refPos
  by_cases hEF : f.F ≤ E
  · rw [if_pos (Or.inl hEF), if_pos]
    rw [hT]
    rcases hy2 with h1 | h1
    · omega
    · rw [hph] at h1
      have hpow : (2 : ℝ) ^ (f.F - 3) * 4 ≤ 2 ^ (E - 1) := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add]
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (f.F - 3)]
  by_cases hW : limit f ≤ pack f E Q
  · rw [if_pos (Or.inr hW), if_pos]
    have hE' : E = f.F - 1 := by
      unfold limit pack at hW
      by_contra hne
      have : E ≤ f.F - 2 := by omega
      have : (E - 1) * half f + Q ≤ (f.F - 3) * half f + 2 * half f := by
        have : (E - 1) * half f ≤ (f.F - 3) * half f := Nat.mul_le_mul_right _ (by omega)
        omega
      have : (f.F - 3) * half f + 2 * half f < f.F * half f := by
        rw [← Nat.add_mul]; exact Nat.mul_lt_mul_of_pos_right (by omega) hB
      omega
    have hQ' : Q = 2 * half f := by
      unfold limit pack at hW
      rw [hE'] at hW
      have : f.F * half f = (f.F - 1 - 1) * half f + 2 * half f := by
        rw [show f.F = (f.F - 1 - 1) + 2 by omega, Nat.add_mul]; simp
      omega
    rw [hE', hQ'] at hr2
    rw [hT]
    have e : (2 : ℝ) ^ (f.F - 1 - 1) = 2 * 2 ^ (f.F - 3) := by
      rw [← pow_succ']; congr 1; omega
    rw [e] at hr2
    push_cast at hr2
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (f.F - 3)]
  have hnot : ¬ (f.F ≤ E ∨ limit f ≤ pack f E Q) := by tauto
  rw [if_neg hnot, if_neg]
  · apply nearest_even_unique f y
    · exact Classical.choose_spec (exists_nearest_even f y)
    · exact nearest_even_pack f y E Q h (by omega)
  · push Not
    rw [hT]
    have hS : (0 : ℝ) < 2 ^ (f.F - 3) := by positivity
    by_cases hE2 : E ≤ f.F - 2
    · rw [hp] at hy1
      have hpow : (2 : ℝ) ^ (E - 1) ≤ 2 ^ (f.F - 3) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      nlinarith
    · have hE' : E = f.F - 1 := by omega
      have hQ2 : Q ≤ 2 * half f - 1 := by
        unfold limit pack at hW
        rw [hE'] at hW
        have : f.F * half f = (f.F - 1 - 1) * half f + 2 * half f := by
          rw [show f.F = (f.F - 1 - 1) + 2 by omega, Nat.add_mul]; simp
        omega
      have e : (2 : ℝ) ^ (E - 1) = 2 * 2 ^ (f.F - 3) := by
        rw [hE', ← pow_succ']; congr 1; omega
      rw [e] at hr1 htie
      have hstrict : 2 * y < (2 * Q + 1) * (2 * 2 ^ (f.F - 3)) ∨ Q < 2 * half f - 1 := by
        rcases lt_or_eq_of_le hr1 with h1 | h1
        · exact Or.inl h1
        · right
          have := htie (Or.inl h1)
          have := half_even f
          omega
      rcases hstrict with h1 | h1
      · have : (Q : ℝ) ≤ 2 * half f - 1 := by
          have : ((Q : ℕ) : ℝ) ≤ ((2 * half f - 1 : ℕ) : ℝ) := by exact_mod_cast hQ2
          rw [Nat.cast_sub (by omega)] at this; push_cast at this; linarith
        nlinarith
      · have : (Q : ℝ) + 1 ≤ 2 * half f - 1 := by
          have : ((Q + 1 : ℕ) : ℝ) ≤ ((2 * half f - 1 : ℕ) : ℝ) := by exact_mod_cast h1
          rw [Nat.cast_sub (by omega)] at this; push_cast at this; linarith
        nlinarith

#print axioms mag_succ
#print axioms mag_pack
#print axioms mag_dvd
#print axioms mag_below
#print axioms nearest_even_pack
#print axioms nearest_even_unique
#print axioms exists_roundsTo
#print axioms positive_reference

end Verified.Examples.StrconvGrid
