import Library.Numerics.MultiPrecision.Program
import Library.Numerics.MultiPrecision.Spec
import LeanExe.Dialect.Lemmas
import LeanExe.Dialect.ArrayLemmas

/-! The proofs that Algorithms A, S, and M compute the digits of the sum, the difference, and the
product.  `prefixValue u q` is the number of the first `q` digits of `u`.  Each loop keeps an
equation between the prefix values of its arguments and of the digits it has written, with the
carry or the borrow weighted by the next power of the base.  `digits_eq` shows that an array of
`N` digits whose value is `x` modulo `b^N` equals the specification's array `digits N x`. -/

namespace Library.Numerics.MultiPrecision

open LeanExe.Dialect

/-! ### Values of digits -/

theorem base_pos : 0 < base := by unfold base; positivity

theorem prefixValue_zero (u : Array UInt64) : prefixValue u 0 = 0 := by simp [prefixValue]

theorem prefixValue_succ (u : Array UInt64) (q : Nat) :
    prefixValue u (q + 1) = prefixValue u q + u[q]!.toNat * base ^ q := by
  simp [prefixValue, List.range_succ]

theorem prefixValue_congr {u w : Array UInt64} {q : Nat} (h : ∀ p, p < q → u[p]! = w[p]!) :
    prefixValue u q = prefixValue w q := by
  unfold prefixValue
  congr 1
  apply List.map_congr_left
  intro p hp
  rw [h p (List.mem_range.mp hp)]

/-- The digits past the end of `u` are 0, so the prefix values past the end are `value u`. -/
theorem prefixValue_ge {u : Array UInt64} {q : Nat} (hq : u.size ≤ q) :
    prefixValue u q = value u := by
  induction q, hq using Nat.le_induction with
  | base => rfl
  | succ q hq ih =>
    rw [prefixValue_succ, ih, getElem!_neg u q (by omega), show (default : UInt64) = 0 from rfl]
    simp

theorem prefixValue_lt {u : Array UInt64} {q : Nat} (h : ∀ p, p < q → u[p]!.toNat < base) :
    prefixValue u q < base ^ q := by
  induction q with
  | zero => simp [prefixValue_zero]
  | succ q ih =>
    rw [prefixValue_succ, pow_succ]
    have h1 := ih fun p hp => h p (by omega)
    have h2 := h q (by omega)
    have h3 : u[q]!.toNat * base ^ q + base ^ q ≤ base ^ q * base := by
      calc u[q]!.toNat * base ^ q + base ^ q = (u[q]!.toNat + 1) * base ^ q := by ring
        _ ≤ base * base ^ q := Nat.mul_le_mul_right _ h2
        _ = base ^ q * base := by ring
    omega

theorem prefixValue_mod {u : Array UInt64} {q n : Nat} (h : ∀ p, p < n → u[p]!.toNat < base)
    (hq : q ≤ n) : prefixValue u n % base ^ q = prefixValue u q := by
  induction n, hq using Nat.le_induction with
  | base => exact Nat.mod_eq_of_lt (prefixValue_lt h)
  | succ n hqn ih =>
    rw [prefixValue_succ, show base ^ n = base ^ q * base ^ (n - q) by
      rw [← pow_add]; congr 1; omega, mul_left_comm, Nat.add_mul_mod_self_left]
    exact ih fun p hp => h p (by omega)

theorem prefixValue_digit {u : Array UInt64} {n i : Nat} (h : ∀ p, p < n → u[p]!.toNat < base)
    (hi : i < n) : prefixValue u n / base ^ i % base = u[i]!.toNat := by
  rw [← Nat.mod_mul_right_div_self, ← pow_succ, prefixValue_mod h hi, prefixValue_succ,
    Nat.add_mul_div_right _ _ (pow_pos base_pos i),
    Nat.div_eq_of_lt (prefixValue_lt fun p hp => h p (by omega)), Nat.zero_add]

theorem mod_digit {x N i : Nat} (hi : i < N) :
    x % base ^ N / base ^ i % base = x / base ^ i % base := by
  rw [show base ^ N = base ^ i * base ^ (N - i) by rw [← pow_add]; congr 1; omega,
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self base (by omega))]

theorem digits_size (n x : Nat) : (digits n x).size = n := by simp [digits]

theorem digits_get {n x i : Nat} (hi : i < n) :
    (digits n x)[i]! = UInt64.ofNat (x / base ^ i % base) := by
  rw [getElem!_pos (digits n x) i (by rw [digits_size]; exact hi)]
  simp [digits]

/-- An array of `N` digits whose value is `x` modulo `base ^ N` is the specification's array of the
digits of `x`. -/
theorem digits_eq {R : Array UInt64} {N x : Nat} (hs : R.size = N)
    (hd : ∀ p, p < N → R[p]!.toNat < base) (hv : value R = x % base ^ N) : digits N x = R := by
  apply Array.ext (by rw [digits_size, hs])
  intro i h1 h2
  have hi : i < N := by rw [digits_size] at h1; exact h1
  rw [← getElem!_pos (digits N x) i h1, ← getElem!_pos R i h2, digits_get hi, ← mod_digit hi,
    ← hv]
  unfold value
  rw [hs, prefixValue_digit hd hi, UInt64.ofNat_toNat]

/-- Every word of an array of digits, and every read past its end, is a digit. -/
theorem digit_all {u : Array UInt64} (hu : Digits u) (p : Nat) : u[p]!.toNat < base := by
  by_cases hp : p < u.size
  · exact hu p hp
  · rw [getElem!_neg u p hp]; exact base_pos

theorem value_lt {u : Array UInt64} (hu : Digits u) : value u < base ^ u.size :=
  prefixValue_lt fun p _ => digit_all hu p

theorem base_eq : base = 4294967296 := by unfold base; norm_num

/-! ### The width of two arguments -/

theorem size_toNat {u : Array UInt64} (h : u.size < 2 ^ 64) : u.size.toUInt64.toNat = u.size := by
  simp only [Nat.toUInt64, UInt64.toNat_ofNat']; omega

theorem width_toNat {u v : Array UInt64} (hu : u.size < 2 ^ 64) (hv : v.size < 2 ^ 64) :
    (width u v).toNat = max u.size v.size := by
  unfold width
  split
  · rename_i h
    rw [UInt64.lt_iff_toNat_lt, size_toNat hu, size_toNat hv] at h
    rw [size_toNat hv]; omega
  · rename_i h
    rw [UInt64.lt_iff_toNat_lt, size_toNat hu, size_toNat hv] at h
    rw [size_toNat hu]; omega

/-! ### Algorithm A -/

/-- The digits that the loop of Algorithm A writes, followed by the final carry, are the digits of
the sum. -/
theorem add_result {u v : Array UInt64} (c : UInt64) (w : Array UInt64)
    (hs : w.size = max u.size v.size) (hd : ∀ p, p < max u.size v.size → w[p]!.toNat < base)
    (hc : c.toNat ≤ 1)
    (hval : prefixValue w (max u.size v.size) + c.toNat * base ^ max u.size v.size =
      value u + value v) :
    w.push c = digits (max u.size v.size + 1) (value u + value v) := by
  have hlast : (w.push c)[max u.size v.size]! = c := by rw [← hs]; exact push_get_size _ _
  have hR : ∀ p, p < max u.size v.size + 1 → (w.push c)[p]!.toNat < base := by
    intro p hp
    rcases Nat.lt_or_ge p (max u.size v.size) with h | h
    · rw [push_get_lt _ _ (by omega)]; exact hd p h
    · rw [show p = max u.size v.size by omega, hlast, base_eq]; omega
  have hV : value (w.push c) = value u + value v := by
    unfold value
    rw [Array.size_push, hs, prefixValue_succ,
      prefixValue_congr (q := max u.size v.size) fun p hp => push_get_lt _ _ (by omega), hlast, hval]
    rfl
  symm
  apply digits_eq (by simp [hs]) hR
  rw [← hV, Nat.mod_eq_of_lt]
  unfold value; rw [Array.size_push, hs]; exact prefixValue_lt hR


theorem add_eq (u v : Array UInt64) (hu : Digits u) (hv : Digits v) (hsu : u.size < 2 ^ 64)
    (hsv : v.size < 2 ^ 64) : add u v = addSpec (u, v) := by
  have hk := width_toNat hsu hsv
  have h := loop_induction (n := width u v) (init := ((0 : UInt64), (#[] : Array UInt64)))
    (f := fun j s => ((u[j.toNat]! + v[j.toNat]! + s.1) / 4294967296,
      s.2.push ((u[j.toNat]! + v[j.toNat]! + s.1) % 4294967296)))
    (P := fun j s => s.2.size = j ∧ (∀ p, p < j → s.2[p]!.toNat < base) ∧ s.1.toNat ≤ 1 ∧
      prefixValue s.2 j + s.1.toNat * base ^ j = prefixValue u j + prefixValue v j)
    ⟨rfl, fun p hp => absurd hp (Nat.not_lt_zero _), by simp, by simp [prefixValue_zero]⟩
    (by
      intro j s hj ⟨hs, hd, hc, hval⟩
      have hjj : (UInt64.ofNat j).toNat = j := UInt64.toNat_ofNat_of_lt' (show j < 2 ^ 64 by omega)
      have hU := digit_all hu j
      have hV := digit_all hv j
      rw [base_eq] at hU hV
      have ht : (u[j]! + v[j]! + s.1).toNat = u[j]!.toNat + v[j]!.toNat + s.1.toNat := by
        simp only [UInt64.toNat_add]; omega
      simp only [hjj]
      have hpush : ∀ p, p < j →
          (s.2.push ((u[j]! + v[j]! + s.1) % 4294967296))[p]! = s.2[p]! := fun p hp =>
        push_get_lt _ _ (by omega)
      have hlast : (s.2.push ((u[j]! + v[j]! + s.1) % 4294967296))[j]! =
          (u[j]! + v[j]! + s.1) % 4294967296 := by rw [← hs]; exact push_get_size _ _
      refine ⟨by simp [hs], fun p hp => ?_, ?_, ?_⟩
      · rcases Nat.lt_or_ge p j with h | h
        · rw [hpush p h]; exact hd p h
        · rw [show p = j by omega, hlast, UInt64.toNat_mod, ht, base_eq]
          simp only [UInt64.reduceToNat]; omega
      · rw [UInt64.toNat_div, ht]; simp only [UInt64.reduceToNat]; omega
      · rw [prefixValue_succ, prefixValue_congr hpush, hlast, prefixValue_succ, prefixValue_succ,
          UInt64.toNat_div, UInt64.toNat_mod, ht]
        have hdm := Nat.mod_add_div (u[j]!.toNat + v[j]!.toNat + s.1.toNat) 4294967296
        simp only [UInt64.reduceToNat]
        rw [base_eq] at hval ⊢
        zify at hval hdm ⊢
        linear_combination hval + (4294967296 : ℤ) ^ j * hdm)
  rw [hk] at h
  obtain ⟨hs, hd, hc, hval⟩ := h
  rw [prefixValue_ge (le_max_left _ _), prefixValue_ge (le_max_right _ _)] at hval
  unfold add addSpec
  exact add_result _ _ hs hd hc hval

/-! ### Algorithm S -/

/-- The digits that the loop of Algorithm S writes are the digits of the difference, modulo
`base ^ k`. -/
theorem sub_result {u v : Array UInt64} (hv : Digits v) (c : UInt64) (w : Array UInt64)
    (hs : w.size = max u.size v.size) (hd : ∀ p, p < max u.size v.size → w[p]!.toNat < base)
    (hc : c.toNat ≤ 1)
    (hval : prefixValue w (max u.size v.size) + value v =
      value u + c.toNat * base ^ max u.size v.size) :
    w = digits (max u.size v.size) (value u + base ^ max u.size v.size - value v) := by
  have hW : prefixValue w (max u.size v.size) < base ^ max u.size v.size := prefixValue_lt hd
  have hvv : value v < base ^ max u.size v.size :=
    lt_of_lt_of_le (value_lt hv) (Nat.pow_le_pow_right base_pos (le_max_right _ _))
  have hvw : value w = prefixValue w (max u.size v.size) := by unfold value; rw [hs]
  symm
  apply digits_eq hs hd
  rw [hvw]
  rcases (show c.toNat = 0 ∨ c.toNat = 1 by omega) with h0 | h1
  · rw [h0, Nat.zero_mul, Nat.add_zero] at hval
    rw [show value u + base ^ max u.size v.size - value v = prefixValue w (max u.size v.size) +
      1 * base ^ max u.size v.size by omega, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hW]
  · rw [h1, Nat.one_mul] at hval
    rw [show value u + base ^ max u.size v.size - value v = prefixValue w (max u.size v.size) by
      omega, Nat.mod_eq_of_lt hW]

theorem sub_eq (u v : Array UInt64) (hu : Digits u) (hv : Digits v) (hsu : u.size < 2 ^ 64)
    (hsv : v.size < 2 ^ 64) : sub u v = subSpec (u, v) := by
  have hk := width_toNat hsu hsv
  have h := loop_induction (n := width u v) (init := ((0 : UInt64), (#[] : Array UInt64)))
    (f := fun j s => (1 - (u[j.toNat]! + 4294967296 - v[j.toNat]! - s.1) / 4294967296,
      s.2.push ((u[j.toNat]! + 4294967296 - v[j.toNat]! - s.1) % 4294967296)))
    (P := fun j s => s.2.size = j ∧ (∀ p, p < j → s.2[p]!.toNat < base) ∧ s.1.toNat ≤ 1 ∧
      prefixValue s.2 j + prefixValue v j = prefixValue u j + s.1.toNat * base ^ j)
    ⟨rfl, fun p hp => absurd hp (Nat.not_lt_zero _), by simp, by simp [prefixValue_zero]⟩
    (by
      intro j s hj ⟨hs, hd, hc, hval⟩
      have hjj : (UInt64.ofNat j).toNat = j := UInt64.toNat_ofNat_of_lt' (show j < 2 ^ 64 by omega)
      have hU := digit_all hu j
      have hV := digit_all hv j
      rw [base_eq] at hU hV
      have ht : (u[j]! + 4294967296 - v[j]! - s.1).toNat =
          u[j]!.toNat + 4294967296 - v[j]!.toNat - s.1.toNat := by
        simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.reduceToNat]; omega
      have hb : (1 - (u[j]! + 4294967296 - v[j]! - s.1) / 4294967296).toNat =
          1 - (u[j]!.toNat + 4294967296 - v[j]!.toNat - s.1.toNat) / 4294967296 := by
        simp only [UInt64.toNat_sub, UInt64.toNat_div, ht, UInt64.reduceToNat]; omega
      simp only [hjj]
      have hpush : ∀ p, p < j →
          (s.2.push ((u[j]! + 4294967296 - v[j]! - s.1) % 4294967296))[p]! = s.2[p]! := fun p hp =>
        push_get_lt _ _ (by omega)
      have hlast : (s.2.push ((u[j]! + 4294967296 - v[j]! - s.1) % 4294967296))[j]! =
          (u[j]! + 4294967296 - v[j]! - s.1) % 4294967296 := by rw [← hs]; exact push_get_size _ _
      refine ⟨by simp [hs], fun p hp => ?_, by rw [hb]; omega, ?_⟩
      · rcases Nat.lt_or_ge p j with h | h
        · rw [hpush p h]; exact hd p h
        · rw [show p = j by omega, hlast, UInt64.toNat_mod, ht, base_eq]
          simp only [UInt64.reduceToNat]; omega
      · rw [prefixValue_succ, prefixValue_congr hpush, hlast, prefixValue_succ, prefixValue_succ,
          UInt64.toNat_mod, ht, hb]
        have hdig : (u[j]!.toNat + 4294967296 - v[j]!.toNat - s.1.toNat) % 4294967296 +
            v[j]!.toNat + s.1.toNat = u[j]!.toNat +
            (1 - (u[j]!.toNat + 4294967296 - v[j]!.toNat - s.1.toNat) / 4294967296) * 4294967296 := by
          omega
        simp only [UInt64.reduceToNat]
        rw [base_eq] at hval ⊢
        zify at hval hdig ⊢
        linear_combination hval + (4294967296 : ℤ) ^ j * hdig)
  rw [hk] at h
  obtain ⟨hs, hd, hc, hval⟩ := h
  rw [prefixValue_ge (le_max_left _ _), prefixValue_ge (le_max_right _ _)] at hval
  unfold sub subSpec
  exact sub_result hv _ _ hs hd hc hval

/-! ### Algorithm M -/

theorem prefixValue_zeros {u : Array UInt64} (h : ∀ p : Nat, u[p]! = 0) (q : Nat) :
    prefixValue u q = 0 := by
  induction q with
  | zero => exact prefixValue_zero u
  | succ q ih => rw [prefixValue_succ, ih, h]; simp

/-- The end of one pass of Algorithm M: writing the final carry `c` at position `j + m` keeps the
invariant of the outer loop. -/
theorem mul_outer_step {u v w : Array UInt64} {j : Nat} (c : UInt64) (w' : Array UInt64)
    (hz : ∀ p, j + u.size ≤ p → w[p]! = 0)
    (hval : prefixValue w (j + u.size) = value u * prefixValue v j)
    (hs' : w'.size = u.size + v.size) (hd' : ∀ p : Nat, w'[p]!.toNat < base) (hc' : c.toNat < base)
    (hun : ∀ p, u.size + j ≤ p → w'[p]! = w[p]!)
    (hval' : prefixValue w' (u.size + j) + c.toNat * base ^ (u.size + j) =
      prefixValue w (u.size + j) + prefixValue u u.size * v[j]!.toNat * base ^ j)
    (hj : j < v.size) :
    (w'.set! (j + u.size) c).size = u.size + v.size ∧
      (∀ p : Nat, (w'.set! (j + u.size) c)[p]!.toNat < base) ∧
      (∀ p, j + 1 + u.size ≤ p → (w'.set! (j + u.size) c)[p]! = 0) ∧
      prefixValue (w'.set! (j + u.size) c) (j + 1 + u.size) = value u * prefixValue v (j + 1) := by
  have hget := fun (p : Nat) => get_set w' (j + u.size) c p (by omega)
  refine ⟨by simp [hs'], fun p => ?_, fun p hp => ?_, ?_⟩
  · rw [hget]; split
    · exact hc'
    · exact hd' p
  · rw [hget, ite_eq_right (show ¬ p = j + u.size by omega), hun p (by omega), hz p (by omega)]
  · have hcongr : prefixValue (w'.set! (j + u.size) c) (j + u.size) = prefixValue w' (j + u.size) :=
      prefixValue_congr fun p hp => by rw [hget, ite_eq_right (show ¬ p = j + u.size by omega)]
    rw [show j + 1 + u.size = j + u.size + 1 by omega, prefixValue_succ, hget, ite_eq_left rfl,
      hcongr, show j + u.size = u.size + j by omega, hval', show u.size + j = j + u.size by omega,
      hval, prefixValue_succ]
    unfold value
    ring

theorem mul_eq (u v : Array UInt64) (hu : Digits u) (hv : Digits v)
    (hsize : u.size + v.size < 2 ^ 64) : mul u v = mulSpec (u, v) := by
  have hm := size_toNat (u := u) (by omega)
  have hn := size_toNat (u := v) (by omega)
  have hmn : (u.size.toUInt64 + v.size.toUInt64).toNat = u.size + v.size := by
    simp only [UInt64.toNat_add, hm, hn]; omega
  have h := loop_induction (n := v.size.toUInt64)
    (init := LeanExe.build (u.size.toUInt64 + v.size.toUInt64) fun _ => (0 : UInt64))
    (f := fun j w =>
      let s := LeanExe.loop u.size.toUInt64 ((0 : UInt64), w) fun i s =>
        ((u[i.toNat]! * v[j.toNat]! + s.2[(i + j).toNat]! + s.1) / 4294967296,
          s.2.set! (i + j).toNat ((u[i.toNat]! * v[j.toNat]! + s.2[(i + j).toNat]! + s.1) % 4294967296))
      s.2.set! (j + u.size.toUInt64).toNat s.1)
    (P := fun j w => w.size = u.size + v.size ∧ (∀ p : Nat, w[p]!.toNat < base) ∧
      (∀ p, j + u.size ≤ p → w[p]! = 0) ∧ prefixValue w (j + u.size) = value u * prefixValue v j)
    (by
      have hz : ∀ p : Nat,
          (LeanExe.build (u.size.toUInt64 + v.size.toUInt64) fun _ => (0 : UInt64))[p]! = 0 := by
        intro p
        by_cases hp : p < (u.size.toUInt64 + v.size.toUInt64).toNat
        · rw [build_get hp]
        · rw [build_get_out hp]; rfl
      refine ⟨by rw [build_size, hmn], fun p => by rw [hz]; exact base_pos, fun p _ => hz p, ?_⟩
      rw [prefixValue_zeros hz, prefixValue_zero, Nat.mul_zero])
    (by
      intro j w hj ⟨hs, hd, hz, hval⟩
      rw [hn] at hj
      have hjj : (UInt64.ofNat j).toNat = j := UInt64.toNat_ofNat_of_lt' (show j < 2 ^ 64 by omega)
      have hV := digit_all hv j
      have hin := loop_induction (n := u.size.toUInt64) (init := ((0 : UInt64), w))
        (f := fun i s =>
          ((u[i.toNat]! * v[(UInt64.ofNat j).toNat]! + s.2[(i + UInt64.ofNat j).toNat]! + s.1) /
              4294967296,
            s.2.set! (i + UInt64.ofNat j).toNat
              ((u[i.toNat]! * v[(UInt64.ofNat j).toNat]! + s.2[(i + UInt64.ofNat j).toNat]! + s.1) %
                4294967296)))
        (P := fun i s => s.2.size = u.size + v.size ∧ (∀ p : Nat, s.2[p]!.toNat < base) ∧
          s.1.toNat < base ∧ (∀ p, i + j ≤ p → s.2[p]! = w[p]!) ∧
          prefixValue s.2 (i + j) + s.1.toNat * base ^ (i + j) =
            prefixValue w (i + j) + prefixValue u i * v[j]!.toNat * base ^ j)
        ⟨hs, hd, base_pos, fun _ _ => rfl, by simp [prefixValue_zero]⟩
        (by
          intro i s hi ⟨hs', hd', hc', hun, hval'⟩
          rw [hm] at hi
          have hii : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (show i < 2 ^ 64 by omega)
          have hij : (UInt64.ofNat i + UInt64.ofNat j).toNat = i + j := by
            simp only [UInt64.toNat_add, hii, hjj]; omega
          have hU := digit_all hu i
          have hW := hd' (i + j)
          rw [base_eq] at hU hV hW hc'
          have hprod : u[i]!.toNat * v[j]!.toNat ≤ 4294967295 * 4294967295 :=
            Nat.mul_le_mul (by omega) (by omega)
          have ht : (u[i]! * v[j]! + s.2[i + j]! + s.1).toNat =
              u[i]!.toNat * v[j]!.toNat + s.2[i + j]!.toNat + s.1.toNat := by
            simp only [UInt64.toNat_add, UInt64.toNat_mul]; omega
          simp only [hii, hjj, hij]
          have hget := fun (p : Nat) => get_set s.2 (i + j)
            ((u[i]! * v[j]! + s.2[i + j]! + s.1) % 4294967296) p (by omega)
          refine ⟨by simp [hs'], fun p => ?_, ?_, fun p hp => ?_, ?_⟩
          · rw [hget]; split
            · rw [UInt64.toNat_mod, ht, base_eq]; simp only [UInt64.reduceToNat]; omega
            · exact hd' p
          · rw [UInt64.toNat_div, ht, base_eq]; simp only [UInt64.reduceToNat]; omega
          · rw [hget, ite_eq_right (show ¬ p = i + j by omega)]; exact hun p (by omega)
          · have hwij := hun (i + j) (le_refl _)
            have hcongr : prefixValue (s.2.set! (i + j)
                ((u[i]! * v[j]! + s.2[i + j]! + s.1) % 4294967296)) (i + j) =
                prefixValue s.2 (i + j) :=
              prefixValue_congr fun p hp => by rw [hget, ite_eq_right (show ¬ p = i + j by omega)]
            rw [show i + 1 + j = i + j + 1 by omega, prefixValue_succ, hget, ite_eq_left rfl,
              hcongr, prefixValue_succ, prefixValue_succ, ← hwij, UInt64.toNat_div, UInt64.toNat_mod,
              ht]
            have hdm := Nat.mod_add_div
              (u[i]!.toNat * v[j]!.toNat + s.2[i + j]!.toNat + s.1.toNat) 4294967296
            simp only [UInt64.reduceToNat]
            rw [base_eq] at hval' ⊢
            zify at hval' hdm ⊢
            linear_combination hval' + (4294967296 : ℤ) ^ (i + j) * hdm)
      rw [hm] at hin
      obtain ⟨hs2, hd2, hc2, hun2, hval2⟩ := hin
      have hjm : (UInt64.ofNat j + u.size.toUInt64).toNat = j + u.size := by
        simp only [UInt64.toNat_add, hjj, hm]; omega
      dsimp only
      rw [hjm]
      exact mul_outer_step _ _ hz hval hs2 hd2 hc2 (fun p hp => hun2 p (by omega))
        (by rw [show u.size + j = u.size + j from rfl]; exact hval2) hj)
  rw [hn] at h
  obtain ⟨hs, hd, -, hval⟩ := h
  unfold mul mulSpec
  dsimp only
  generalize (LeanExe.loop v.size.toUInt64
    (LeanExe.build (u.size.toUInt64 + v.size.toUInt64) fun _ => (0 : UInt64)) fun j w =>
      let s := LeanExe.loop u.size.toUInt64 ((0 : UInt64), w) fun i s =>
        ((u[i.toNat]! * v[j.toNat]! + s.2[(i + j).toNat]! + s.1) / 4294967296,
          s.2.set! (i + j).toNat ((u[i.toNat]! * v[j.toNat]! + s.2[(i + j).toNat]! + s.1) % 4294967296))
      s.2.set! (j + u.size.toUInt64).toNat s.1) = R at hs hd hval ⊢
  have hR : value R = value u * value v := by
    show prefixValue R R.size = _
    rw [hs, show u.size + v.size = v.size + u.size by omega, hval]
    rfl
  have hlt : value R < base ^ (u.size + v.size) := by
    unfold value; rw [hs]; exact prefixValue_lt fun p _ => hd p
  symm
  apply digits_eq hs fun p _ => hd p
  rw [← hR, Nat.mod_eq_of_lt hlt]

end Library.Numerics.MultiPrecision
