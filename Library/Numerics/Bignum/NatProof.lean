module

public import Library.Numerics.Bignum.Canonical

@[expose] public section

/-!
The natural functions equal their specifications.  Each applies one of MultiPrecision's theorems,
`add_eq`, `sub_eq`, `mul_eq`, or `divide_eq`, whose results are `digits N x` for the length `N`
of Knuth's algorithm, and `natTrim_digits` or `natTrim_eq` with `value_digits` turns the digits
into `limbsOf` of the exact result.  `natCmp_eq` applies Uscale's `le_spec` in both orders.
-/

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision
open LeanExe.Dialect

theorem value_lt_pow {u : Array UInt64} (hu : Digits u) {N : ℕ} (hN : u.size ≤ N) :
    value u < base ^ N :=
  lt_of_lt_of_le (value_lt hu) (Nat.pow_le_pow_right base_pos hN)

theorem le_eq {u v : Array UInt64} (hu : Digits u) (hv : Digits v) (hsu : u.size < 2 ^ 32)
    (hsv : v.size < 2 ^ 32) :
    Library.Numerics.Arithmetic.Uscale.le u v = decide (value u ≤ value v) := by
  rw [Library.Numerics.Arithmetic.Uscale.UscaleTheorem.le_spec u v (limbs_of_digits hu)
    (limbs_of_digits hv) hsu hsv, value_eq_val, value_eq_val]

theorem natCmp_eq {u v : Array UInt64} (hu : Digits u) (hv : Digits v) (hsu : u.size < 2 ^ 32)
    (hsv : v.size < 2 ^ 32) : natCmp u v = cmpSpec (value u) (value v) := by
  unfold natCmp cmpSpec
  rw [le_eq hu hv hsu hsv, le_eq hv hu hsv hsu]
  rcases lt_trichotomy (value u) (value v) with h | h | h
  · simp [h, h.le, not_le.mpr h]
  · simp [h]
  · simp [h, h.le, not_lt.mpr h.le, h.ne']

theorem natAdd_eq {u v : Array UInt64} (hu : Digits u) (hv : Digits v) (hsu : u.size < 2 ^ 32)
    (hsv : v.size < 2 ^ 32) : natAdd u v = limbsOf (value u + value v) := by
  unfold natAdd
  rw [add_eq u v hu hv (by omega) (by omega), addSpec]
  dsimp only
  apply natTrim_digits (by omega)
  have h1 := value_lt_pow hu (le_max_left u.size v.size)
  have h2 := value_lt_pow hv (le_max_right u.size v.size)
  rw [pow_succ]
  have := base_eq
  nlinarith

/-- Algorithm S of the larger minus the smaller, trimmed, is the canonical difference. -/
theorem natTrim_sub {u v : Array UInt64} (hu : Digits u) (hv : Digits v) (hsu : u.size < 2 ^ 32)
    (hsv : v.size < 2 ^ 32) (hle : value v ≤ value u) :
    natTrim (sub u v) = limbsOf (value u - value v) := by
  rw [sub_eq u v hu hv (by omega) (by omega), subSpec]
  dsimp only
  rw [natTrim_eq (digits_digits _ _) (by rw [digits_size]; omega), value_digits]
  have h1 := value_lt_pow hu (le_max_left u.size v.size)
  rw [show value u + base ^ max u.size v.size - value v =
      (value u - value v) + base ^ max u.size v.size by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

theorem natSub_eq {u v : Array UInt64} (hu : Digits u) (hv : Digits v) (hsu : u.size < 2 ^ 32)
    (hsv : v.size < 2 ^ 32) : natSub u v = natSubSpec (value u) (value v) := by
  unfold natSub natSubSpec
  rw [le_eq hv hu hsv hsu]
  by_cases h : value v ≤ value u
  · rw [decide_eq_true h, ite_eq_left rfl, natTrim_sub hu hv hsu hsv h]
    congr 1
    · simp; omega
    · congr 1; omega
  · rw [decide_eq_false h, ite_eq_right (by decide), natTrim_sub hv hu hsv hsu (by omega)]
    congr 1
    · simp; omega
    · congr 1; omega

theorem natMul_eq {u v : Array UInt64} (hu : Digits u) (hv : Digits v) (hsu : u.size < 2 ^ 32)
    (hsv : v.size < 2 ^ 32) : natMul u v = limbsOf (value u * value v) := by
  unfold natMul
  rw [mul_eq u v hu hv (by omega), mulSpec]
  dsimp only
  apply natTrim_digits (by omega)
  rw [pow_add]
  exact Nat.mul_lt_mul'' (value_lt hu) (value_lt hv)

theorem size_toUInt64_beq_zero {u : Array UInt64} (hs : u.size < 2 ^ 64) :
    (u.size.toUInt64 == 0) = decide (u.size = 0) := by
  have h := size_toNat hs
  by_cases h0 : u.size = 0
  · simp only [h0, decide_true]
    rw [h0] at h
    exact beq_iff_eq.mpr (UInt64.toNat_inj.mp (by rw [h]; rfl))
  · simp only [h0, decide_false]
    exact beq_eq_false_iff_ne.mpr fun he => h0 (by rw [← h, he]; rfl)

theorem slice_eq {w : Array UInt64} {start len : UInt64} {R : Array UInt64}
    (hs : R.size = len.toNat) (hw : start.toNat + len.toNat < 2 ^ 64)
    (h : ∀ i, i < len.toNat → w[start.toNat + i]! = R[i]!) : slice w start len = R := by
  apply array_ext (by rw [slice, build_size, hs])
  intro i hi
  rw [slice, build_size] at hi
  rw [slice, build_get hi, ← h i hi]
  congr 1
  rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
  omega

theorem natDivMod_eq {u v : Array UInt64} (hu : Canonical u) (hv : Canonical v)
    (hsu : u.size < 2 ^ 32) (hsv : v.size < 2 ^ 32) :
    natDivMod u v = natDivModSpec (value u) (value v) := by
  unfold natDivMod natDivModSpec
  rw [size_toUInt64_beq_zero (by omega)]
  by_cases h0 : v.size = 0
  · have hv0 : value v = 0 := (value_eq_zero_iff hv).mpr h0
    rw [decide_eq_true h0, ite_eq_left rfl, hv0, Nat.div_zero, Nat.mod_zero, limbsOf_zero,
      natTrim_canonical hu (by omega), ← (canonical_iff u).mp hu]
  · rw [decide_eq_false h0, ite_eq_right (by decide)]
    dsimp only
    have hmU := size_toNat (u := u) (by omega)
    have hnU := size_toNat (u := v) (by omega)
    rw [divide_eq u v hu.1 hv.1 (by omega), divSpec]
    dsimp only
    have hq : slice (digits u.size (value u / value v) ++ digits v.size (value u % value v)) 0
        u.size.toUInt64 = digits u.size (value u / value v) := by
      apply slice_eq (by rw [digits_size, hmU]) (by simp only [UInt64.toNat_zero]; omega)
      intro i hi
      rw [hmU] at hi
      rw [show (0 : UInt64).toNat + i = i from by simp, append_get_left (by rw [digits_size]; exact hi)]
    have hr : slice (digits u.size (value u / value v) ++ digits v.size (value u % value v))
        u.size.toUInt64 v.size.toUInt64 = digits v.size (value u % value v) := by
      apply slice_eq (by rw [digits_size, hnU]) (by omega)
      intro i hi
      rw [hnU] at hi
      rw [hmU, append_get_right (by rw [digits_size]; omega)
        (by rw [digits_size, digits_size]; omega), digits_size, Nat.add_sub_cancel_left]
    have hpos : 0 < value v := by
      rcases Nat.eq_zero_or_pos (value v) with h | h
      · exact absurd ((value_eq_zero_iff hv).mp h) h0
      · exact h
    rw [hq, hr, natTrim_digits (by omega) (lt_of_le_of_lt (Nat.div_le_self _ _) (value_lt hu.1)),
      natTrim_digits (by omega) (lt_trans (Nat.mod_lt _ hpos) (value_lt hv.1))]

theorem natDivModChecked_eq {u v : Array UInt64} (hu : Canonical u) (hv : Canonical v)
    (hsu : u.size < 2 ^ 32) (hsv : v.size < 2 ^ 32) :
    natDivModChecked u v = natDivModCheckedSpec (value u) (value v) := by
  unfold natDivModChecked natDivModCheckedSpec
  rw [size_toUInt64_beq_zero (by omega)]
  by_cases h0 : v.size = 0
  · rw [decide_eq_true h0, ite_eq_left rfl, ite_eq_left ((value_eq_zero_iff hv).mpr h0), limbsOf_zero]
  · rw [decide_eq_false h0, ite_eq_right (by decide),
      ite_eq_right fun h => h0 ((value_eq_zero_iff hv).mp h)]
    dsimp only
    rw [natDivMod_eq hu hv hsu hsv]
    rfl

end Library.Numerics.Bignum
