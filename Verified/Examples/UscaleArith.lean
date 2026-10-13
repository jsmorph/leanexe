import Verified.Examples.UscaleBase
import Mathlib.Data.Nat.Size

/-!
The values of `Uscale`'s shift, comparison, subtraction, and bit lengths.  `shl a k` is the product
by `2 ^ (k % 32)` followed by `k / 32` zero limbs below it, so its list of limbs is the zero limbs
followed by the product's (`shl_spec`).  `le` compares limbs from the top, and its state records
whether the values agree above the current limb (`le_spec`).  `sub` keeps the invariant that the
first `k` limbs of the result and of `b` add up to the first `k` limbs of `a` plus the borrow times
`2 ^ (32 k)` (`sub_spec`).  `wordBits` and `bitLen` give Mathlib's `Nat.size` (`bitLen_spec`).
-/

namespace Verified.Examples.UscaleTheorem
open Uscale

/-! ### `LeanExe.build` -/

theorem build_size {α : Type} (n : UInt64) (f : UInt64 → α) : (LeanExe.build n f).size = n.toNat := by
  simp [LeanExe.build]

theorem build_getElem {α : Type} (n : UInt64) (f : UInt64 → α) (i : ℕ) (h : i < n.toNat) :
    (LeanExe.build n f).toList[i]'(by simp [LeanExe.build]; exact h) = f (UInt64.ofNat i) := by
  simp [LeanExe.build]

/-! ### `shl` -/

theorem valL_replicate (q : ℕ) (l : List UInt64) :
    valL (List.replicate q 0 ++ l) = 2 ^ (32 * q) * valL l := by
  induction q with
  | zero => simp
  | succ q ih =>
    simp only [List.replicate_succ, List.cons_append, valL, ih]
    simp
    rw [show 32 * (q + 1) = 32 + 32 * q by ring, pow_add]; ring

theorem shl_spec (a : Array UInt64) (k : UInt64) (ha : Limbs a) (hs : a.size < 2 ^ 32) :
    Limbs (shl a k) ∧ val (shl a k) = val a * 2 ^ k.toNat ∧
      (shl a k).size = a.size + 1 + k.toNat / 32 := by
  have hr : ((1 : UInt64) <<< (k &&& 31)).toNat = 2 ^ (k.toNat % 32) := by
    rw [UInt64.toNat_shiftLeft, UInt64.toNat_and]
    rw [show (31 : UInt64).toNat = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    have h1 : k.toNat % 2 ^ 5 % 64 = k.toNat % 32 := by omega
    rw [h1, show (1 : UInt64).toNat = 1 from rfl, Nat.shiftLeft_eq, one_mul]
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hq : (k >>> 5).toNat = k.toNat / 32 := by
    rw [UInt64.toNat_shiftRight, show (5 : UInt64).toNat % 64 = 5 from rfl,
      Nat.shiftRight_eq_div_pow]
  obtain ⟨hb1, hb2, hb3⟩ := mulSmall_spec a ((1 : UInt64) <<< (k &&& 31)) 0 ha (by omega)
    (by rw [hr]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)) (by decide)
  unfold shl
  dsimp only
  generalize mulSmall a ((1 : UInt64) <<< (k &&& 31)) 0 = b at hb1 hb2 hb3
  have hk := k.toNat_lt
  have hN : (b.size.toUInt64 + (k >>> 5)).toNat = b.size + k.toNat / 32 := by
    rw [UInt64.toNat_add, size_toUInt64 b (by omega), hq]
    exact Nat.mod_eq_of_lt (by omega)
  have hlist : (LeanExe.build (b.size.toUInt64 + (k >>> 5)) fun i =>
      if i < k >>> 5 then (0 : UInt64) else b[(i - (k >>> 5)).toNat]!).toList =
      List.replicate (k.toNat / 32) (0 : UInt64) ++ b.toList := by
    apply List.ext_getElem
    · simp [LeanExe.build, hN]; omega
    · intro i h1 h2
      rw [build_getElem _ _ i (by simpa [LeanExe.build] using h1)]
      have hi : i < 2 ^ 64 := by
        have : i < b.size + k.toNat / 32 := by simpa [LeanExe.build, hN] using h1
        omega
      by_cases hlt : i < k.toNat / 32
      · have : UInt64.ofNat i < k >>> 5 := by
          rw [UInt64.lt_iff_toNat_lt, ofNat_toNat i hi, hq]; exact hlt
        rw [if_pos this, List.getElem_append_left (by simpa using hlt)]
        simp
      · have : ¬ UInt64.ofNat i < k >>> 5 := by
          rw [UInt64.lt_iff_toNat_lt, ofNat_toNat i hi, hq]; exact hlt
        rw [if_neg this, List.getElem_append_right (by simpa using hlt)]
        have hsub : (UInt64.ofNat i - (k >>> 5)).toNat = i - k.toNat / 32 := by
          rw [UInt64.toNat_sub_of_le _ _ (by
            rw [UInt64.le_iff_toNat_le, ofNat_toNat i hi, hq]; omega), ofNat_toNat i hi, hq]
        rw [hsub]
        simp only [List.length_replicate]
        have hlen : i - k.toNat / 32 < b.size := by
          have : i < b.size + k.toNat / 32 := by simpa [LeanExe.build, hN] using h1
          omega
        rw [getElem!_pos b _ hlen]
        rfl
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [hlist] at hx
    rcases List.mem_append.mp hx with h | h
    · rw [List.eq_of_mem_replicate h]; norm_num
    · exact hb1 x h
  · rw [val, hlist, valL_replicate, ← val, hb2, hr]
    have e : (2 : ℕ) ^ k.toNat = 2 ^ (32 * (k.toNat / 32)) * 2 ^ (k.toNat % 32) := by
      rw [← pow_add, Nat.div_add_mod]
    rw [e, show (0 : UInt64).toNat = 0 from rfl, add_zero]
    ring
  · rw [build_size, hN, hb3]

#print axioms shl_spec

/-! ### `le` -/

theorem digit_split (v j : ℕ) :
    v / 2 ^ (32 * j) = v / 2 ^ (32 * (j + 1)) * 2 ^ 32 + v / 2 ^ (32 * j) % 2 ^ 32 := by
  rw [show 32 * (j + 1) = 32 * j + 32 by ring, pow_add, ← Nat.div_div_eq_div_mul]
  have := Nat.div_add_mod (v / 2 ^ (32 * j)) (2 ^ 32)
  linarith

theorem lt_of_div_lt (u v w : ℕ) (h : u / w < v / w) : u < v := by
  by_contra h'
  push Not at h'
  exact absurd (Nat.div_le_div_right (c := w) h') (not_le.mpr h)

theorem le_spec (a b : Array UInt64) (ha : Limbs a) (hb : Limbs b) (hsa : a.size < 2 ^ 32)
    (hsb : b.size < 2 ^ 32) : le a b = decide (val a ≤ val b) := by
  unfold le
  dsimp only
  have hN : (max a.size.toUInt64 b.size.toUInt64).toNat = max a.size b.size := by
    rw [UInt64.toNat_max, size_toUInt64 a (by omega), size_toUInt64 b (by omega)]
  generalize hn : max a.size.toUInt64 b.size.toUInt64 = n at hN ⊢
  have hloop := loop_inv n (0 : UInt64) (fun i s => cmpStep a b (n - 1 - i) s)
    (fun k s => (s = 0 ∧ val a / 2 ^ (32 * (n.toNat - k)) = val b / 2 ^ (32 * (n.toNat - k))) ∨
      (s = 1 ∧ val a < val b) ∨ (s = 2 ∧ val b < val a))
    (by
      left
      refine ⟨rfl, ?_⟩
      rw [Nat.sub_zero, hN]
      have h1 : val a < 2 ^ (32 * max a.size b.size) :=
        lt_of_lt_of_le (val_lt a ha) (Nat.pow_le_pow_right (by norm_num) (by omega))
      have h2 : val b < 2 ^ (32 * max a.size b.size) :=
        lt_of_lt_of_le (val_lt b hb) (Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [Nat.div_eq_of_lt h1, Nat.div_eq_of_lt h2])
    (by
      intro k s hk hP
      have hj : (n - 1 - UInt64.ofNat k).toNat = n.toNat - 1 - k := by
        have h1 : (UInt64.ofNat k).toNat = k := ofNat_toNat k (by omega)
        rw [UInt64.toNat_sub_of_le, UInt64.toNat_sub_of_le, h1]
        · rw [show (1 : UInt64).toNat = 1 from rfl]
        · rw [UInt64.le_iff_toNat_le, show (1 : UInt64).toNat = 1 from rfl]; omega
        · rw [UInt64.le_iff_toNat_le, h1, UInt64.toNat_sub_of_le _ _ (by
            rw [UInt64.le_iff_toNat_le, show (1 : UInt64).toNat = 1 from rfl]; omega)]
          rw [show (1 : UInt64).toNat = 1 from rfl]; omega
      unfold cmpStep
      rw [limb_eq a _ (by omega), limb_eq b _ (by omega)]
      rcases hP with ⟨h0, heq⟩ | ⟨h1, hlt⟩ | ⟨h2, hgt⟩
      · subst h0
        simp only [bne_self_eq_false, Bool.false_eq_true, ite_false]
        rw [hj]
        set j := n.toNat - 1 - k with hjdef
        have hjk : n.toNat - k = j + 1 := by omega
        have hjk' : n.toNat - (k + 1) = j := by omega
        rw [hjk] at heq
        have sa := digit_split (val a) j
        have sb := digit_split (val b) j
        rw [← getElem!_digit a ha j] at sa
        rw [← getElem!_digit b hb j] at sb
        by_cases hxy : a[j]! < b[j]!
        · rw [if_pos hxy]
          right; left
          refine ⟨rfl, lt_of_div_lt _ _ (2 ^ (32 * j)) ?_⟩
          rw [UInt64.lt_iff_toNat_lt] at hxy
          omega
        · rw [if_neg hxy]
          by_cases hyx : b[j]! < a[j]!
          · rw [if_pos hyx]
            right; right
            refine ⟨rfl, lt_of_div_lt _ _ (2 ^ (32 * j)) ?_⟩
            rw [UInt64.lt_iff_toNat_lt] at hyx
            omega
          · rw [if_neg hyx]
            left
            refine ⟨rfl, ?_⟩
            rw [hjk']
            rw [UInt64.lt_iff_toNat_lt] at hxy hyx
            omega
      · subst h1
        right; left
        exact ⟨by simp, hlt⟩
      · subst h2
        right; right
        exact ⟨by simp, hgt⟩)
  generalize LeanExe.loop n 0 _ = s at hloop ⊢
  rcases hloop with ⟨h0, heq⟩ | ⟨h1, hlt⟩ | ⟨h2, hgt⟩
  · rw [Nat.sub_self, Nat.mul_zero, pow_zero, Nat.div_one, Nat.div_one] at heq
    rw [h0, heq]; simp
  · rw [h1]; simp [hlt.le]
  · rw [h2]; simp [hgt]

/-! ### `sub` -/

theorem sub_spec (a b : Array UInt64) (ha : Limbs a) (hb : Limbs b) (hs : a.size < 2 ^ 32)
    (hsb64 : b.size < 2 ^ 64) (hle : val b ≤ val a) :
    Limbs (sub a b) ∧ val (sub a b) = val a - val b ∧ (sub a b).size = a.size := by
  unfold sub
  have hloop := loop_inv a.size.toUInt64 (LeanExe.build 0 fun _ => (0 : UInt64), (0 : UInt64))
    (fun i (s : Array UInt64 × UInt64) =>
      ((s.1.push ((a[i.toNat]! + 0x100000000 - limb b i - s.2) &&& 0xFFFFFFFF)),
        (1 : UInt64) - ((a[i.toNat]! + 0x100000000 - limb b i - s.2) >>> 32)))
    (fun k s => s.1.size = k ∧ Limbs s.1 ∧ s.2.toNat ≤ 1 ∧
      val s.1 + val b % 2 ^ (32 * k) = val a % 2 ^ (32 * k) + 2 ^ (32 * k) * s.2.toNat)
    ⟨size_empty, limbs_empty, by decide, by simp [val_empty, Nat.mod_one]⟩
    (by
      intro k s hk ⟨h1, h2, h3, h4⟩
      rw [size_toUInt64 a (by omega)] at hk
      rw [limb_eq b _ hsb64, ofNat_toNat k (by omega)]
      have hx := getElem!_lt a ha k
      have hy := getElem!_lt b hb k
      have hd : (a[k]! + 0x100000000 - b[k]! - s.2).toNat =
          a[k]!.toNat + 2 ^ 32 - b[k]!.toNat - s.2.toNat := by
        have e1 : (a[k]! + 0x100000000).toNat = a[k]!.toNat + 2 ^ 32 := by
          rw [UInt64.toNat_add, show (0x100000000 : UInt64).toNat = 2 ^ 32 from rfl]
          exact Nat.mod_eq_of_lt (by omega)
        have e2 : (a[k]! + 0x100000000 - b[k]!).toNat = a[k]!.toNat + 2 ^ 32 - b[k]!.toNat := by
          rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, e1]; omega), e1]
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, e2]; omega), e2]
      have hq : (a[k]! + 0x100000000 - b[k]! - s.2).toNat / 2 ^ 32 ≤ 1 := by
        rw [hd]; omega
      have hb' : ((1 : UInt64) - ((a[k]! + 0x100000000 - b[k]! - s.2) >>> 32)).toNat =
          1 - (a[k]! + 0x100000000 - b[k]! - s.2).toNat / 2 ^ 32 := by
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, shr32]; exact hq), shr32]
        rfl
      refine ⟨by simp [h1], limbs_push _ _ h2 (by rw [and_mask]; exact Nat.mod_lt _ (by norm_num)),
        by rw [hb']; omega, ?_⟩
      rw [val_push, and_mask, hb', h1, mod_succ (val a), mod_succ (val b),
        ← getElem!_digit a ha k, ← getElem!_digit b hb k]
      rw [show 32 * (k + 1) = 32 * k + 32 by ring, pow_add]
      generalize (a[k]! + 0x100000000 - b[k]! - s.2).toNat = d at hd hq
      have hdm := Nat.div_add_mod d (2 ^ 32)
      have key : s.2.toNat + d % 2 ^ 32 + b[k]!.toNat = a[k]!.toNat + 2 ^ 32 * (1 - d / 2 ^ 32) := by
        omega
      calc val s.1 + 2 ^ (32 * k) * (d % 2 ^ 32) + (val b % 2 ^ (32 * k) + 2 ^ (32 * k) * b[k]!.toNat)
          = (val s.1 + val b % 2 ^ (32 * k)) +
            2 ^ (32 * k) * (d % 2 ^ 32 + b[k]!.toNat) := by ring
        _ = val a % 2 ^ (32 * k) + 2 ^ (32 * k) * (s.2.toNat + d % 2 ^ 32 + b[k]!.toNat) := by
          rw [h4]; ring
        _ = _ := by rw [key]; ring)
  rw [size_toUInt64 a (by omega)] at hloop
  obtain ⟨h1, h2, h3, h4⟩ := hloop
  generalize LeanExe.loop _ _ _ = s at h1 h2 h3 h4 ⊢
  have hva := val_lt a ha
  have hvs := val_lt s.1 h2
  rw [h1] at hvs
  rw [Nat.mod_eq_of_lt hva, Nat.mod_eq_of_lt (lt_of_le_of_lt hle hva)] at h4
  refine ⟨h2, ?_, h1⟩
  have hw : s.2.toNat = 0 := by
    by_contra hw
    have : s.2.toNat = 1 := by omega
    rw [this] at h4
    omega
  rw [hw] at h4
  omega

/-! ### Bit lengths -/

theorem wordBits_spec (x : UInt64) : (wordBits x).toNat = Nat.size x.toNat := by
  unfold wordBits
  have hloop := loop_inv 64 (0 : UInt64) (fun i n => if x >>> i != 0 then i + 1 else n)
    (fun k n => n.toNat = min k (Nat.size x.toNat)) (by simp)
    (by
      intro k n hk hP
      have hk' : k < 64 := hk
      have hi : (UInt64.ofNat k).toNat = k := ofNat_toNat k (by omega)
      have hsh : (x >>> UInt64.ofNat k).toNat = x.toNat / 2 ^ k := by
        rw [UInt64.toNat_shiftRight, hi, Nat.mod_eq_of_lt hk', Nat.shiftRight_eq_div_pow]
      by_cases hc : (x >>> UInt64.ofNat k != 0) = true
      · simp only [hc, ite_true]
        have hne : x.toNat / 2 ^ k ≠ 0 := by
          intro h0; apply (bne_iff_ne.mp hc); apply UInt64.toNat_inj.mp; rw [hsh, h0]; rfl
        have hlt : k < Nat.size x.toNat := Nat.lt_size.mpr (by
          by_contra h; push Not at h; exact hne (Nat.div_eq_of_lt h))
        rw [UInt64.toNat_add, hi, show (1 : UInt64).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (by omega)]
        omega
      · simp only [Bool.not_eq_true] at hc
        simp only [hc, Bool.false_eq_true, ite_false]
        have he : x.toNat / 2 ^ k = 0 := by
          have := bne_eq_false_iff_eq.mp hc
          rw [← hsh, this]; rfl
        have hle : Nat.size x.toNat ≤ k := Nat.size_le.mpr ((Nat.div_eq_zero_iff_lt
          (by positivity)).mp he)
        omega)
  rw [hloop]
  have : Nat.size x.toNat ≤ 64 := Nat.size_le.mpr x.toNat_lt
  simp; omega

theorem size_add_shift (p d m : ℕ) (hp : p < 2 ^ m) (hd : 0 < d) :
    Nat.size (p + 2 ^ m * d) = m + Nat.size d := by
  have ht1 : d < 2 ^ Nat.size d := Nat.lt_size_self d
  have ht0 : 1 ≤ Nat.size d := by
    rcases Nat.eq_zero_or_pos (Nat.size d) with h | h
    · rw [Nat.size_eq_zero.mp h] at hd; omega
    · exact h
  have ht2 : 2 ^ (Nat.size d - 1) ≤ d := Nat.lt_size.mp (by omega)
  apply le_antisymm
  · apply Nat.size_le.mpr
    rw [pow_add]
    have : d + 1 ≤ 2 ^ Nat.size d := ht1
    nlinarith
  · have : m + Nat.size d - 1 < Nat.size (p + 2 ^ m * d) := by
      apply Nat.lt_size.mpr
      rw [show m + Nat.size d - 1 = m + (Nat.size d - 1) by omega, pow_add]
      nlinarith
    omega

theorem bitLen_spec (a : Array UInt64) (ha : Limbs a) (hs : a.size < 2 ^ 32) :
    (bitLen a).toNat = Nat.size (val a) := by
  unfold bitLen
  have hloop := loop_inv a.size.toUInt64 (0 : UInt64)
    (fun i s => if a[i.toNat]! != 0 then 32 * i + wordBits a[i.toNat]! else s)
    (fun k s => s.toNat = Nat.size (val a % 2 ^ (32 * k))) (by simp [Nat.mod_one, Nat.size_zero])
    (by
      intro k s hk hP
      rw [size_toUInt64 a (by omega)] at hk
      have hi : (UInt64.ofNat k).toNat = k := ofNat_toNat k (by omega)
      simp only [hi]
      rw [mod_succ, ← getElem!_digit a ha k]
      have hx := getElem!_lt a ha k
      by_cases hc : (a[k]! != 0) = true
      · simp only [hc, ite_true]
        have hpos : 0 < a[k]!.toNat := by
          rcases Nat.eq_zero_or_pos a[k]!.toNat with h | h
          · exfalso; apply bne_iff_ne.mp hc; exact UInt64.toNat_inj.mp (by rw [h]; rfl)
          · exact h
        rw [size_add_shift _ _ _ (Nat.mod_lt _ (by positivity)) hpos]
        have hw := wordBits_spec a[k]!
        have hw64 : (wordBits a[k]!).toNat ≤ 64 := by
          rw [hw]; exact Nat.size_le.mpr (by omega)
        rw [UInt64.toNat_add, UInt64.toNat_mul, hi, hw,
          show (32 : UInt64).toNat = 32 from rfl]
        rw [hw] at hw64
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      · simp only [Bool.not_eq_true] at hc
        simp only [hc, Bool.false_eq_true, ite_false]
        have h0 : a[k]!.toNat = 0 := by
          have := bne_eq_false_iff_eq.mp hc; rw [this]; rfl
        rw [h0, Nat.mul_zero, Nat.add_zero]
        exact hP)
  rw [size_toUInt64 a (by omega), Nat.mod_eq_of_lt (val_lt a ha)] at hloop
  exact hloop

#print axioms le_spec
#print axioms sub_spec
#print axioms wordBits_spec
#print axioms bitLen_spec

end Verified.Examples.UscaleTheorem
