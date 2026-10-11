import Verified.Examples.TrigWords
import Verified.Examples.TrigWindows

/-!
The integer stages of `Trig.remLarge`.  `stage1` forms the low 192 bits `V` of the product of the
significand and the 192-bit window of `2/π`, `stage2` splits `V` into the quadrant `q` and the
190-bit fraction, negated when it is at least one half, `stage3` normalizes that fraction and
multiplies it by `π/2`, and `stage4` cuts the 128-bit product into the 53-bit words `hi` and `lo`.
`remLarge_eq` states that `Trig.remLarge` is the composition of these stages with `stage5`, which
forms `y0` and `y1` in floating point.
-/

namespace Verified.Examples.TrigLargeInt

open TrigWords TrigPi

set_option exponentiation.threshold 4096

def stage1 (inv : Array UInt64) (b : UInt64) : UInt64 × UInt64 × UInt64 :=
  let m := (b &&& 0xFFFFFFFFFFFFF) ||| 0x10000000000000
  let g := ((b >>> 52) &&& 0x7FF) - 1013
  let d := g >>> 6
  let s := g &&& 63
  let (h2, l2) := Trig.mul64 (Trig.window inv (d + 2) s) m
  let (h1, l1) := Trig.mul64 (Trig.window inv (d + 1) s) m
  let w1 := h2 + l1
  let w2 := h1 + Trig.window inv d s * m + (if w1 < h2 then 1 else 0)
  (w2, w1, l2)

def stage2 (w2 w1 l2 : UInt64) : UInt64 × Bool × UInt64 × UInt64 × UInt64 :=
  let q := w2 >>> 62
  let f2 := w2 &&& 0x3FFFFFFFFFFFFFFF
  let up := f2 >>> 61 == 1
  let (a2, a1, a0) := if up then
      ((0 - f2 - (if w1 != 0 || l2 != 0 then 1 else 0)) &&& 0x3FFFFFFFFFFFFFFF,
        0 - w1 - (if l2 != 0 then 1 else 0), 0 - l2)
    else (f2, w1, l2)
  (q, up, a2, a1, a0)

def lzOf (a2 a1 a0 : UInt64) : UInt64 :=
  if a2 != 0 then Trig.clz64 a2 else if a1 != 0 then 64 + Trig.clz64 a1 else 128 + Trig.clz64 a0

def stage3 (half : Array UInt64) (a2 a1 a0 : UInt64) : UInt64 × UInt64 × UInt64 :=
  let lz := lzOf a2 a1 a0
  let (t1, t0) := Trig.shiftTop a2 a1 a0 lz
  let (u1, u0) := Trig.mulTop t1 t0 half[(0 : UInt64).toNat]! half[(1 : UInt64).toNat]!
  (lz, u1, u0)

def stage4 (u1 u0 : UInt64) : UInt64 × UInt64 × UInt64 :=
  let k := if u1 >>> 63 == 1 then (63 : UInt64) else 62
  (k, u1 >>> (k - 52), ((u1 <<< (105 - k)) ||| (u0 >>> (k - 41))) &&& 0x1FFFFFFFFFFFFF)

def stage5 (k hi lo lz : UInt64) : Float × Float :=
  let a := hi.toFloat * Float.ofBits ((k + 910 - lz) <<< 52)
  let c := lo.toFloat * Float.ofBits ((k + 857 - lz) <<< 52)
  let y0 := a + c
  (y0, c - (y0 - a))

set_option maxHeartbeats 4000000 in
theorem remLarge_eq (inv half : Array UInt64) (x : Float) :
    Trig.remLarge inv half x =
      (let (w2, w1, l2) := stage1 inv x.toBits
      let (q, up, a2, a1, a0) := stage2 w2 w1 l2
      let (lz, u1, u0) := stage3 half a2 a1 a0
      let (k, hi, lo) := stage4 u1 u0
      let (y0, y1) := stage5 k hi lo lz
      if up then (q + 1, -y0, -y1) else (q, y0, y1)) := by
  unfold Trig.remLarge stage1 stage2 stage3 stage4 stage5 lzOf
  rfl

theorem mant_toNat (b : UInt64) :
    ((b &&& 0xFFFFFFFFFFFFF) ||| 0x10000000000000).toNat = b.toNat % 2 ^ 52 + 2 ^ 52 := by
  rw [UInt64.toNat_or, UInt64.toNat_and]
  have h1 : (0xFFFFFFFFFFFFF : UInt64).toNat = 2 ^ 52 - 1 := rfl
  have h2 : (0x10000000000000 : UInt64).toNat = 1 <<< 52 := rfl
  rw [h1, h2, Nat.and_two_pow_sub_one_eq_mod, Nat.or_comm,
    ← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (by norm_num)), Nat.shiftLeft_eq, Nat.add_comm]
  norm_num

theorem exponentField_eq (b : UInt64) :
    ((b >>> 52) &&& 0x7FF) = UInt64.ofNat (b.toNat / 2 ^ 52 % 2 ^ 11) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, shr_toNat]
  have h1 : (0x7FF : UInt64).toNat = 2 ^ 11 - 1 := rfl
  have h2 : (52 : UInt64).toNat % 64 = 52 := rfl
  rw [h1, h2, Nat.and_two_pow_sub_one_eq_mod, UInt64.toNat_ofNat_of_lt']
  exact lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)

/-- `stage1` computes the low 192 bits of the significand times the window of `2/π`. -/
theorem stage1_spec (b : UInt64) (hE1 : 1043 ≤ b.toNat / 2 ^ 52 % 2 ^ 11)
    (hE2 : b.toNat / 2 ^ 52 % 2 ^ 11 < 2047) :
    (stage1 Trig.invPi b).1.toNat * 2 ^ 128 + (stage1 Trig.invPi b).2.1.toNat * 2 ^ 64 +
        (stage1 Trig.invPi b).2.2.toNat =
      (b.toNat % 2 ^ 52 + 2 ^ 52) *
        (tableNum * 2 ^ (b.toNat / 2 ^ 52 % 2 ^ 11 - 1013) / 2 ^ 1088 % 2 ^ 192) % 2 ^ 192 := by
  have hw := TrigWindows.windows_eq _ hE2 hE1
  have hm := mant_toNat b
  unfold stage1
  dsimp only
  rw [exponentField_eq]
  generalize b.toNat / 2 ^ 52 % 2 ^ 11 = E at hw ⊢
  rw [← hm]
  generalize (b &&& 0xFFFFFFFFFFFFF) ||| 0x10000000000000 = m
  generalize Trig.window Trig.invPi ((UInt64.ofNat E - 1013) >>> 6)
    ((UInt64.ofNat E - 1013) &&& 63) = W0 at hw ⊢
  generalize Trig.window Trig.invPi ((UInt64.ofNat E - 1013) >>> 6 + 1)
    ((UInt64.ofNat E - 1013) &&& 63) = W1 at hw ⊢
  generalize Trig.window Trig.invPi ((UInt64.ofNat E - 1013) >>> 6 + 2)
    ((UInt64.ofNat E - 1013) &&& 63) = W2 at hw ⊢
  rw [← hw]
  have m2 := mul64_spec W2 m
  have m1 := mul64_spec W1 m
  generalize Trig.mul64 W2 m = q2 at m2 ⊢
  generalize Trig.mul64 W1 m = q1 at m1 ⊢
  obtain ⟨h2, l2⟩ := q2
  obtain ⟨h1, l1⟩ := q1
  dsimp only at m1 m2 ⊢
  simp only [UInt64.toNat_add, UInt64.toNat_mul, carry_flag]
  have hexp : m.toNat * (W0.toNat * 2 ^ 128 + W1.toNat * 2 ^ 64 + W2.toNat) =
      W0.toNat * m.toNat * 2 ^ 128 + (W1.toNat * m.toNat) * 2 ^ 64 + W2.toNat * m.toNat := by
    ring
  rw [hexp, ← m1, ← m2]
  have hH1 := h1.toNat_lt
  have hL1 := l1.toNat_lt
  have hH2 := h2.toNat_lt
  have hL2 := l2.toNat_lt
  generalize W0.toNat * m.toNat = P at *
  generalize h1.toNat = H1 at *
  generalize l1.toNat = L1 at *
  generalize h2.toNat = H2 at *
  generalize l2.toNat = L2 at *
  clear * - hH1 hL1 hH2 hL2
  simp only [Nat.reducePow] at *
  omega

/-- The 190-bit negation of a nonzero fraction held in three words. -/
theorem neg3_spec (f2 w1 l2 : UInt64) (hf2 : f2.toNat < 2 ^ 62)
    (hpos : 0 < f2.toNat * 2 ^ 128 + w1.toNat * 2 ^ 64 + l2.toNat) :
    ((0 - f2 - (if (w1 != 0 || l2 != 0) = true then 1 else 0)) &&& 0x3FFFFFFFFFFFFFFF).toNat <
        2 ^ 62 ∧
      ((0 - f2 - (if (w1 != 0 || l2 != 0) = true then 1 else 0)) &&& 0x3FFFFFFFFFFFFFFF).toNat *
          2 ^ 128 + (0 - w1 - (if (l2 != 0) = true then 1 else 0)).toNat * 2 ^ 64 +
        (0 - l2).toNat =
        2 ^ 190 - (f2.toNat * 2 ^ 128 + w1.toNat * 2 ^ 64 + l2.toNat) := by
  have hw1 := w1.toNat_lt
  have hl2 := l2.toNat_lt
  have hm : (0x3FFFFFFFFFFFFFFF : UInt64).toNat = 2 ^ 62 - 1 := rfl
  by_cases h1 : w1 = 0 <;> by_cases h2 : l2 = 0
  · subst h1; subst h2
    simp only [bne_self_eq_false, Bool.or_false, Bool.false_eq_true, ite_false, UInt64.toNat_and,
      UInt64.toNat_sub, hm, Nat.and_two_pow_sub_one_eq_mod, UInt64.reduceToNat] at hpos ⊢
    omega
  · subst h1
    have h2' : (l2 != 0) = true := bne_iff_ne.mpr h2
    have h2n : l2.toNat ≠ 0 := fun h => h2 (UInt64.toNat_inj.mp (by rw [h]; rfl))
    simp only [bne_self_eq_false, Bool.false_or, h2', ite_true, UInt64.toNat_and,
      UInt64.toNat_sub, hm, Nat.and_two_pow_sub_one_eq_mod, UInt64.reduceToNat] at hpos ⊢
    omega
  · subst h2
    have h1' : (w1 != 0) = true := bne_iff_ne.mpr h1
    have h1n : w1.toNat ≠ 0 := fun h => h1 (UInt64.toNat_inj.mp (by rw [h]; rfl))
    simp only [bne_self_eq_false, Bool.or_false, h1', ite_true, ite_false, Bool.false_eq_true,
      UInt64.toNat_and, UInt64.toNat_sub, hm, Nat.and_two_pow_sub_one_eq_mod,
      UInt64.reduceToNat] at hpos ⊢
    omega
  · have h1' : (w1 != 0) = true := bne_iff_ne.mpr h1
    have h2' : (l2 != 0) = true := bne_iff_ne.mpr h2
    have h1n : w1.toNat ≠ 0 := fun h => h1 (UInt64.toNat_inj.mp (by rw [h]; rfl))
    have h2n : l2.toNat ≠ 0 := fun h => h2 (UInt64.toNat_inj.mp (by rw [h]; rfl))
    simp only [h1', h2', Bool.or_true, ite_true, UInt64.toNat_and, UInt64.toNat_sub, hm,
      Nat.and_two_pow_sub_one_eq_mod, UInt64.reduceToNat] at hpos ⊢
    omega

/-- `stage2` splits `V` into the quadrant and the fraction, negating a fraction of at least one
half. -/
theorem stage2_spec (w2 w1 l2 : UInt64) :
    (stage2 w2 w1 l2).1.toNat = (w2.toNat * 2 ^ 128 + w1.toNat * 2 ^ 64 + l2.toNat) / 2 ^ 190 ∧
      (stage2 w2 w1 l2).2.2.1.toNat < 2 ^ 62 ∧
      ((stage2 w2 w1 l2).2.1 = true ↔
        2 ^ 189 ≤ (w2.toNat * 2 ^ 128 + w1.toNat * 2 ^ 64 + l2.toNat) % 2 ^ 190) ∧
      (stage2 w2 w1 l2).2.2.1.toNat * 2 ^ 128 + (stage2 w2 w1 l2).2.2.2.1.toNat * 2 ^ 64 +
          (stage2 w2 w1 l2).2.2.2.2.toNat =
        (if (stage2 w2 w1 l2).2.1 then
          2 ^ 190 - (w2.toNat * 2 ^ 128 + w1.toNat * 2 ^ 64 + l2.toNat) % 2 ^ 190
        else (w2.toNat * 2 ^ 128 + w1.toNat * 2 ^ 64 + l2.toNat) % 2 ^ 190) := by
  have hw2 := w2.toNat_lt
  have hw1 := w1.toNat_lt
  have hl2 := l2.toNat_lt
  have hq : (w2 >>> 62).toNat = w2.toNat / 2 ^ 62 := by
    rw [shr_toNat]
    rfl
  have hf : (w2 &&& 0x3FFFFFFFFFFFFFFF).toNat = w2.toNat % 2 ^ 62 := by
    rw [UInt64.toNat_and]
    exact land_62 _
  have hup : ((w2 &&& 0x3FFFFFFFFFFFFFFF) >>> 61 == 1) = true ↔
      2 ^ 61 ≤ w2.toNat % 2 ^ 62 := by
    rw [beq_iff_eq, ← UInt64.toNat_inj, shr_toNat, hf]
    simp only [UInt64.reduceToNat, Nat.reduceMod]
    omega
  unfold stage2
  dsimp only
  by_cases hu : ((w2 &&& 0x3FFFFFFFFFFFFFFF) >>> 61 == 1) = true
  · rw [ite_eq_left hu]
    dsimp only
    have hge := hup.mp hu
    have hpos : 0 < (w2 &&& 0x3FFFFFFFFFFFFFFF).toNat * 2 ^ 128 + w1.toNat * 2 ^ 64 +
        l2.toNat := by
      rw [hf]
      omega
    have hn := neg3_spec (w2 &&& 0x3FFFFFFFFFFFFFFF) w1 l2 (by rw [hf]; omega) hpos
    rw [hf] at hn
    refine ⟨by rw [hq]; omega, hn.1, ⟨fun _ => by omega, fun _ => hu⟩, ?_⟩
    rw [ite_eq_left hu, hn.2]
    omega
  · rw [ite_eq_right hu]
    dsimp only
    have hlt := mt hup.mpr hu
    refine ⟨by rw [hq]; omega, by rw [hf]; omega, ⟨fun h => absurd h hu, fun h => ?_⟩, ?_⟩
    · exfalso
      omega
    · rw [ite_eq_right hu, hf]
      omega

/-- The normalization bounds for one word with `clz64`: a word below `2 ^ 64` shifted by its
leading-zero count, followed by `r` lower bits, lies in `[2 ^ (63 + j), 2 ^ (64 + j))`. -/
theorem lead_bounds (a c R j : Nat) (hc : 2 ^ 63 ≤ a * 2 ^ c) (hc' : a * 2 ^ c < 2 ^ 64)
    (hR : R < 2 ^ j) :
    2 ^ (63 + j) ≤ (a * 2 ^ j + R) * 2 ^ c ∧ (a * 2 ^ j + R) * 2 ^ c < 2 ^ (64 + j) := by
  have hP : 0 < 2 ^ c := by positivity
  have hcle : c ≤ 64 := by
    by_contra h
    have h1 : 2 ^ 65 ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) (by omega)
    have ha : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with h0 | h0
      · rw [h0] at hc
        simp at hc
      · exact h0
    have : 2 ^ 65 ≤ a * 2 ^ c := le_trans h1 (Nat.le_mul_of_pos_left _ ha)
    omega
  have hQ : 2 ^ (64 - c) * 2 ^ c = 2 ^ 64 := by rw [← pow_add, Nat.sub_add_cancel hcle]
  have ha : a < 2 ^ (64 - c) := by
    rw [← hQ] at hc'
    exact Nat.lt_of_mul_lt_mul_right hc'
  have ha1 : (a + 1) * 2 ^ c ≤ 2 ^ 64 := by
    rw [← hQ]
    exact Nat.mul_le_mul_right _ ha
  constructor
  · calc 2 ^ (63 + j) = 2 ^ 63 * 2 ^ j := by rw [pow_add]
      _ ≤ a * 2 ^ c * 2 ^ j := Nat.mul_le_mul_right _ hc
      _ = a * 2 ^ j * 2 ^ c := by ring
      _ ≤ (a * 2 ^ j + R) * 2 ^ c := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  · calc (a * 2 ^ j + R) * 2 ^ c < (a * 2 ^ j + 2 ^ j) * 2 ^ c :=
          Nat.mul_lt_mul_of_pos_right (by omega) hP
      _ = (a + 1) * 2 ^ c * 2 ^ j := by ring
      _ ≤ 2 ^ 64 * 2 ^ j := Nat.mul_le_mul_right _ ha1
      _ = 2 ^ (64 + j) := by rw [pow_add]

/-- `lzOf` normalizes a nonzero 190-bit fraction to `[2 ^ 191, 2 ^ 192)`. -/
theorem lz_spec (a2 a1 a0 : UInt64)
    (hA : 0 < a2.toNat * 2 ^ 128 + a1.toNat * 2 ^ 64 + a0.toNat) :
    (lzOf a2 a1 a0).toNat < 192 ∧
      2 ^ 191 ≤ (a2.toNat * 2 ^ 128 + a1.toNat * 2 ^ 64 + a0.toNat) * 2 ^ (lzOf a2 a1 a0).toNat ∧
      (a2.toNat * 2 ^ 128 + a1.toNat * 2 ^ 64 + a0.toNat) * 2 ^ (lzOf a2 a1 a0).toNat <
        2 ^ 192 := by
  have h1 := a1.toNat_lt
  have h0 := a0.toNat_lt
  unfold lzOf
  by_cases z2 : a2 = 0
  · have z2' : (a2 != 0) = false := by rw [z2]; rfl
    rw [z2', ite_eq_right (by simp)]
    have hz2 : a2.toNat = 0 := by rw [z2]; rfl
    rw [hz2, Nat.zero_mul, Nat.zero_add] at hA ⊢
    by_cases z1 : a1 = 0
    · have z1' : (a1 != 0) = false := by rw [z1]; rfl
      rw [z1', ite_eq_right (by simp)]
      have hz1 : a1.toNat = 0 := by rw [z1]; rfl
      rw [hz1, Nat.zero_mul, Nat.zero_add] at hA ⊢
      obtain ⟨c64, clo, chi⟩ := TrigWords.clz64_spec a0 (by omega)
      have hadd : (128 + Trig.clz64 a0).toNat = 128 + (Trig.clz64 a0).toNat := by
        simp only [UInt64.toNat_add, UInt64.reduceToNat]
        omega
      rw [hadd]
      have hb := lead_bounds a0.toNat (Trig.clz64 a0).toNat 0 128 clo chi (by positivity)
      have e : a0.toNat * 2 ^ (128 + (Trig.clz64 a0).toNat) =
          (a0.toNat * 2 ^ 128 + 0) * 2 ^ (Trig.clz64 a0).toNat := by
        rw [Nat.add_zero, pow_add, Nat.mul_assoc]
      rw [e]
      exact ⟨by omega, (by norm_num : (2 : Nat) ^ 191 = 2 ^ (63 + 128)).trans_le hb.1,
        hb.2.trans_eq (by norm_num)⟩
    · have z1' : (a1 != 0) = true := bne_iff_ne.mpr z1
      rw [z1', ite_eq_left rfl]
      have hz1 : a1.toNat ≠ 0 := fun h => z1 (UInt64.toNat_inj.mp (by rw [h]; rfl))
      obtain ⟨c64, clo, chi⟩ := TrigWords.clz64_spec a1 hz1
      have hadd : (64 + Trig.clz64 a1).toNat = 64 + (Trig.clz64 a1).toNat := by
        simp only [UInt64.toNat_add, UInt64.reduceToNat]
        omega
      rw [hadd]
      have hb := lead_bounds a1.toNat (Trig.clz64 a1).toNat a0.toNat 64 clo chi h0
      have e : (a1.toNat * 2 ^ 64 + a0.toNat) * 2 ^ (64 + (Trig.clz64 a1).toNat) =
          (a1.toNat * 2 ^ 64 + a0.toNat) * 2 ^ (Trig.clz64 a1).toNat * 2 ^ 64 := by
        rw [pow_add, Nat.mul_comm (2 ^ 64), Nat.mul_assoc]
      rw [e]
      refine ⟨by omega, ?_, ?_⟩
      · calc 2 ^ 191 = 2 ^ (63 + 64) * 2 ^ 64 := by norm_num
          _ ≤ _ := Nat.mul_le_mul_right _ hb.1
      · calc _ < 2 ^ (64 + 64) * 2 ^ 64 := Nat.mul_lt_mul_of_pos_right hb.2 (by positivity)
          _ = 2 ^ 192 := by norm_num
  · have z2' : (a2 != 0) = true := bne_iff_ne.mpr z2
    rw [z2', ite_eq_left rfl]
    have hz2 : a2.toNat ≠ 0 := fun h => z2 (UInt64.toNat_inj.mp (by rw [h]; rfl))
    obtain ⟨c64, clo, chi⟩ := TrigWords.clz64_spec a2 hz2
    have hb := lead_bounds a2.toNat (Trig.clz64 a2).toNat (a1.toNat * 2 ^ 64 + a0.toNat) 128
      clo chi (by omega)
    rw [show a2.toNat * 2 ^ 128 + a1.toNat * 2 ^ 64 + a0.toNat =
      a2.toNat * 2 ^ 128 + (a1.toNat * 2 ^ 64 + a0.toNat) by ring]
    refine ⟨by omega, ?_, ?_⟩
    · calc 2 ^ 191 = 2 ^ (63 + 128) := by norm_num
        _ ≤ _ := hb.1
    · calc _ < 2 ^ (64 + 128) := hb.2
        _ = 2 ^ 192 := by norm_num

theorem half_words :
    (Trig.halfPi[(0 : UInt64).toNat]!).toNat * 2 ^ 64 + (Trig.halfPi[(1 : UInt64).toNat]!).toNat =
      halfNum := by
  decide +kernel

/-- `stage3` multiplies the normalized fraction by `π/2`. -/
theorem stage3_spec (a2 a1 a0 : UInt64)
    (hA : 0 < a2.toNat * 2 ^ 128 + a1.toNat * 2 ^ 64 + a0.toNat) :
    (stage3 Trig.halfPi a2 a1 a0).1 = lzOf a2 a1 a0 ∧
      (stage3 Trig.halfPi a2 a1 a0).2.1.toNat * 2 ^ 64 + (stage3 Trig.halfPi a2 a1 a0).2.2.toNat =
        (a2.toNat * 2 ^ 128 + a1.toNat * 2 ^ 64 + a0.toNat) * 2 ^ (lzOf a2 a1 a0).toNat /
          2 ^ 64 * halfNum / 2 ^ 128 := by
  obtain ⟨hlz, -, hhi⟩ := lz_spec a2 a1 a0 hA
  have hs := TrigWords.shiftTop_spec a2 a1 a0 (lzOf a2 a1 a0) hlz hhi
  unfold stage3
  dsimp only
  refine ⟨rfl, ?_⟩
  generalize Trig.shiftTop a2 a1 a0 (lzOf a2 a1 a0) = t at hs ⊢
  obtain ⟨t1, t0⟩ := t
  dsimp only at hs ⊢
  have hm := TrigWords.mulTop_spec t1 t0 Trig.halfPi[(0 : UInt64).toNat]!
    Trig.halfPi[(1 : UInt64).toNat]!
  rw [half_words, hs] at hm
  exact hm

/-- `stage4` cuts the 128-bit product `U` into `hi`, its top 53 bits, and `lo`, the next 53. -/
theorem stage4_spec (u1 u0 : UInt64) (hU : 2 ^ 126 ≤ u1.toNat * 2 ^ 64 + u0.toNat) :
    ((stage4 u1 u0).1 = 63 ∧ 2 ^ 127 ≤ u1.toNat * 2 ^ 64 + u0.toNat ∨
        (stage4 u1 u0).1 = 62 ∧ u1.toNat * 2 ^ 64 + u0.toNat < 2 ^ 127) ∧
      (stage4 u1 u0).2.1.toNat =
        (u1.toNat * 2 ^ 64 + u0.toNat) / 2 ^ ((stage4 u1 u0).1.toNat + 12) ∧
      (stage4 u1 u0).2.2.toNat =
        (u1.toNat * 2 ^ 64 + u0.toNat) / 2 ^ ((stage4 u1 u0).1.toNat - 41) % 2 ^ 53 := by
  have h1 := u1.toNat_lt
  have h0 := u0.toNat_lt
  have hmask : ∀ z : UInt64, (z &&& 0x1FFFFFFFFFFFFF).toNat = z.toNat % 2 ^ 53 := fun z => by
    rw [UInt64.toNat_and]
    exact land_53 _
  unfold stage4
  dsimp only
  by_cases hk : (u1 >>> 63 == 1) = true
  · rw [ite_eq_left hk]
    have hk' : 2 ^ 63 ≤ u1.toNat := by
      rw [beq_iff_eq, ← UInt64.toNat_inj, shr_toNat] at hk
      simp only [UInt64.reduceToNat, Nat.reduceMod] at hk
      omega
    have hor := or_shift u1 u0 42 (by decide) (by decide)
    simp only [UInt64.reduceSub, UInt64.reduceToNat] at hor ⊢
    rw [hmask, hor, shr_toNat]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub]
    clear hk hor hmask
    simp only [Nat.reducePow] at *
    refine ⟨Or.inl ⟨trivial, by omega⟩, by omega, by omega⟩
  · rw [ite_eq_right hk]
    have hk' : u1.toNat < 2 ^ 63 := by
      rw [beq_iff_eq, ← UInt64.toNat_inj, shr_toNat] at hk
      simp only [UInt64.reduceToNat, Nat.reduceMod] at hk
      omega
    have hor := or_shift u1 u0 43 (by decide) (by decide)
    simp only [UInt64.reduceSub, UInt64.reduceToNat] at hor ⊢
    rw [hmask, hor, shr_toNat]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub]
    clear hk hor hmask
    simp only [Nat.reducePow] at *
    refine ⟨Or.inr ⟨trivial, by omega⟩, by omega, by omega⟩

#print axioms stage4_spec
#print axioms lead_bounds
#print axioms lz_spec
#print axioms stage3_spec
#print axioms neg3_spec
#print axioms stage2_spec

#print axioms remLarge_eq
#print axioms mant_toNat
#print axioms exponentField_eq
#print axioms stage1_spec

end Verified.Examples.TrigLargeInt
