import Library.Numerics.Arithmetic.Fma.FmaDecode

/-!
`Fma.fmaBits` written with named parts (`fmaBits_eq`): `sigWord` and `expWord` decode an operand,
`product` forms the normalized product of the significands of `a` and `b` with its scale, `addend`
the normalized significand of `c` with its scale, and `combine` aligns, adds, and rounds them.
`product_spec` and `addend_spec` state the parts as natural numbers: the product of the significands
shifted left by `S`, with its highest bit at 125 and bits 0 to 19 clear, and its scale
`w = mexp a + mexp b + 250 - S`, and the addend likewise with `w = mexp c + 1325 - S`.
-/

namespace Library.Numerics.Arithmetic.Fma.FmaParts
open Verified.Examples FmaWords FmaDecode

/-- The significand word of an operand. -/
def sigWord (x : UInt64) : UInt64 :=
  if (x >>> 52) &&& 0x7FF == 0 then x &&& 0xFFFFFFFFFFFFF
  else (x &&& 0xFFFFFFFFFFFFF) ||| 0x10000000000000

/-- The exponent word of an operand, 1 for a subnormal one. -/
def expWord (x : UInt64) : UInt64 :=
  if (x >>> 52) &&& 0x7FF == 0 then 1 else (x >>> 52) &&& 0x7FF

/-- The normalized product of the significands of `a` and `b`, as a pair, with its scale. -/
def product (a b : UInt64) : UInt64 × UInt64 × UInt64 :=
  let (ph, pl) := Fma.mul128 (sigWord a) (sigWord b)
  let shiftP := 125 - Fma.msb128 ph pl
  let (ph, pl) := Fma.shl128 ph pl shiftP
  (ph, pl, expWord a + expWord b + 250 - shiftP)

/-- The normalized significand of `c`, as a pair, with its scale. -/
def addend (c : UInt64) : UInt64 × UInt64 × UInt64 :=
  let shiftC := 125 - Fma.msb64 (sigWord c)
  let (ch, cl) := Fma.shl128 0 (sigWord c) shiftC
  (ch, cl, expWord c + 1325 - shiftC)

/-- The alignment, sum, and rounding of `x` (at scale `wX`, sign `sX`) and `y`, with `x` the larger
in magnitude. -/
def tail (sX sY xh xl wX yh yl wY : UInt64) : UInt64 :=
  let (yh, yl) := Fma.sticky128 yh yl (wX - wY)
  let (h, l) := if sX == sY then Fma.add128 xh xl yh yl else Fma.sub128 xh xl yh yl
  if h == 0 && l == 0 then 0 else Fma.roundPack sX wX h l

/-- The sum of the product and the addend, rounded. -/
def combine (sp sc ph pl wP ch cl wC : UInt64) : UInt64 :=
  let first := wP > wC || (wP == wC && !Fma.lt128 ph pl ch cl)
  let (xh, xl, wX, sX) := if first then (ph, pl, wP, sp) else (ch, cl, wC, sc)
  let (yh, yl, wY, sY) := if first then (ch, cl, wC, sc) else (ph, pl, wP, sp)
  tail sX sY xh xl wX yh yl wY

theorem combine_eq (sp sc ph pl wP ch cl wC : UInt64) : combine sp sc ph pl wP ch cl wC =
    if wP > wC || (wP == wC && !Fma.lt128 ph pl ch cl) then tail sp sc ph pl wP ch cl wC
    else tail sc sp ch cl wC ph pl wP := by
  unfold combine
  dsimp only
  split_ifs <;> rfl

theorem fmaBits_eq (a b c : UInt64) : Fma.fmaBits a b c =
    if (a >>> 52) &&& 0x7FF == 0x7FF && a &&& 0xFFFFFFFFFFFFF != 0 then a ||| 0x8000000000000
    else if (b >>> 52) &&& 0x7FF == 0x7FF && b &&& 0xFFFFFFFFFFFFF != 0 then
      b ||| 0x8000000000000
    else if (c >>> 52) &&& 0x7FF == 0x7FF && c &&& 0xFFFFFFFFFFFFF != 0 then
      c ||| 0x8000000000000
    else if (a >>> 52) &&& 0x7FF == 0x7FF || (b >>> 52) &&& 0x7FF == 0x7FF then
      if a <<< 1 == 0 || b <<< 1 == 0 ||
          ((c >>> 52) &&& 0x7FF == 0x7FF && c >>> 63 != (a ^^^ b) >>> 63) then
        0x7FF8000000000000
      else (((a ^^^ b) >>> 63) <<< 63) ||| 0x7FF0000000000000
    else if (c >>> 52) &&& 0x7FF == 0x7FF then c
    else if a <<< 1 == 0 || b <<< 1 == 0 then
      if c <<< 1 == 0 then (((a ^^^ b) >>> 63) &&& (c >>> 63)) <<< 63 else c
    else if c <<< 1 == 0 then
      Fma.roundPack ((a ^^^ b) >>> 63) (product a b).2.2 (product a b).1 (product a b).2.1
    else
      combine ((a ^^^ b) >>> 63) (c >>> 63) (product a b).1 (product a b).2.1 (product a b).2.2
        (addend c).1 (addend c).2.1 (addend c).2.2 := by
  unfold Fma.fmaBits product addend combine tail sigWord expWord
  dsimp only

theorem sigWord_toNat (x : UInt64) : (sigWord x).toNat = msig x := msig_bits x

theorem expWord_toNat (x : UInt64) : (expWord x).toNat = mexp x := mexp_bits x

/-- The normalized product of two nonzero significands. -/
theorem product_spec (a b : UInt64) (ha : Wasm.IEEE64.scaledMagnitude a ≠ 0)
    (hb : Wasm.IEEE64.scaledMagnitude b ≠ 0) (haf : CodeLib.IEEE64.Finite a)
    (hbf : CodeLib.IEEE64.Finite b) :
    ∃ S : ℕ, pair (product a b).1 (product a b).2.1 = msig a * msig b * 2 ^ S ∧
      (product a b).2.2.toNat + S = mexp a + mexp b + 250 ∧
      2 ^ 125 ≤ pair (product a b).1 (product a b).2.1 ∧
      pair (product a b).1 (product a b).2.1 < 2 ^ 126 ∧
      pair (product a b).1 (product a b).2.1 % 2 ^ 20 = 0 ∧
      (product a b).2.2.toNat < 2 ^ 32 := by
  have hA := msig_pos a ha
  have hB := msig_pos b hb
  have hA53 := msig_lt a
  have hB53 := msig_lt b
  have hea := mexp_le a haf
  have heb := mexp_le b hbf
  have hea1 := mexp_pos a
  have heb1 := mexp_pos b
  have hm := mul128_spec (sigWord a) (sigWord b) (by rw [sigWord_toNat]; exact hA53)
    (by rw [sigWord_toNat]; exact hB53)
  rw [sigWord_toNat, sigWord_toNat] at hm
  have hw1 : (expWord a + expWord b + 250).toNat = mexp a + mexp b + 250 := by
    rw [UInt64.toNat_add, UInt64.toNat_add, expWord_toNat, expWord_toNat]
    simp only [UInt64.reduceToNat]
    have : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
    omega
  unfold product
  generalize Fma.mul128 (sigWord a) (sigWord b) = pr at hm ⊢
  obtain ⟨ph, pl⟩ := pr
  dsimp only at hm ⊢
  generalize hM : msig a * msig b = M at hm ⊢
  have hM0 : M ≠ 0 := by rw [← hM]; exact Nat.mul_ne_zero (by omega) (by omega)
  have hM106 : M < 2 ^ 106 := by
    calc M = msig a * msig b := hM.symm
      _ ≤ msig a * 2 ^ 53 := Nat.mul_le_mul_left _ hB53.le
      _ < 2 ^ 53 * 2 ^ 53 := Nat.mul_lt_mul_of_pos_right hA53 (by positivity)
      _ = 2 ^ 106 := by norm_num
  obtain ⟨m128, m1, m2⟩ := msb128_spec ph pl (by rw [hm]; exact hM0)
  rw [hm] at m1 m2
  generalize Fma.msb128 ph pl = mm at m128 m1 m2 ⊢
  generalize hmdef : mm.toNat = m at m128 m1 m2
  have hm105 : m ≤ 105 := by
    by_contra hc
    have : 2 ^ 106 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hsh : (125 - mm).toNat = 125 - m := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
      rw [hmdef]; exact le_trans hm105 (by decide))), hmdef]
    rfl
  have hfit : M * 2 ^ (125 - m) < 2 ^ 126 := by
    calc M * 2 ^ (125 - m) < 2 ^ (m + 1) * 2 ^ (125 - m) :=
          Nat.mul_lt_mul_of_pos_right m2 (by positivity)
      _ = 2 ^ 126 := by rw [← pow_add, show m + 1 + (125 - m) = 126 by omega]
  have hs := shl128_spec ph pl (125 - mm) (by rw [hsh]; omega)
    (by rw [hsh, hm]; exact lt_trans hfit (by norm_num))
  rw [hsh, hm] at hs
  generalize Fma.shl128 ph pl (125 - mm) = pp at hs ⊢
  obtain ⟨qh, ql⟩ := pp
  dsimp only at hs ⊢
  have hw : (expWord a + expWord b + 250 - (125 - mm)).toNat =
      mexp a + mexp b + 250 - (125 - m) := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hw1, hsh]; omega)), hw1,
      hsh]
  have h32 : (2 : ℕ) ^ 32 = 4294967296 := by norm_num
  refine ⟨125 - m, hs, by rw [hw]; omega, ?_, by rw [hs]; exact hfit, ?_, by rw [hw]; omega⟩
  · rw [hs]
    calc 2 ^ 125 = 2 ^ m * 2 ^ (125 - m) := by
          rw [← pow_add, show m + (125 - m) = 125 by omega]
      _ ≤ M * 2 ^ (125 - m) := Nat.mul_le_mul_right _ m1
  · rw [hs]
    have : 2 ^ 20 ∣ 2 ^ (125 - m) := Nat.pow_dvd_pow 2 (by omega)
    exact Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_left this M)

/-- The normalized significand of a nonzero addend. -/
theorem addend_spec (c : UInt64) (hc : Wasm.IEEE64.scaledMagnitude c ≠ 0)
    (hcf : CodeLib.IEEE64.Finite c) :
    ∃ S : ℕ, pair (addend c).1 (addend c).2.1 = msig c * 2 ^ S ∧
      (addend c).2.2.toNat + S = mexp c + 1325 ∧
      2 ^ 125 ≤ pair (addend c).1 (addend c).2.1 ∧
      pair (addend c).1 (addend c).2.1 < 2 ^ 126 ∧
      pair (addend c).1 (addend c).2.1 % 2 ^ 20 = 0 ∧
      (addend c).2.2.toNat < 2 ^ 32 := by
  have hC := msig_pos c hc
  have hC53 := msig_lt c
  have hec := mexp_le c hcf
  have hec1 := mexp_pos c
  have hw1 : (expWord c + 1325).toNat = mexp c + 1325 := by
    rw [UInt64.toNat_add, expWord_toNat]
    simp only [UInt64.reduceToNat]
    have : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
    omega
  have hp0 : pair 0 (sigWord c) = msig c := by
    unfold pair; rw [sigWord_toNat]; simp
  obtain ⟨m64, m1, m2⟩ := msb64_spec (sigWord c) (by rw [sigWord_toNat]; omega)
  rw [sigWord_toNat] at m1 m2
  unfold addend
  dsimp only
  generalize Fma.msb64 (sigWord c) = mm at m64 m1 m2 ⊢
  generalize hmdef : mm.toNat = m at m64 m1 m2
  have hm52 : m ≤ 52 := by
    by_contra hc'
    have : 2 ^ 53 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hsh : (125 - mm).toNat = 125 - m := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
      rw [hmdef]; exact le_trans hm52 (by decide))), hmdef]
    rfl
  have hfit : msig c * 2 ^ (125 - m) < 2 ^ 126 := by
    calc msig c * 2 ^ (125 - m) < 2 ^ (m + 1) * 2 ^ (125 - m) :=
          Nat.mul_lt_mul_of_pos_right m2 (by positivity)
      _ = 2 ^ 126 := by rw [← pow_add, show m + 1 + (125 - m) = 126 by omega]
  have hs := shl128_spec 0 (sigWord c) (125 - mm) (by rw [hsh]; omega)
    (by rw [hsh, hp0]; exact lt_trans hfit (by norm_num))
  rw [hsh, hp0] at hs
  have hw : (expWord c + 1325 - (125 - mm)).toNat = mexp c + 1325 - (125 - m) := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hw1, hsh]; omega)), hw1,
      hsh]
  have h32 : (2 : ℕ) ^ 32 = 4294967296 := by norm_num
  have hw2 : mexp c + 1325 - (125 - m) + (125 - m) = mexp c + 1325 :=
    Nat.sub_add_cancel (by omega)
  have hw3 : mexp c + 1325 - (125 - m) < 2 ^ 32 :=
    lt_of_le_of_lt (Nat.sub_le _ _) (by omega)
  refine ⟨125 - m, hs, (congrArg (fun x => x + (125 - m)) hw).trans hw2, ?_,
    by rw [hs]; exact hfit, ?_, lt_of_eq_of_lt hw hw3⟩
  · rw [hs]
    calc 2 ^ 125 = 2 ^ m * 2 ^ (125 - m) := by
          rw [← pow_add, show m + (125 - m) = 125 by omega]
      _ ≤ msig c * 2 ^ (125 - m) := Nat.mul_le_mul_right _ m1
  · rw [hs]
    have : 2 ^ 20 ∣ 2 ^ (125 - m) := Nat.pow_dvd_pow 2 (by omega)
    exact Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_left this (msig c))

#print axioms fmaBits_eq
#print axioms combine_eq
#print axioms product_spec
#print axioms addend_spec

end Library.Numerics.Arithmetic.Fma.FmaParts
