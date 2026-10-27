import Demos.RunningSumFp.PrintCharges

/-! Bounds on the generated allocation bounds of the binary64 parser that the running sum
compiles.  The digits of a decimal significand cost at most 716,264 bytes, since `decParse` keeps
at most 768 of them, and the rounding of `decRound` at most 3,688,256 bytes, since its range tests
leave only exponents within 1,093 of the bias.  The hexadecimal and special forms allocate
nothing, so `parse` costs at most `8 L + 4,404,576` bytes for a line of `L` bytes, the copy that
`stripCR` makes included. -/

namespace Demos.RunningSumFp

open Verified Library.Numerics.Arithmetic.Uscale
open Library.Numerics.Arithmetic.Uscale.UscaleTheorem (wordBits_spec)
open Library.Numerics.Decimal.ParseFloat (decParse digitsVal)

theorem wordBits_le (x : UInt64) : (wordBits x).toNat ≤ 64 := by
  rw [wordBits_spec, Nat.size_le]
  exact UInt64.toNat_lt x

theorem bitLen_le (a : Array UInt64) (bound : a.size < 2 ^ 50) :
    (bitLen a).toNat ≤ 32 * a.size + 32 := by
  have usize : UInt64.size = 18446744073709551616 := rfl
  unfold bitLen
  apply LeanExe.IR.loop_induction (fun _ (s : UInt64) => s.toNat ≤ 32 * a.size + 32)
  · simp
  · intro k s index le
    have kSize : k < a.size := lt_of_lt_of_le index (toUInt64_toNat_le a.size)
    have kNat : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by omega)
    split
    · rw [UInt64.toNat_add, UInt64.toNat_mul, kNat]
      have bits := wordBits_le a[k]!
      simp only [UInt64.reduceToNat]
      omega
    · exact le

theorem loop_mulSmall_size' (count : UInt64) (init : Array UInt64) (m c : UInt64 → UInt64)
    (bound : init.size + count.toNat < UInt64.size) :
    (LeanExe.loop count init fun i a => mulSmall a (m i) (c i)).size = init.size + count.toNat := by
  apply LeanExe.IR.loop_induction (fun k (b : Array UInt64) => b.size = init.size + k)
  · rfl
  · intro k b index same
    rw [mulSmall_size b _ _ (by omega)]
    omega

theorem chunks_le (kept : UInt64) (hk : kept.toNat ≤ 768) : ((kept + 8) / 9).toNat ≤ 86 := by
  rw [UInt64.toNat_div, UInt64.toNat_add]
  simp only [UInt64.reduceToNat]
  omega

theorem digitsVal_size (s : Array UInt64) (i0 ni z kept : UInt64) (hk : kept.toNat ≤ 768) :
    (digitsVal s i0 ni z kept).size = ((kept + 8) / 9).toNat := by
  have usize : UInt64.size = 18446744073709551616 := rfl
  have count := chunks_le kept hk
  unfold digitsVal
  rw [loop_mulSmall_size', LeanExe.IR.build_size, UInt64.toNat_zero, Nat.zero_add]
  rw [LeanExe.IR.build_size, UInt64.toNat_zero]
  omega

/-- The charge of the digits of a decimal significand: at most 86 products of nine digits each. -/
theorem digitsVal_bound_le (s : Array UInt64) (i0 ni z kept : UInt64) (hk : kept.toNat ≤ 768) :
    io.pureSources.digitsVal.bound (s, i0, ni, z, kept) ≤ 716264 := by
  have usize : UInt64.size = 18446744073709551616 := rfl
  have count := chunks_le kept hk
  rw [io.pureSources.digitsVal.bound_eq]
  refine le_trans (Nat.add_le_add_left (m := ((kept + 8) / 9).toNat * 8328) ?_ _) ?_
  · rw [← sumBelow_const 8328]
    apply loopCost_le_upto (fun j (b : Array UInt64) => b.size = j)
    · intro j b index same
      simp only [↓reduceIte, Nat.zero_add]
      exact le_trans (mulSmall_bound_le b _ _ (by omega)) (by omega)
    · intro j b index same _
      rw [mulSmall_size b _ _ (by omega)]
      omega
    · rw [LeanExe.IR.build_size]
      rfl
  · simp only [blockCost_eq, UInt64.reduceToNat]
    omega

theorem decParse_kept (general : Bool) (s : Array UInt64) (i0 : UInt64) :
    (decParse general 768 s i0).2.2.1.toNat ≤ 768 := by
  unfold decParse
  dsimp only
  rw [UInt64.toNat_min]
  simp only [UInt64.reduceToNat]
  omega

theorem decParse_size (general : Bool) (s : Array UInt64) (i0 : UInt64) :
    (decParse general 768 s i0).2.1.size ≤ 86 := by
  have kept := decParse_kept general s i0
  unfold decParse at kept ⊢
  dsimp only at kept ⊢
  rw [digitsVal_size _ _ _ _ _ kept]
  exact chunks_le _ kept

theorem decParse_bound_le (general : Bool) (s : Array UInt64) (i0 : UInt64) :
    io.pureSources.decParse.bound (general, 768, s, i0) ≤ 716264 := by
  rw [io.pureSources.decParse.bound_eq]
  apply digitsVal_bound_le
  rw [UInt64.toNat_min]
  simp only [UInt64.reduceToNat]
  omega

theorem shift_up_le (n d : Array UInt64) (hd : (bitLen d).toNat < 2 ^ 60) :
    (if bitLen n ≤ bitLen d + 53 + 2 then bitLen d + 53 + 2 - bitLen n else 0).toNat ≤
      (bitLen d).toNat + 55 := by
  split
  · rename_i le
    rw [UInt64.toNat_sub_of_le _ _ le, UInt64.toNat_add, UInt64.toNat_add]
    simp only [UInt64.reduceToNat]
    omega
  · simp

theorem shift_down_le (n d : Array UInt64) (hd : (bitLen d).toNat < 2 ^ 60) :
    (if bitLen n ≤ bitLen d + 53 + 2 then 0 else bitLen n - bitLen d - 53 - 2).toNat ≤
      (bitLen n).toNat := by
  split
  · simp
  · rename_i above
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_add, UInt64.toNat_add] at above
    simp only [UInt64.reduceToNat] at above
    have first : bitLen d ≤ bitLen n := UInt64.le_iff_toNat_le.mpr (by omega)
    have second : (53 : UInt64) ≤ bitLen n - bitLen d := UInt64.le_iff_toNat_le.mpr (by
      rw [UInt64.toNat_sub_of_le _ _ first]
      simp only [UInt64.reduceToNat]
      omega)
    have third : (2 : UInt64) ≤ bitLen n - bitLen d - 53 := UInt64.le_iff_toNat_le.mpr (by
      rw [UInt64.toNat_sub_of_le _ _ second, UInt64.toNat_sub_of_le _ _ first]
      simp only [UInt64.reduceToNat]
      omega)
    rw [UInt64.toNat_sub_of_le _ _ third, UInt64.toNat_sub_of_le _ _ second,
      UInt64.toNat_sub_of_le _ _ first]
    omega

/-- The charge of `decRound` for binary64, for at most 86 limbs of at most 768 digits.  Its range
tests leave only biased exponents within 1,093 below and 310 above the bias.  The lemma takes the
digit count, exponent, and flag whole, as the caller passes them. -/
theorem decRound_bound_le (D : Array UInt64) (rest : UInt64 × UInt64 × Bool) (hD : D.size ≤ 86)
    (hk : rest.1.toNat ≤ 768) :
    io.pureSources.decRound.bound (53, 2047, 1074, 309, 325, { val := D }, rest) ≤ 3688256 := by
  obtain ⟨kept, qb, sticky⟩ := rest
  have keptLe : kept.toNat ≤ 768 := hk
  have usize : UInt64.size = 18446744073709551616 := rfl
  have qbLt := UInt64.toNat_lt qb
  have keptLt := UInt64.toNat_lt kept
  rw [io.pureSources.decRound.bound_eq]
  split
  · omega
  split
  · omega
  rename_i overflow
  split
  · omega
  rename_i underflow
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_add, UInt64.toNat_add] at overflow underflow
  simp only [UInt64.reduceToNat] at overflow underflow
  have qbLo : 4611686018427387904 < qb.toNat + 1093 := by omega
  have qbHi : qb.toNat < 4611686018427387904 + 310 := by omega
  have startSize : (if sticky = true then mulSmall D 2 1 else D).size ≤ 87 := by
    split
    · rw [mulSmall_size D 2 1 (by omega)]
      omega
    · omega
  have startCost : (if sticky = true then io.pureSources.mulSmall.bound (D, 2, 1) else 0) ≤ 8424 := by
    split
    · have := mulSmall_bound_le D 2 1 (by omega)
      omega
    · omega
  have oneSize : (LeanExe.build 1 fun _ => if sticky = true then (2 : UInt64) else 1).size = 1 := by
    rw [LeanExe.IR.build_size]
    rfl
  generalize (if sticky = true then io.pureSources.mulSmall.bound (D, 2, 1) else 0) = c0
    at startCost ⊢
  generalize (if sticky = true then mulSmall D 2 1 else D) = n0 at startSize ⊢
  generalize (LeanExe.build 1 fun _ => if sticky = true then (2 : UInt64) else 1) = one
    at oneSize ⊢
  by_cases above : 4611686018427387904 ≤ qb
  · simp only [ge_iff_le, above, ↓reduceIte]
    have aboveNat : 4611686018427387904 ≤ qb.toNat := by
      have h := UInt64.le_iff_toNat_le.mp above
      simp only [UInt64.reduceToNat] at h
      exact h
    have kNat : (qb - 4611686018427387904).toNat = qb.toNat - 4611686018427387904 := by
      simp only [UInt64.toNat_sub_of_le _ _ above, UInt64.reduceToNat]
    have m : ((qb - 4611686018427387904) / 9).toNat ≤ 34 := by
      simp only [UInt64.toNat_div, kNat, UInt64.reduceToNat]
      omega
    have power := mulPow10_bound_le n0 (qb - 4611686018427387904) (by omega)
    have powerBound : (((qb - 4611686018427387904) / 9).toNat + 1) *
        (96 * (n0.size + ((qb - 4611686018427387904) / 9).toNat) + 168) ≤ 35 * (96 * 121 + 168) :=
      Nat.mul_le_mul (by omega) (by omega)
    have size := mulPow10_size n0 (qb - 4611686018427387904) (by omega)
    generalize mulPow10 n0 (qb - 4611686018427387904) = n at size ⊢
    have nBits := bitLen_le n (by omega)
    have oneBits := bitLen_le one (by omega)
    have up := shift_up_le n one (by omega)
    have down := shift_down_le n one (by omega)
    generalize (if bitLen n ≤ bitLen one + 53 + 2 then bitLen one + 53 + 2 - bitLen n else 0) = sn
      at up ⊢
    generalize (if bitLen n ≤ bitLen one + 53 + 2 then 0 else bitLen n - bitLen one - 53 - 2) = sd
      at down ⊢
    have quotient := scaledQuot_bound_le n one sn sd (53 + 3) (by decide) (by omega) (by omega)
    simp only [UInt64.reduceAdd, UInt64.reduceToNat] at quotient
    simp only [blockCost_eq, UInt64.reduceAdd, UInt64.reduceToNat]
    omega
  · simp only [ge_iff_le, above, ↓reduceIte]
    rw [UInt64.le_iff_toNat_le] at above
    simp only [UInt64.reduceToNat] at above
    have le : qb ≤ 4611686018427387904 := UInt64.le_iff_toNat_le.mpr (by
      simp only [UInt64.reduceToNat]
      omega)
    have kNat : (4611686018427387904 - qb).toNat = 4611686018427387904 - qb.toNat := by
      simp only [UInt64.toNat_sub_of_le _ _ le, UInt64.reduceToNat]
    have m : ((4611686018427387904 - qb) / 9).toNat ≤ 121 := by
      simp only [UInt64.toNat_div, kNat, UInt64.reduceToNat]
      omega
    have power := mulPow10_bound_le one (4611686018427387904 - qb) (by omega)
    rw [oneSize] at power
    have powerBound : (((4611686018427387904 - qb) / 9).toNat + 1) *
        (96 * (1 + ((4611686018427387904 - qb) / 9).toNat) + 168) ≤ 122 * (96 * 122 + 168) :=
      Nat.mul_le_mul (by omega) (by omega)
    have size := mulPow10_size one (4611686018427387904 - qb) (by omega)
    rw [oneSize] at size
    generalize mulPow10 one (4611686018427387904 - qb) = d at size ⊢
    have nBits := bitLen_le n0 (by omega)
    have dBits := bitLen_le d (by omega)
    have up := shift_up_le n0 d (by omega)
    have down := shift_down_le n0 d (by omega)
    generalize (if bitLen n0 ≤ bitLen d + 53 + 2 then bitLen d + 53 + 2 - bitLen n0 else 0) = sn
      at up ⊢
    generalize (if bitLen n0 ≤ bitLen d + 53 + 2 then 0 else bitLen n0 - bitLen d - 53 - 2) = sd
      at down ⊢
    have quotient := scaledQuot_bound_le n0 d sn sd (53 + 3) (by decide) (by omega) (by omega)
    simp only [UInt64.reduceAdd, UInt64.reduceToNat] at quotient
    simp only [blockCost_eq, UInt64.reduceAdd, UInt64.reduceToNat]
    omega

theorem parse64_bound_le (general : Bool) (s : Array UInt64) :
    io.pureSources.parse64.bound (general, s) ≤ 716264 + 3688256 := by
  rw [io.pureSources.parse64.bound_eq]
  generalize (if (limb s 0 == 45 || general && limb s 0 == 43) = true then (1 : UInt64) else 0) = i0
  split
  · omega
  split
  · omega
  split
  · omega
  refine Nat.add_le_add (decParse_bound_le _ _ _) ?_
  split
  · omega
  split
  · omega
  refine decRound_bound_le _ _ ?_ ?_
  · exact decParse_size _ _ _
  · exact decParse_kept _ _ _

theorem stripCR_bound_le (input : Array UInt64) :
    io.pureSources.stripCR.bound { val := input } ≤ 8 * input.size + 56 := by
  have small := toUInt64_toNat_le input.size
  rw [io.pureSources.stripCR.bound_eq]
  split
  · rename_i holds
    simp only [Bool.and_eq_true, decide_eq_true_eq] at holds
    have positive := UInt64.lt_iff_toNat_lt.mp holds.1
    simp only [UInt64.reduceToNat] at positive
    have one : (1 : UInt64) ≤ input.size.toUInt64 := UInt64.le_iff_toNat_le.mpr (by
      simp only [UInt64.reduceToNat]
      omega)
    rw [blockCost_eq, UInt64.toNat_sub_of_le _ _ one]
    omega
  · omega

/-- The charge of parsing a line of `L` bytes: the copy without its carriage return, the digits,
and the rounding. -/
theorem parse_bound_le (input : Array UInt64) :
    io.pureSources.parse.bound { val := input } ≤ 8 * input.size + 4404576 := by
  have copy := stripCR_bound_le input
  have number := parse64_bound_le true (Demos.RunningSumFp.stripCR input)
  rw [io.pureSources.parse.bound_eq]
  omega

end Demos.RunningSumFp
