import Demos.RunningSumFp.Wasi
import Verified.ChargeFacts
import LeanExe.IR.Combinators
import Library.Numerics.Decimal.PrintFloat.PrintFloatSteps

/-! Bounds on the generated allocation bounds of the big-integer arithmetic and the printer that
the binary64 running sum compiles, and the sizes of the arrays that their callers pass on.  Each
quotient of the printer costs at most `quotAtCost` bytes for the exponents that a binary64 word
reaches, and `shortest` makes at most 62 such quotients' worth of charges: its search stops
within 27 steps of its start (`PrintFloatSteps.search_le`), so it tests at most 28 exponents. -/

namespace Demos.RunningSumFp

open Verified Library.Numerics.Arithmetic.Uscale
open Library.Numerics.Decimal.PrintFloat.PrintFloatPick (WordBounds words_spec startExp_spec)
open Library.Numerics.Decimal.PrintFloat.PrintFloatSteps (jstart_binary64 search_le)
open Library.Numerics.Decimal.PrintFloat (startExp)

theorem mulSmall_size (a : Array UInt64) (m c : UInt64) (bound : a.size < UInt64.size) :
    (mulSmall a m c).size = a.size + 1 := by
  have count : a.size.toUInt64.toNat = a.size := UInt64.toNat_ofNat_of_lt' bound
  unfold mulSmall
  dsimp only
  rw [Array.size_push, loop_push_size]
  case pushes => intro i state; simp
  simp only [LeanExe.IR.build_size, UInt64.toNat_zero, Nat.zero_add]
  omega

theorem mulSmall_bound_le (a : Array UInt64) (m c : UInt64) (bound : a.size < UInt64.size) :
    io.pureSources.mulSmall.bound (a, m, c) ≤ 96 * a.size + 168 := by
  have count : a.size.toUInt64.toNat = a.size := UInt64.toNat_ofNat_of_lt' bound
  rw [io.pureSources.mulSmall.bound_eq]
  refine le_trans (Nat.add_le_add_right (Nat.min_le_right _ _) _) ?_
  rw [loopCost_const, loop_push_size]
  case pushes => intro i state; simp
  simp only [LeanExe.IR.build_size, UInt64.toNat_zero, Nat.zero_add, blockCost_eq, creditCost,
    paidGrowCost, growCost, allocCost]
  omega

theorem sub_size (a b : Array UInt64) (bound : a.size < UInt64.size) :
    (sub a b).size = a.size := by
  have count : a.size.toUInt64.toNat = a.size := UInt64.toNat_ofNat_of_lt' bound
  unfold sub
  rw [loop_push_size]
  case pushes => intro i state; simp
  simp only [LeanExe.IR.build_size, UInt64.toNat_zero, Nat.zero_add]
  omega

theorem sub_bound_le (a b : Array UInt64) (bound : a.size < UInt64.size) :
    io.pureSources.sub.bound (a, b) ≤ 80 * a.size + 72 := by
  have count : a.size.toUInt64.toNat = a.size := UInt64.toNat_ofNat_of_lt' bound
  rw [io.pureSources.sub.bound_eq]
  refine le_trans (Nat.min_le_right _ _) ?_
  rw [loopCost_const]
  simp only [LeanExe.IR.build_size, UInt64.toNat_zero, Nat.zero_add, blockCost_eq, creditCost,
    paidGrowCost, allocCost]
  omega

theorem shift_toNat_le (n : Nat) (k : UInt64) :
    (n.toUInt64 + (k >>> 5)).toNat ≤ n + (k >>> 5).toNat := by
  rw [UInt64.toNat_add]
  have := toUInt64_toNat_le n
  have := Nat.mod_le (n.toUInt64.toNat + (k >>> 5).toNat) (2 ^ 64)
  omega

theorem shl_size_le (a : Array UInt64) (k : UInt64) (bound : a.size < UInt64.size) :
    (shl a k).size ≤ a.size + 1 + (k >>> 5).toNat := by
  unfold shl
  dsimp only
  rw [LeanExe.IR.build_size, mulSmall_size a _ _ bound]
  exact shift_toNat_le _ _

theorem shl_bound_le (a : Array UInt64) (k : UInt64) (bound : a.size < UInt64.size) :
    io.pureSources.shl.bound (a, k) ≤ 104 * a.size + 232 + 8 * (k >>> 5).toNat := by
  have product := mulSmall_bound_le a ((1 : UInt64) <<< (k &&& 31)) 0 bound
  rw [io.pureSources.shl.bound_eq, mulSmall_size a _ _ bound]
  have shifted := shift_toNat_le (a.size + 1) k
  rw [blockCost_eq]
  omega

theorem divStep_size (d : Array UInt64) (j : UInt64) (s : UInt64 × Array UInt64)
    (bound : s.2.size < UInt64.size) : (divStep d j s).2.size = s.2.size := by
  unfold divStep
  dsimp only
  split
  · exact sub_size _ _ bound
  · rfl

theorem divStep_bound_le (d : Array UInt64) (j : UInt64) (s : UInt64 × Array UInt64)
    (dBound : d.size < UInt64.size) (sBound : s.2.size < UInt64.size) :
    io.pureSources.divStep.bound (d, j, s) ≤
      104 * d.size + 232 + 8 * (j >>> 5).toNat + 80 * s.2.size + 72 := by
  have shifted := shl_bound_le d j dBound
  have taken := sub_bound_le s.2 (shl d j) sBound
  rw [io.pureSources.divStep.bound_eq]
  split
  · omega
  · rw [blockCost_eq]
    omega

theorem shift_small {bits : UInt64} {k : Nat} (small : bits.toNat ≤ 64) (index : k < bits.toNat) :
    ((bits - 1 - UInt64.ofNat k) >>> 5).toNat ≤ 1 := by
  have kNat : (UInt64.ofNat k).toNat = k :=
    UInt64.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le index (Nat.le_trans small (by decide)))
  have one : (1 : UInt64) ≤ bits := UInt64.le_iff_toNat_le.mpr (by rw [UInt64.toNat_one]; omega)
  have first : (bits - 1).toNat = bits.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ one, UInt64.toNat_one]
  have second : UInt64.ofNat k ≤ bits - 1 := UInt64.le_iff_toNat_le.mpr (by omega)
  have difference : (bits - 1 - UInt64.ofNat k).toNat = bits.toNat - 1 - k := by
    rw [UInt64.toNat_sub_of_le _ _ second, first, kNat]
  rw [UInt64.toNat_shiftRight, difference]
  simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
  omega

theorem divBits_bound_le (n d : Array UInt64) (bits : UInt64) (small : bits.toNat ≤ 64)
    (nBound : n.size < UInt64.size) (dBound : d.size < UInt64.size) :
    io.pureSources.divBits.bound ({ val := n }, d, bits) ≤
      bits.toNat * (104 * d.size + 80 * n.size + 312) := by
  rw [io.pureSources.divBits.bound_eq, ← sumBelow_const (104 * d.size + 80 * n.size + 312)]
  apply loopCost_le_upto (fun _ (state : UInt64 × Array UInt64) => state.2.size = n.size)
  · intro k state index same
    have step := divStep_bound_le d (bits - 1 - UInt64.ofNat k) state dBound (by omega)
    have shifted := shift_small small index
    simp only [↓reduceIte, Nat.zero_add]
    omega
  · intro k state _ same _
    rw [divStep_size d (bits - 1 - UInt64.ofNat k) state (by omega)]
    exact same
  · rfl

theorem toNat_shift_five (x : UInt64) : (x >>> 5).toNat = x.toNat / 32 := by
  rw [UInt64.toNat_shiftRight]
  simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]

theorem scaledQuot_bound_le (n d : Array UInt64) (sn sd bits : UInt64) (small : bits.toNat ≤ 64)
    (nBound : n.size + 1 + sn.toNat / 32 < UInt64.size)
    (dBound : d.size + 1 + sd.toNat / 32 < UInt64.size) :
    io.pureSources.scaledQuot.bound (n, d, sn, sd, bits) ≤
      104 * n.size + 104 * d.size + 464 + 8 * (sn.toNat / 32) + 8 * (sd.toNat / 32) +
        bits.toNat * (104 * (d.size + 1 + sd.toNat / 32) + 80 * (n.size + 1 + sn.toNat / 32) + 312) := by
  have numerator := shl_bound_le n sn (by omega)
  have denominator := shl_bound_le d sd (by omega)
  have numeratorSize := shl_size_le n sn (by omega)
  have denominatorSize := shl_size_le d sd (by omega)
  rw [toNat_shift_five] at numerator numeratorSize denominator denominatorSize
  have division := divBits_bound_le (shl n sn) (shl d sd) bits small (by omega) (by omega)
  have product : bits.toNat * (104 * (shl d sd).size + 80 * (shl n sn).size + 312) ≤
      bits.toNat * (104 * (d.size + 1 + sd.toNat / 32) + 80 * (n.size + 1 + sn.toNat / 32) + 312) :=
    Nat.mul_le_mul (Nat.le_refl _) (by omega)
  rw [io.pureSources.scaledQuot.bound_eq]
  omega

theorem loop_mulSmall_size (a : Array UInt64) (count : UInt64)
    (bound : a.size + count.toNat < UInt64.size) :
    (LeanExe.loop count a fun _ a => mulSmall a 1000000000 0).size = a.size + count.toNat := by
  apply LeanExe.IR.loop_induction (fun k (b : Array UInt64) => b.size = a.size + k)
  · rfl
  · intro k b index same
    rw [mulSmall_size b _ _ (by omega)]
    omega

theorem mulPow10_size (a : Array UInt64) (k : UInt64)
    (bound : a.size + (k / 9).toNat + 1 < UInt64.size) :
    (mulPow10 a k).size = a.size + (k / 9).toNat + 1 := by
  have loopSize := loop_mulSmall_size a (k / 9) (by omega)
  unfold mulPow10
  rw [mulSmall_size, loopSize]
  rw [loopSize]
  omega

theorem mulPow10_bound_le (a : Array UInt64) (k : UInt64)
    (bound : a.size + (k / 9).toNat + 1 < UInt64.size) :
    io.pureSources.mulPow10.bound ({ val := a }, k) ≤
      ((k / 9).toNat + 1) * (96 * (a.size + (k / 9).toNat) + 168) := by
  have loopSize := loop_mulSmall_size a (k / 9) (by omega)
  rw [io.pureSources.mulPow10.bound_eq, Nat.add_mul, Nat.one_mul]
  apply Nat.add_le_add
  · rw [← sumBelow_const (96 * (a.size + (k / 9).toNat) + 168) (k / 9).toNat]
    apply loopCost_le_upto (fun j (b : Array UInt64) => b.size = a.size + j)
    · intro j b index same
      have step := mulSmall_bound_le b 1000000000 0 (by omega)
      simp only [↓reduceIte, Nat.zero_add]
      omega
    · intro j b index same _
      rw [mulSmall_size b _ _ (by omega)]
      omega
    · rfl
  · have last := mulSmall_bound_le (LeanExe.loop (k / 9) a fun _ a => mulSmall a 1000000000 0)
      (pow10Word (k % 9)) 0 (by rw [loopSize]; omega)
    rw [loopSize] at last
    exact last

/-- A bound on the charge of one quotient of the binary64 printer, `quotAt`, for the exponents
of a binary64 word: 953,376 bytes. -/
def quotAtCost : Nat := 953376

open Library.Numerics.Decimal.PrintFloat in
theorem limbsOf_size (x : UInt64) : (limbsOf x).size = 2 := by
  unfold limbsOf
  rw [LeanExe.IR.build_size]
  rfl

theorem one_size : (LeanExe.build 1 fun _ => (1 : UInt64)).size = 1 := by
  rw [LeanExe.IR.build_size]
  rfl

/-- The charge of `quotAt` for a shift `sn` below 2048, `sd` at most 1076, and a biased decimal
exponent from `2 ^ 62 - 349` to `2 ^ 62 + 319`. -/
theorem quotAt_bound_le (N sn sd jb : UInt64) (hsn : sn.toNat ≤ 2047) (hsd : sd.toNat ≤ 1076)
    (lo : 4611686018427387904 ≤ jb.toNat + 349) (hi : jb.toNat ≤ 4611686018427387904 + 319) :
    io.pureSources.quotAt.bound (N, sn, sd, jb) ≤ quotAtCost := by
  have usize : UInt64.size = 18446744073709551616 := rfl
  rw [io.pureSources.quotAt.bound_eq, io.pureSources.limbsOf.bound_eq]
  unfold quotAtCost
  split
  · rename_i above
    have aboveNat : 4611686018427387904 ≤ jb.toNat := by
      have h := UInt64.le_iff_toNat_le.mp above
      simp only [UInt64.reduceToNat] at h
      exact h
    have kNat : (jb - 4611686018427387904).toNat = jb.toNat - 4611686018427387904 := by
      simp only [UInt64.toNat_sub_of_le _ _ above, UInt64.reduceToNat]
    have m : ((jb - 4611686018427387904) / 9).toNat ≤ 35 := by
      simp only [UInt64.toNat_div, kNat, UInt64.reduceToNat]
      omega
    have power := mulPow10_bound_le (LeanExe.build 1 fun _ => (1 : UInt64))
      (jb - 4611686018427387904) (by rw [one_size]; omega)
    have size := mulPow10_size (LeanExe.build 1 fun _ => (1 : UInt64))
      (jb - 4611686018427387904) (by rw [one_size]; omega)
    rw [one_size] at power size
    have quotient := scaledQuot_bound_le (Library.Numerics.Decimal.PrintFloat.limbsOf N)
      (mulPow10 (LeanExe.build 1 fun _ => (1 : UInt64)) (jb - 4611686018427387904)) sn sd 63
      (by decide) (by rw [limbsOf_size]; omega) (by rw [size]; omega)
    rw [limbsOf_size, size] at quotient
    simp only [UInt64.reduceToNat] at quotient
    have powerBound : (((jb - 4611686018427387904) / 9).toNat + 1) *
        (96 * (1 + ((jb - 4611686018427387904) / 9).toNat) + 168) ≤ 36 * 3624 :=
      Nat.mul_le_mul (by omega) (by omega)
    simp only [blockCost_eq, UInt64.reduceToNat]
    omega
  · rename_i below
    rw [UInt64.le_iff_toNat_le] at below
    simp only [UInt64.reduceToNat] at below
    have le : jb ≤ 4611686018427387904 := UInt64.le_iff_toNat_le.mpr (by
      simp only [UInt64.reduceToNat]
      omega)
    have kNat : (4611686018427387904 - jb).toNat = 4611686018427387904 - jb.toNat := by
      simp only [UInt64.toNat_sub_of_le _ _ le, UInt64.reduceToNat]
    have m : ((4611686018427387904 - jb) / 9).toNat ≤ 38 := by
      simp only [UInt64.toNat_div, kNat, UInt64.reduceToNat]
      omega
    have power := mulPow10_bound_le (Library.Numerics.Decimal.PrintFloat.limbsOf N)
      (4611686018427387904 - jb) (by rw [limbsOf_size]; omega)
    have size := mulPow10_size (Library.Numerics.Decimal.PrintFloat.limbsOf N)
      (4611686018427387904 - jb) (by rw [limbsOf_size]; omega)
    rw [limbsOf_size] at power size
    have quotient := scaledQuot_bound_le
      (mulPow10 (Library.Numerics.Decimal.PrintFloat.limbsOf N) (4611686018427387904 - jb))
      (LeanExe.build 1 fun _ => (1 : UInt64)) sn sd 63
      (by decide) (by rw [size]; omega) (by rw [one_size]; omega)
    rw [one_size, size] at quotient
    simp only [UInt64.reduceToNat] at quotient
    have powerBound : (((4611686018427387904 - jb) / 9).toNat + 1) *
        (96 * (2 + ((4611686018427387904 - jb) / 9).toNat) + 168) ≤ 39 * 4008 :=
      Nat.mul_le_mul (by omega) (by omega)
    simp only [blockCost_eq, UInt64.reduceToNat]
    omega

theorem range_bound_le (Nl Nh sn sd jb : UInt64) (closed : Bool) (hsn : sn.toNat ≤ 2047)
    (hsd : sd.toNat ≤ 1076) (lo : 4611686018427387904 ≤ jb.toNat + 349)
    (hi : jb.toNat ≤ 4611686018427387904 + 319) :
    io.pureSources.range.bound (Nl, Nh, sn, sd, jb, closed) ≤ 2 * quotAtCost := by
  have low := quotAt_bound_le Nl sn sd jb hsn hsd lo hi
  have high := quotAt_bound_le Nh sn sd jb hsn hsd lo hi
  rw [io.pureSources.range.bound_eq]
  omega

theorem found_bound_le (Nl Nh sn sd jb : UInt64) (closed : Bool) (hsn : sn.toNat ≤ 2047)
    (hsd : sd.toNat ≤ 1076) (lo : 4611686018427387904 ≤ jb.toNat + 349)
    (hi : jb.toNat ≤ 4611686018427387904 + 319) :
    io.pureSources.found.bound (Nl, Nh, sn, sd, jb, closed) ≤ 2 * quotAtCost := by
  rw [io.pureSources.found.bound_eq]
  exact range_bound_le Nl Nh sn sd jb closed hsn hsd lo hi

theorem exponent_sub (j0 x : UInt64) (lo : 4611686018427387904 ≤ j0.toNat + 321)
    (hi : j0.toNat ≤ 4611686018427387904 + 319) (small : x.toNat ≤ 28) :
    4611686018427387904 ≤ (j0 - x).toNat + 349 ∧ (j0 - x).toNat ≤ 4611686018427387904 + 319 := by
  have le : x ≤ j0 := UInt64.le_iff_toNat_le.mpr (by omega)
  rw [UInt64.toNat_sub_of_le _ _ le]
  omega

theorem exponent_sub_one (j0 x : UInt64) (lo : 4611686018427387904 ≤ j0.toNat + 321)
    (hi : j0.toNat ≤ 4611686018427387904 + 319) (small : x.toNat ≤ 27) :
    4611686018427387904 ≤ (j0 - x - 1).toNat + 349 ∧
      (j0 - x - 1).toNat ≤ 4611686018427387904 + 319 := by
  have le : x ≤ j0 := UInt64.le_iff_toNat_le.mpr (by omega)
  have one : (1 : UInt64) ≤ j0 - x :=
    UInt64.le_iff_toNat_le.mpr (by rw [UInt64.toNat_sub_of_le _ _ le, UInt64.toNat_one]; omega)
  rw [UInt64.toNat_sub_of_le _ _ one, UInt64.toNat_sub_of_le _ _ le, UInt64.toNat_one]
  omega

theorem ite_add_ite_le {p q : Prop} [Decidable p] [Decidable q] {a b x y : Nat} (ha : a ≤ x)
    (hb : b ≤ y) : (if p then a + (if q then b else 0) else 0) ≤ x + y := by
  split_ifs <;> omega

/-- The charge of `shortest` for a binary64 word: the search tests at most 28 exponents, two
quotients each, and the choice of the digits takes at most two ranges and two more quotients. -/
theorem shortest_bound_le {Q E : Nat} (low : Bool) (hb : WordBounds Q E 1074) (hE : E ≤ 2047) :
    io.pureSources.shortest.bound (UInt64.ofNat Q, UInt64.ofNat E, UInt64.ofNat 1074, low) ≤
      62 * quotAtCost := by
  have usize : UInt64.size = 18446744073709551616 := rfl
  obtain ⟨_, _, _, w4, w5, _⟩ := words_spec (low := low) hb
  have start := startExp_spec hb
  obtain ⟨jlo, jhi⟩ := jstart_binary64 hb
  have count := search_le (low := low) hb
  have hsn : (UInt64.ofNat E - 1).toNat ≤ 2047 := by omega
  have hsd : (UInt64.ofNat 1074 + 2).toNat ≤ 1076 := by omega
  have hsv : (UInt64.ofNat E - 1 + 1).toNat ≤ 2047 := by
    rw [UInt64.sub_add_cancel, UInt64.toNat_ofNat_of_lt' (by omega)]
    exact hE
  rw [io.pureSources.shortest.bound_eq]
  generalize startExp (4 * UInt64.ofNat Q + 2) (UInt64.ofNat E - 1) (UInt64.ofNat 1074 + 2) = j0
    at start count ⊢
  have j0lo : 4611686018427387904 ≤ j0.toNat + 321 := by omega
  have j0hi : j0.toNat ≤ 4611686018427387904 + 319 := by omega
  have total : 28 * (2 * quotAtCost) +
      (2 * quotAtCost + (quotAtCost + (2 * quotAtCost + quotAtCost))) ≤ 62 * quotAtCost := by
    omega
  refine le_trans (Nat.add_le_add (b := 28 * (2 * quotAtCost)) ?_
    (Nat.add_le_add (b := 2 * quotAtCost) ?_ (Nat.add_le_add (b := quotAtCost) ?_ ?_))) total
  · refine le_trans (loopCost_repeatWhile_le _ _ (2 * quotAtCost) _ ?_)
      (Nat.mul_le_mul (by omega) (Nat.le_refl _))
    intro j hj
    have jNat : (UInt64.ofNat j).toNat = j := UInt64.toNat_ofNat_of_lt' (by omega)
    have range := exponent_sub j0 (UInt64.ofNat j) j0lo j0hi (by omega)
    exact found_bound_le _ _ _ _ _ _ hsn hsd range.1 range.2
  · have range := exponent_sub j0 _ j0lo j0hi (Nat.le_succ_of_le count)
    exact range_bound_le _ _ _ _ _ _ hsn hsd range.1 range.2
  · have range := exponent_sub j0 _ j0lo j0hi (Nat.le_succ_of_le count)
    exact quotAt_bound_le _ _ _ _ hsv hsd range.1 range.2
  · have range := exponent_sub_one j0 _ j0lo j0hi count
    exact ite_add_ite_le (range_bound_le _ _ _ _ _ _ hsn hsd range.1 range.2)
      (quotAt_bound_le _ _ _ _ hsv hsd range.1 range.2)

theorem shortest_word_bound_le (Q E : UInt64) (low : Bool) (hQ : 1 ≤ Q.toNat)
    (hQ53 : Q.toNat < 2 ^ 53) (hE : 1 ≤ E.toNat) (hE2 : E.toNat ≤ 2047) :
    io.pureSources.shortest.bound (Q, E, 1074, low) ≤ 62 * quotAtCost := by
  have bound := shortest_bound_le (Q := Q.toNat) (E := E.toNat) low
    ⟨hQ, hQ53, hE, by omega, by norm_num, by norm_num⟩ hE2
  have nu : UInt64.ofNat 1074 = 1074 := rfl
  simpa only [UInt64.ofNat_toNat, nu] using bound

open Library.Numerics.Decimal.PrintFloat
  (numDigits digitsFrom byte1 noBytes special fixed sciLayoutW print64 print64With)

theorem numDigits_range (t : UInt64) : 1 ≤ (numDigits t).toNat ∧ (numDigits t).toNat ≤ 19 := by
  unfold numDigits LeanExe.repeatWhile
  refine ⟨repeatWhile_count_ge _ 19 1 (by decide), repeatWhile_count_le _ 19 (by decide) ?_ _ _
    (by decide)⟩
  intro k holds
  simp only [Bool.and_eq_true, decide_eq_true_eq] at holds
  have lt := UInt64.lt_iff_toNat_lt.mp holds.1
  simpa only [UInt64.reduceToNat] using lt

theorem digitsFrom_size (t nd s cnt : UInt64) : (digitsFrom t nd s cnt).size = cnt.toNat := by
  unfold digitsFrom
  rw [LeanExe.IR.build_size]

theorem byte1_size (b : UInt64) : (byte1 b).size = 1 := by
  unfold byte1
  rw [LeanExe.IR.build_size]
  rfl

theorem noBytes_size : noBytes.size = 0 := by
  unfold noBytes
  rw [LeanExe.IR.build_size]
  rfl

theorem numDigits_pred (t : UInt64) : (numDigits t - 1).toNat = (numDigits t).toNat - 1 := by
  have range := numDigits_range t
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [UInt64.toNat_one]; omega)),
    UInt64.toNat_one]

/-- The charge of the scientific layout.  The lemma takes the pair of digits and exponent whole, so
that a caller's pair `shortest Q E nu low` matches it without structure eta, which would make the
kernel reduce `shortest` on a symbolic word. -/
theorem sciLayoutW_bound_le (neg : Bool) (p : UInt64 × UInt64) :
    io.pureSources.sciLayoutW.bound (neg, p) ≤ 2968 := by
  obtain ⟨t, kb⟩ := p
  have digits := numDigits_range t
  have below := numDigits_range (4611686018427387904 - (kb + numDigits t - 1))
  have above := numDigits_range (kb + numDigits t - 1 - 4611686018427387904)
  have pred := numDigits_pred t
  rw [io.pureSources.sciLayoutW.bound_eq]
  simp only [io.pureSources.digitsFrom.bound_eq, io.pureSources.byte1.bound_eq,
    io.pureSources.noBytes.bound_eq]
  split_ifs <;>
    simp only [digitsFrom_size, byte1_size, noBytes_size, Array.size_append, blockCost_eq,
      growCost_eq, paidGrowCost, allocCost, UInt64.reduceToNat, pred] <;>
    omega

theorem sciLayoutW_size_le (neg : Bool) (t kb : UInt64) : (sciLayoutW neg t kb).size ≤ 42 := by
  have digits := numDigits_range t
  have below := numDigits_range (4611686018427387904 - (kb + numDigits t - 1))
  have above := numDigits_range (kb + numDigits t - 1 - 4611686018427387904)
  have pred := numDigits_pred t
  unfold sciLayoutW
  dsimp only
  split_ifs <;>
    simp only [digitsFrom_size, byte1_size, noBytes_size, Array.size_append, UInt64.reduceToNat,
      pred] <;>
    omega

theorem special_bound_le (neg inf nan ecma : Bool) :
    io.pureSources.special.bound (neg, inf, nan, ecma) ≤ 128 := by
  rw [io.pureSources.special.bound_eq]
  simp only [io.pureSources.fixed.bound_eq, blockCost_eq, UInt64.reduceToNat]
  split_ifs <;> omega

theorem special_size_le (neg inf nan ecma : Bool) : (special neg inf nan ecma).size ≤ 9 := by
  unfold special fixed
  split_ifs <;> simp only [LeanExe.IR.build_size, UInt64.reduceToNat] <;> omega

theorem word_fields (w : UInt64) :
    (w >>> 52 &&& 2047).toNat ≤ 2047 ∧ (w &&& 4503599627370495).toNat ≤ 4503599627370495 := by
  constructor
  · rw [UInt64.toNat_and]
    exact Nat.and_le_right
  · rw [UInt64.toNat_and]
    exact Nat.and_le_right

/-- The charge of printing a binary64 word: `shortest` and the scientific layout, or a special
string. -/
theorem print64_bound_le (w : UInt64) :
    io.pureSources.print64.bound w ≤ 62 * quotAtCost + 2968 := by
  obtain ⟨field, fraction⟩ := word_fields w
  rw [io.pureSources.print64.bound_eq, io.pureSources.print64With.bound_eq]
  simp only [Bool.false_eq_true, ↓reduceIte]
  split_ifs with infinite zero subnormal
  · have := special_bound_le (w >>> 63 == 1) true (w &&& 4503599627370495 != 0) false
    omega
  · have := special_bound_le (w >>> 63 == 1) false false false
    omega
  · simp only [Bool.and_eq_true, beq_iff_eq, ← UInt64.toNat_inj,
      UInt64.reduceToNat] at infinite zero subnormal
    exact Nat.add_le_add
      (shortest_word_bound_le _ _ _ (by omega) (by omega) (by rw [UInt64.toNat_one])
        (by rw [UInt64.toNat_one]; omega))
      (sciLayoutW_bound_le _ _)
  · simp only [Bool.and_eq_true, beq_iff_eq, ← UInt64.toNat_inj,
      UInt64.reduceToNat] at infinite zero subnormal
    have significand : ((w &&& 4503599627370495) + 4503599627370496).toNat =
        (w &&& 4503599627370495).toNat + 4503599627370496 := by
      rw [UInt64.toNat_add]
      simp only [UInt64.reduceToNat]
      omega
    exact Nat.add_le_add
      (shortest_word_bound_le _ _ _ (by rw [significand]; omega) (by rw [significand]; omega)
        (by omega) (by omega))
      (sciLayoutW_bound_le _ _)

theorem print64_size_le (w : UInt64) : (print64 w).size ≤ 42 := by
  unfold print64 print64With
  dsimp only
  simp only [Bool.false_eq_true, ↓reduceIte]
  split_ifs
  · exact le_trans (special_size_le _ _ _ _) (by decide)
  · exact le_trans (special_size_le _ _ _ _) (by decide)
  all_goals exact sciLayoutW_size_le _ _ _

/-- The charge of rendering a total: the printer and the byte string with its newline. -/
theorem render_bound_le (value : Float) :
    io.pureSources.render.bound value ≤ 62 * quotAtCost + 3066 := by
  have printed := print64_bound_le value.toBits
  have size := print64_size_le value.toBits
  have small := toUInt64_toNat_le (print64 value.toBits).size
  rw [io.pureSources.render.bound_eq]
  have count : ((print64 value.toBits).size.toUInt64 + 1).toNat ≤ 43 := by
    rw [UInt64.toNat_add, UInt64.toNat_one]
    omega
  have cost := allocationCost_le ((print64 value.toBits).size.toUInt64 + 1).toNat
  omega

end Demos.RunningSumFp
