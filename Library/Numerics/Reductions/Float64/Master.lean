import Library.Numerics.Reductions.Float64.Compiled
import Library.Numerics.Reductions.Binary64
import LeanExe.Dialect.ArrayLemmas
import Verified.Master

/-!
The master theorems of the binary64 reductions.  `total` and `select` are left-to-right sums,
whose errors `Binary64.sum_bound` gives; `sumRange` sums by halves, and `sumRange_approx` bounds
its error by induction on the recursion, with `γ` of the depth `⌈log₂ n⌉`; `largest` returns the
last element that is not a NaN and that no element exceeds, by the invariant `LargestInv`.
-/

namespace Library.Numerics.Reductions.Float64

open CodeLib.IEEE64 (value Finite)
open LeanExe.ProofKit LeanExe.ProofKit.F64Approx LeanExe.Dialect
open Library.Numerics.Reductions.Binary64 Library.Numerics.Reductions.SumError

set_option exponentiation.threshold 4096

theorem total_export :
    ({ name := "total", funcIdx := 2 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem largest_export :
    ({ name := "largest", funcIdx := 3 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem select_export :
    ({ name := "select", funcIdx := 4 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem sumRange_export :
    ({ name := "sumRange", funcIdx := 6 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem size_lt {α : Type} {xs : Array α} {f : α → UInt64}
    (h : (xs.map f).size < 536870912) : xs.size < 536870912 := by
  simpa using h

/-! ### `total` -/

theorem total_eq (xs : Array Float) (h : xs.size < 2 ^ 64) :
    total xs = xs.toList.foldl (fun acc x => acc + x) 0.0 := by
  have h1 : total xs =
      (List.range xs.size.toUInt64.toNat).foldl (fun acc i => acc + xs[i]!) 0.0 :=
    loop_toNat _ _ (fun j acc => acc + xs[j]!)
  rw [h1, size_toUInt64 xs h, ← range_map_get xs, List.foldl_map]

theorem total_spec (xs : Array Float) (hs : xs.size < 2 ^ 52) (hf : ∀ x ∈ xs, Finite x.toBits)
    (hS : (xs.toList.map fun x => |value x.toBits|).sum ≤ 2 ^ 1022) :
    Finite (total xs).toBits ∧
      |value (total xs).toBits - (xs.toList.map fun x => value x.toBits).sum| ≤
        ((xs.size - 1 : ℕ) : ℝ) / (2 ^ 53 - (xs.size - 1 : ℕ)) *
          (xs.toList.map fun x => |value x.toBits|).sum := by
  rw [total_eq xs (by omega)]
  have h := sum_bound xs.toList (fun x => x) (fun a ha => hf a (Array.mem_toList_iff.mp ha))
    (by rw [Array.length_toList]; exact hs) hS
  rw [Array.length_toList] at h
  exact h

/-- The export `total`, called on an array of `n` finite floats whose magnitudes sum to at most
`2 ^ 1022`, returns a finite float within `γ_(n-1) Σ |x_i|` of the exact sum `Σ x_i`, where
`γ_k = k / (2 ^ 53 - k)`. -/
theorem total_master :
    Verified.Master compiled.module compiled.tables "total" compiled.total.bound
      (fun xs : Array Float => (∀ x ∈ xs, Finite x.toBits) ∧
        (xs.toList.map fun x => |value x.toBits|).sum ≤ 2 ^ 1022)
      (fun xs (y : Float) => Finite y.toBits ∧
        |value y.toBits - (xs.toList.map fun x => value x.toBits).sum| ≤
          ((xs.size - 1 : ℕ) : ℝ) / (2 ^ 53 - (xs.size - 1 : ℕ)) *
            (xs.toList.map fun x => |value x.toBits|).sum) :=
  .of_trapFree (.ofA compiled.total.trapFree) nofun total_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ xs ⟨_, _, hxs⟩ hD =>
      total_spec xs (by have := size_lt hxs.values.size_lt_memory32; omega) hD.1 hD.2

#print axioms total_master

/-! ### `select` -/

theorem select_eq (bs : Array Bool) (xs : Array Float) (h : xs.size < 2 ^ 64) :
    select bs xs =
      ((List.range xs.size).filter fun i => bs[i]!).foldl (fun acc i => acc + xs[i]!) 0.0 := by
  have h1 : select bs xs = (List.range xs.size.toUInt64.toNat).foldl
      (fun acc i => if bs[i]! then acc + xs[i]! else acc) 0.0 :=
    loop_toNat _ _ (fun j acc => if bs[j]! then acc + xs[j]! else acc)
  rw [h1, size_toUInt64 xs h, List.foldl_filter]

theorem select_spec (bs : Array Bool) (xs : Array Float) (hs : xs.size < 2 ^ 52)
    (hf : ∀ x ∈ xs, Finite x.toBits)
    (hS : (((List.range xs.size).filter fun i => bs[i]!).map
      fun i => |value xs[i]!.toBits|).sum ≤ 2 ^ 1022) :
    Finite (select bs xs).toBits ∧
      |value (select bs xs).toBits - (((List.range xs.size).filter fun i => bs[i]!).map
          fun i => value xs[i]!.toBits).sum| ≤
        ((((List.range xs.size).filter fun i => bs[i]!).length - 1 : ℕ) : ℝ) /
          (2 ^ 53 - (((List.range xs.size).filter fun i => bs[i]!).length - 1 : ℕ)) *
          (((List.range xs.size).filter fun i => bs[i]!).map
            fun i => |value xs[i]!.toBits|).sum := by
  rw [select_eq bs xs (by omega)]
  exact sum_bound _ (fun i => xs[i]!) (fun i _ => finite_get xs hf i)
    (lt_of_le_of_lt ((List.length_filter_le _ _).trans (by simp)) hs) hS

/-- The export `select`, called on an array of flags and an array of finite floats, returns a
finite float within `γ_(m-1) Σ |x_i|` of the exact sum `Σ x_i` of the `m` elements whose flag is
true, a missing flag counting as false, when their magnitudes sum to at most `2 ^ 1022`; here
`γ_k = k / (2 ^ 53 - k)`. -/
theorem select_master :
    Verified.Master compiled.module compiled.tables "select" compiled.select.bound
      (fun x : Array Bool × Array Float =>
        let I := (List.range x.2.size).filter fun i => x.1[i]!
        (∀ v ∈ x.2, Finite v.toBits) ∧ (I.map fun i => |value x.2[i]!.toBits|).sum ≤ 2 ^ 1022)
      (fun x (y : Float) =>
        let I := (List.range x.2.size).filter fun i => x.1[i]!
        Finite y.toBits ∧ |value y.toBits - (I.map fun i => value x.2[i]!.toBits).sum| ≤
          ((I.length - 1 : ℕ) : ℝ) / (2 ^ 53 - (I.length - 1 : ℕ)) *
            (I.map fun i => |value x.2[i]!.toBits|).sum) :=
  .of_trapFree (.ofA compiled.select.trapFree) nofun select_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, _, ⟨_, _, hxs⟩⟩ hD =>
      select_spec x.1 x.2 (by have := size_lt hxs.values.size_lt_memory32; omega) hD.1 hD.2

#print axioms select_master

/-! ### `largest` -/

/-- Negative infinity. -/
def negInf : UInt64 := 0xFFF0000000000000

theorem largest_init : (-(1.0 / 0.0) : Float).toBits = negInf := by
  rw [F64Bits.toBits_neg, F64Bits.toBits_div]
  decide +kernel

theorem negInf_not_nan : Wasm.IEEE64.isNaN negInf = false := by decide

/-- Every word that is not a NaN has a scaled value at least that of negative infinity. -/
theorem negInf_le (x : UInt64) (hx : Wasm.IEEE64.isNaN x = false) :
    Wasm.IEEE64.scaledValue negInf ≤ Wasm.IEEE64.scaledValue x := by
  have hn : Wasm.IEEE64.scaledValue negInf = -(2 ^ 2098 : Int) := by decide +kernel
  have hm : Wasm.IEEE64.scaledMagnitude x ≤ 2 ^ 2098 := by
    have he : Wasm.IEEE64.exponent x < 2048 := Nat.mod_lt _ (by norm_num)
    have hf : Wasm.IEEE64.fraction x < 2 ^ 52 := Nat.mod_lt _ (by norm_num)
    unfold Wasm.IEEE64.scaledMagnitude
    by_cases h0 : Wasm.IEEE64.exponent x = 0
    · simp only [h0, beq_self_eq_true, ↓reduceIte]
      have : (2 : ℕ) ^ 52 ≤ 2 ^ 2098 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
      omega
    · simp only [show (Wasm.IEEE64.exponent x == 0) = false by simpa using h0,
        Bool.false_eq_true, ↓reduceIte]
      by_cases h7 : Wasm.IEEE64.exponent x = 2047
      · have hf0 : Wasm.IEEE64.fraction x = 0 := by
          simp only [Wasm.IEEE64.isNaN, h7] at hx
          simpa using hx
        rw [h7, hf0]
        norm_num
      · calc (2 ^ 52 + Wasm.IEEE64.fraction x) * 2 ^ (Wasm.IEEE64.exponent x - 1)
            ≤ 2 ^ 53 * 2 ^ 2045 :=
              Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by norm_num) (by omega))
          _ ≤ 2 ^ 2098 := by norm_num
  have habs : -(Wasm.IEEE64.scaledMagnitude x : Int) ≤ Wasm.IEEE64.scaledValue x := by
    have := neg_abs_le (Wasm.IEEE64.scaledValue x)
    rwa [Int.abs_eq_natAbs, CodeLib.IEEE64.natAbs_scaledValue] at this
  rw [hn]
  have : (Wasm.IEEE64.scaledMagnitude x : Int) ≤ 2 ^ 2098 := by exact_mod_cast hm
  omega

theorem le_bits (a b : Float) (ha : Wasm.IEEE64.isNaN a.toBits = false)
    (hb : Wasm.IEEE64.isNaN b.toBits = false) :
    a ≤ b ↔ Wasm.IEEE64.scaledValue a.toBits ≤ Wasm.IEEE64.scaledValue b.toBits := by
  rw [F64Bits.le_iff]
  simp [Wasm.IEEE64.le, ha, hb]

theorem lt_bits (a b : Float) (ha : Wasm.IEEE64.isNaN a.toBits = false)
    (hb : Wasm.IEEE64.isNaN b.toBits = false) :
    a < b ↔ Wasm.IEEE64.scaledValue a.toBits < Wasm.IEEE64.scaledValue b.toBits := by
  rw [F64Bits.lt_iff]
  simp [Wasm.IEEE64.lt, ha, hb]

/-- The state after the first `k` elements: negative infinity when they are all NaNs, and
otherwise the last of them that is not a NaN and that none of them exceeds. -/
def LargestInv (xs : Array Float) (k : ℕ) (acc : Float) : Prop :=
  (acc.toBits = negInf ∧ ∀ j < k, Wasm.IEEE64.isNaN xs[j]!.toBits = true) ∨
  ∃ i < k, Wasm.IEEE64.isNaN xs[i]!.toBits = false ∧ acc.toBits = xs[i]!.toBits ∧
    (∀ j < k, Wasm.IEEE64.isNaN xs[j]!.toBits = false →
      Wasm.IEEE64.scaledValue xs[j]!.toBits ≤ Wasm.IEEE64.scaledValue xs[i]!.toBits) ∧
    ∀ j, i < j → j < k → Wasm.IEEE64.isNaN xs[j]!.toBits = false →
      Wasm.IEEE64.scaledValue xs[j]!.toBits < Wasm.IEEE64.scaledValue xs[i]!.toBits

theorem largestInv_step (xs : Array Float) (k : ℕ) (acc : Float) (h : LargestInv xs k acc) :
    LargestInv xs (k + 1) (max acc xs[k]!) := by
  have hmax := F64Bits.toBits_max acc xs[k]!
  by_cases hk : Wasm.IEEE64.isNaN xs[k]!.toBits = true
  · have hle : Wasm.IEEE64.le acc.toBits xs[k]!.toBits = false := by
      simp [Wasm.IEEE64.le, hk]
    rw [hle] at hmax
    simp only [Bool.false_eq_true, ↓reduceIte] at hmax
    rcases h with ⟨h1, h2⟩ | ⟨i, hi, hn, he, hle', hlt⟩
    · exact Or.inl ⟨hmax.trans h1, fun j hj => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact h2 j hj
        · exact hk⟩
    · refine Or.inr ⟨i, by omega, hn, hmax.trans he, fun j hj hjn => ?_, fun j hij hj hjn => ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact hle' j hj hjn
        · rw [hk] at hjn; exact absurd hjn (by decide)
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact hlt j hij hj hjn
        · rw [hk] at hjn; exact absurd hjn (by decide)
  · have hk' : Wasm.IEEE64.isNaN xs[k]!.toBits = false := by simpa using hk
    rcases h with ⟨h1, h2⟩ | ⟨i, hi, hn, he, hle', hlt⟩
    · have hle : Wasm.IEEE64.le acc.toBits xs[k]!.toBits = true := by
        simp only [Wasm.IEEE64.le, h1, negInf_not_nan, hk', Bool.or_self, Bool.false_eq_true,
          ↓reduceIte, decide_eq_true_eq]
        exact negInf_le _ hk'
      rw [hle] at hmax
      simp only [↓reduceIte] at hmax
      refine Or.inr ⟨k, by omega, hk', hmax, fun j hj hjn => ?_, fun j hkj hj _ => by omega⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [h2 j hj] at hjn; exact absurd hjn (by decide)
      · exact le_rfl
    · by_cases hc : Wasm.IEEE64.scaledValue xs[i]!.toBits ≤ Wasm.IEEE64.scaledValue xs[k]!.toBits
      · have hle : Wasm.IEEE64.le acc.toBits xs[k]!.toBits = true := by
          simp only [Wasm.IEEE64.le, he, hn, hk', Bool.or_self, Bool.false_eq_true, ↓reduceIte,
            decide_eq_true_eq]
          exact hc
        rw [hle] at hmax
        simp only [↓reduceIte] at hmax
        refine Or.inr ⟨k, by omega, hk', hmax, fun j hj hjn => ?_, fun j hkj hj _ => by omega⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact (hle' j hj hjn).trans hc
        · exact le_rfl
      · have hle : Wasm.IEEE64.le acc.toBits xs[k]!.toBits = false := by
          simp only [Wasm.IEEE64.le, he, hn, hk', Bool.or_self, Bool.false_eq_true, ↓reduceIte,
            decide_eq_false_iff_not]
          exact hc
        rw [hle] at hmax
        simp only [Bool.false_eq_true, ↓reduceIte] at hmax
        refine Or.inr ⟨i, by omega, hn, hmax.trans he, fun j hj hjn => ?_,
          fun j hij hj hjn => ?_⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
          · exact hle' j hj hjn
          · exact (lt_of_not_ge hc).le
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
          · exact hlt j hij hj hjn
          · exact lt_of_not_ge hc

theorem largest_inv (xs : Array Float) (h : xs.size < 2 ^ 64) :
    LargestInv xs xs.size (largest xs) := by
  have h1 : largest xs = (List.range xs.size.toUInt64.toNat).foldl
      (fun acc i => max acc xs[i]!) (-(1.0 / 0.0)) :=
    loop_toNat _ _ (fun j acc => max acc xs[j]!)
  rw [h1, size_toUInt64 xs h]
  generalize xs.size = n
  induction n with
  | zero => exact Or.inl ⟨largest_init, fun j hj => absurd hj (by omega)⟩
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact largestInv_step xs k _ ih

/-- The export `largest`, called on an array of floats, returns negative infinity when every
element is a NaN, the empty array included, and otherwise the last element that is not a NaN and
that no element exceeds in the IEEE 754 order of `Float`.  For finite elements, the result is
therefore an element of the largest value, the last one among equal values such as `+0` and
`-0`. -/
theorem largest_master :
    Verified.Master compiled.module compiled.tables "largest" compiled.largest.bound
      (fun _ => True)
      (fun (xs : Array Float) (y : Float) =>
        ((∀ x ∈ xs, Wasm.IEEE64.isNaN x.toBits = true) → y.toBits = 0xFFF0000000000000) ∧
        ((∃ x ∈ xs, Wasm.IEEE64.isNaN x.toBits = false) →
          ∃ i, ∃ hi : i < xs.size, Wasm.IEEE64.isNaN xs[i].toBits = false ∧
            y.toBits = xs[i].toBits ∧
            (∀ j, ∀ hj : j < xs.size, Wasm.IEEE64.isNaN xs[j].toBits = false → xs[j] ≤ xs[i]) ∧
            ∀ j, ∀ hj : j < xs.size, i < j → Wasm.IEEE64.isNaN xs[j].toBits = false →
              xs[j] < xs[i])) :=
  .of_trapFree (.ofA compiled.largest.trapFree) nofun largest_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ xs ⟨_, _, hxs⟩ _ => by
      have hs := size_lt hxs.values.size_lt_memory32
      have hinv := largest_inv xs (by omega)
      have hget : ∀ j (hj : j < xs.size), xs[j]! = xs[j] := fun j hj => getElem!_pos xs j hj
      refine ⟨fun hall => ?_, fun ⟨x, hx, hxn⟩ => ?_⟩
      · rcases hinv with ⟨h1, _⟩ | ⟨i, hi, hn, _, _, _⟩
        · exact h1
        · rw [hget i hi, hall _ (Array.getElem_mem hi)] at hn
          exact absurd hn (by decide)
      · rcases hinv with ⟨_, h2⟩ | ⟨i, hi, hn, he, hle, hlt⟩
        · obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp hx
          have := h2 j hj
          rw [hget j hj, hxn] at this
          exact absurd this (by decide)
        · rw [hget i hi] at hn he
          refine ⟨i, hi, hn, he, fun j hj hjn => ?_, fun j hj hij hjn => ?_⟩
          · have := hle j hj (by rw [hget j hj]; exact hjn)
            rw [hget j hj, hget i hi] at this
            exact (le_bits _ _ hjn hn).mpr this
          · have := hlt j hij hj (by rw [hget j hj]; exact hjn)
            rw [hget j hj, hget i hi] at this
            exact (lt_bits _ _ hjn hn).mpr this

#print axioms largest_master

/-! ### `sumRange` -/

theorem sub_half (d : UInt64) : (d - d / 2).toNat = d.toNat - d.toNat / 2 := by
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
    rw [UInt64.toNat_div]; exact Nat.div_le_self _ _)), UInt64.toNat_div]
  rfl

theorem fits_true (xs : Array Float) (k : ℕ) :
    ∀ lo hi : UInt64, (hi - lo).toNat ≤ 2 ^ k → ∀ j,
      compiled.sumRange.fits (k + 1 + j) (xs, lo, hi) = true := by
  induction k with
  | zero =>
    intro lo hi h j
    rw [show 0 + 1 + j = j + 1 by omega, compiled.sumRange.fits_eq,
      ite_eq_left (UInt64.le_iff_toNat_le.mpr (by simpa using h))]
  | succ k ih =>
    intro lo hi h j
    rw [show k + 1 + 1 + j = (k + 1 + j) + 1 by omega, compiled.sumRange.fits_eq]
    split
    · rfl
    · have e1 : lo + (hi - lo) / 2 - lo = (hi - lo) / 2 := by
        rw [UInt64.add_comm, UInt64.add_sub_cancel]
      have e2 : hi - (lo + (hi - lo) / 2) = (hi - lo) - (hi - lo) / 2 := by
        rw [UInt64.sub_eq_iff_eq_add, UInt64.add_comm lo, ← UInt64.add_assoc,
          UInt64.sub_add_cancel, UInt64.sub_add_cancel]
      have h1 := ih lo (lo + (hi - lo) / 2) (by
        rw [e1, UInt64.toNat_div]
        have : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
        simp only [UInt64.reduceToNat]
        omega) j
      have h2 := ih (lo + (hi - lo) / 2) hi (by
        rw [e2, sub_half]
        have : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
        omega) j
      rw [h1, h2]
      rfl

theorem fits_1000 (x : Array Float × UInt64 × UInt64) : compiled.sumRange.fits 1000 x = true := by
  obtain ⟨xs, lo, hi⟩ := x
  have h := fits_true xs 64 lo hi (UInt64.toNat_lt _).le 935
  exact h

theorem clog_le (n : ℕ) (hn : n ≤ 2 ^ 64) : Nat.clog 2 n ≤ 64 :=
  Nat.clog_le_of_le_pow hn

/-- The error of `sumRange` on `[lo, hi)`: `(1 + 2 ^ -53) ^ ⌈log₂ n⌉ - 1` times the sum of the
magnitudes, for `n = hi - lo`. -/
theorem sumRange_approx (xs : Array Float) (hf : ∀ x ∈ xs, Finite x.toBits) (n : ℕ) :
    ∀ lo hi : UInt64, lo ≤ hi → hi.toNat - lo.toNat = n →
      ∑ i ∈ Finset.Ico lo.toNat hi.toNat, |value xs[i]!.toBits| ≤ 2 ^ 1022 →
      FApprox (sumRange xs lo hi) (∑ i ∈ Finset.Ico lo.toNat hi.toNat, value xs[i]!.toBits)
        (((1 + 1 / 2 ^ 53 : ℝ) ^ Nat.clog 2 n - 1) *
          ∑ i ∈ Finset.Ico lo.toNat hi.toNat, |value xs[i]!.toBits|) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro lo hi hlh hn hV
  have hlh' : lo.toNat ≤ hi.toNat := UInt64.le_iff_toNat_le.mp hlh
  have hd : (hi - lo).toNat = n := by rw [UInt64.toNat_sub_of_le _ _ hlh]; exact hn
  rw [sumRange]
  split
  · rename_i hle
    have hn1 : n ≤ 1 := by rw [← hd]; exact UInt64.le_iff_toNat_le.mp hle
    split
    · rename_i heq
      have hn1' : n = 1 := by rw [← hd, heq]; rfl
      have hI : Finset.Ico lo.toNat hi.toNat = {lo.toNat} := by
        rw [show hi.toNat = lo.toNat + 1 by omega]
        exact Nat.Ico_succ_singleton _
      rw [hI, Finset.sum_singleton, Finset.sum_singleton, hn1']
      simp only [Nat.clog_one_right, pow_zero, sub_self, zero_mul]
      exact approx_self _ (finite_get xs hf _)
    · rename_i hne
      have hn0 : n = 0 := by
        rcases Nat.lt_or_ge n 1 with h | h
        · omega
        · exfalso; apply hne
          apply UInt64.toNat_inj.mp
          rw [hd]; simp; omega
      have hI : Finset.Ico lo.toNat hi.toNat = ∅ := Finset.Ico_eq_empty (by omega)
      rw [hI, Finset.sum_empty, Finset.sum_empty, mul_zero]
      refine ⟨by rw [zero_bits]; exact finite_zero, ?_⟩
      rw [zero_bits, value_zero]; simp
  · rename_i hgt
    have hn2 : 2 ≤ n := by
      have := UInt64.le_iff_toNat_le.not.mp hgt
      rw [hd] at this
      simp at this
      omega
    set mid := lo + (hi - lo) / 2 with hmid
    have hmidN : mid.toNat = lo.toNat + n / 2 := by
      rw [hmid, UInt64.toNat_add, UInt64.toNat_div, hd]
      simp only [UInt64.reduceToNat]
      have := hi.toNat_lt
      rw [Nat.mod_eq_of_lt (by omega)]
    have hlm : lo ≤ mid := UInt64.le_iff_toNat_le.mpr (by omega)
    have hmh : mid ≤ hi := UInt64.le_iff_toNat_le.mpr (by omega)
    have hsplit (f : ℕ → ℝ) : ∑ i ∈ Finset.Ico lo.toNat hi.toNat, f i =
        ∑ i ∈ Finset.Ico lo.toNat mid.toNat, f i + ∑ i ∈ Finset.Ico mid.toNat hi.toNat, f i :=
      (Finset.sum_Ico_consecutive f (by omega) (by omega)).symm
    have hV1 : 0 ≤ ∑ i ∈ Finset.Ico lo.toNat mid.toNat, |value xs[i]!.toBits| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hV2 : 0 ≤ ∑ i ∈ Finset.Ico mid.toNat hi.toNat, |value xs[i]!.toBits| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    rw [hsplit] at hV ⊢
    rw [hsplit]
    have h1 := ih (n / 2) (by omega) lo mid hlm (by omega) (by linarith)
    have h2 := ih (n - n / 2) (by omega) mid hi hmh (by omega) (by linarith)
    have hd1 : Nat.clog 2 n = Nat.clog 2 (n - n / 2) + 1 := by
      rw [Nat.clog_of_two_le (by norm_num) hn2]
      congr 2
      omega
    have hc1 : Nat.clog 2 (n / 2) ≤ Nat.clog 2 n - 1 := by
      have := Nat.clog_mono_right 2 (show n / 2 ≤ n - n / 2 by omega)
      omega
    have hc2 : Nat.clog 2 (n - n / 2) = Nat.clog 2 n - 1 := by omega
    have hdle : Nat.clog 2 n ≤ 64 := clog_le n (by
      have := hi.toNat_lt
      have : UInt64.size = 2 ^ 64 := rfl
      omega)
    rw [hc2] at h2
    have hpowd : (1 + 1 / 2 ^ 53 : ℝ) ^ Nat.clog 2 n =
        (1 + 1 / 2 ^ 53) * (1 + 1 / 2 ^ 53 : ℝ) ^ (Nat.clog 2 n - 1) := by
      rw [← pow_succ', show Nat.clog 2 n - 1 + 1 = Nat.clog 2 n by omega]
    have hmono := pow_le_pow_right₀ (show (1 : ℝ) ≤ 1 + 1 / 2 ^ 53 by norm_num) hc1
    have hQ2 : (1 + 1 / 2 ^ 53 : ℝ) ^ (Nat.clog 2 n - 1) < 2 :=
      pow_le_two 53 (Nat.clog 2 n - 1) (by
        have : ((Nat.clog 2 n - 1 : ℕ) : ℝ) ≤ 64 := by
          exact_mod_cast (Nat.sub_le _ _).trans hdle
        linarith)
    rw [hpowd]
    set Q := (1 + 1 / 2 ^ 53 : ℝ) ^ (Nat.clog 2 n - 1)
    set V1 := ∑ i ∈ Finset.Ico lo.toNat mid.toNat, |value xs[i]!.toBits|
    set V2 := ∑ i ∈ Finset.Ico mid.toNat hi.toNat, |value xs[i]!.toBits|
    set S1 := ∑ i ∈ Finset.Ico lo.toNat mid.toNat, value xs[i]!.toBits
    set S2 := ∑ i ∈ Finset.Ico mid.toNat hi.toNat, value xs[i]!.toBits
    have hQ1 : 1 ≤ Q := one_le_pow₀ (by norm_num)
    have he1 : ((1 + 1 / 2 ^ 53 : ℝ) ^ Nat.clog 2 (n / 2) - 1) * V1 ≤ (Q - 1) * V1 :=
      mul_le_mul_of_nonneg_right (by linarith) hV1
    have hS1 : |S1| ≤ V1 := Finset.abs_sum_le_sum_abs _ _
    have hS2 : |S2| ≤ V2 := Finset.abs_sum_le_sum_abs _ _
    have hS : |S1 + S2| ≤ V1 + V2 := (abs_add_le _ _).trans (add_le_add hS1 hS2)
    have hB : |S1 + S2| + ((Q - 1) * V1 + (Q - 1) * V2) ≤ Q * (V1 + V2) := by nlinarith
    have hQV : Q * (V1 + V2) < 2 ^ 1023 := by
      have : Q * (V1 + V2) ≤ Q * 2 ^ 1022 := mul_le_mul_of_nonneg_left hV (by linarith)
      have : Q * (2 : ℝ) ^ 1022 < 2 * 2 ^ 1022 := by
        exact (mul_lt_mul_iff_left₀ (by positivity)).mpr hQ2
      linarith
    have hadd := fapprox_add (h1.mono he1) h2 (Q * (V1 + V2)) hB hQV
    refine hadd.mono ?_
    have : 0 ≤ Q * (V1 + V2) := by positivity
    have e : ((1 + 1 / 2 ^ 53) * Q - 1) * (V1 + V2) =
        (Q - 1) * V1 + (Q - 1) * V2 + Q * (V1 + V2) / 2 ^ 53 := by ring
    rw [e]

/-- `sumRange_approx` in closed form. -/
theorem sumRange_spec (xs : Array Float) (lo hi : UInt64) (hf : ∀ x ∈ xs, Finite x.toBits)
    (hlh : lo ≤ hi) (hV : ∑ i ∈ Finset.Ico lo.toNat hi.toNat, |value xs[i]!.toBits| ≤ 2 ^ 1022) :
    Finite (sumRange xs lo hi).toBits ∧
      |value (sumRange xs lo hi).toBits -
          ∑ i ∈ Finset.Ico lo.toNat hi.toNat, value xs[i]!.toBits| ≤
        (Nat.clog 2 (hi.toNat - lo.toNat) : ℝ) / (2 ^ 53 - Nat.clog 2 (hi.toNat - lo.toNat)) *
          ∑ i ∈ Finset.Ico lo.toNat hi.toNat, |value xs[i]!.toBits| := by
  have h := sumRange_approx xs hf _ lo hi hlh rfl hV
  refine ⟨h.1, h.2.trans (mul_le_mul_of_nonneg_right (gamma_pow 53 _ ?_)
    (Finset.sum_nonneg fun _ _ => abs_nonneg _))⟩
  have := clog_le (hi.toNat - lo.toNat) (by
    have := hi.toNat_lt
    have : UInt64.size = 2 ^ 64 := rfl
    omega)
  have : (Nat.clog 2 (hi.toNat - lo.toNat) : ℝ) ≤ 64 := by exact_mod_cast this
  linarith

/-- The export `sumRange`, called on an array of finite floats and words `lo ≤ hi`, sums the
elements of indices `lo` to `hi - 1` by halves, each missing element counting as 0, and returns a
finite float within `γ_d Σ |x_i|` of the exact sum `Σ x_i`, where `d = ⌈log₂ (hi - lo)⌉` and
`γ_k = k / (2 ^ 53 - k)`, when the magnitudes sum to at most `2 ^ 1022`.  The recursion depth is
at most 65, so the call stays within the compiler's limit of 1,000 frames. -/
theorem sumRange_master :
    Verified.Master compiled.module compiled.tables "sumRange" (compiled.sumRange.bound 1000)
      (fun x : Array Float × UInt64 × UInt64 => (∀ v ∈ x.1, Finite v.toBits) ∧ x.2.1 ≤ x.2.2 ∧
        ∑ i ∈ Finset.Ico x.2.1.toNat x.2.2.toNat, |value x.1[i]!.toBits| ≤ 2 ^ 1022)
      (fun x (y : Float) => Finite y.toBits ∧
        |value y.toBits - ∑ i ∈ Finset.Ico x.2.1.toNat x.2.2.toNat, value x.1[i]!.toBits| ≤
          (Nat.clog 2 (x.2.2.toNat - x.2.1.toNat) : ℝ) /
            (2 ^ 53 - Nat.clog 2 (x.2.2.toNat - x.2.1.toNat)) *
            ∑ i ∈ Finset.Ico x.2.1.toNat x.2.2.toNat, |value x.1[i]!.toBits|) :=
  .of_trapFree (.ofA compiled.sumRange.trapFree) nofun sumRange_export
    (fun x _ _ _ h => ⟨fits_1000 x, h⟩) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ hD => sumRange_spec x.1 x.2.1 x.2.2 hD.1 hD.2.1 hD.2.2

#print axioms sumRange_master

end Library.Numerics.Reductions.Float64
