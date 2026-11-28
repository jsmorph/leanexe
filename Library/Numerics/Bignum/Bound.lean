module

public import Library.Numerics.Bignum.OfText
public import Library.Numerics.Bignum.Compiled
public import Verified.ChargeFacts

@[expose] public section

/-!
Closed forms of the generated allocation bounds.  Each bound is the number of bytes by which a call
can raise the allocator's `top`, and it credits no freed block.  The bounds of MultiPrecision's
`add`, `sub`, and `mulSmall` are the smaller of two accountings of a loop of pushes, and the paid one
charges `paidGrowCost 1 = 80` bytes for each push after a credit of 16 bytes for the empty array
(`loopCost_const`), with one more growth for the final push of `add` and `mulSmall`.  `mul`, `shortDiv`,
`natTrim`, and `slice` build one block each, and the loops that write into arrays of their state
cost nothing.  `divide_bound_le` covers Algorithm D's normalized arguments, quotient block, short
division of the remainder, and result block.
-/

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision
open LeanExe.Dialect
open Verified (blockCost growCost paidGrowCost creditCost loopCost)

/-! ## Sizes after loops -/

/-- A loop that pushes one word onto the array of its state at each pass. -/
theorem loop_push_size2 {β : Type} (n : UInt64) (init : β × Array UInt64)
    (F : UInt64 → β × Array UInt64 → β × Array UInt64)
    (hF : ∀ i s, (F i s).2.size = s.2.size + 1) :
    (LeanExe.loop n init F).2.size = init.2.size + n.toNat :=
  loop_induction (P := fun k (s : β × Array UInt64) => s.2.size = init.2.size + k) rfl
    (fun k s _ h => by rw [hF, h]; omega)

/-- A loop whose passes keep the size of the array of its state. -/
theorem loop_keep_size2 {β : Type} (n : UInt64) (init : β × Array UInt64)
    (F : UInt64 → β × Array UInt64 → β × Array UInt64)
    (hF : ∀ i s, (F i s).2.size = s.2.size) :
    (LeanExe.loop n init F).2.size = init.2.size :=
  loop_induction (P := fun _ (s : β × Array UInt64) => s.2.size = init.2.size) rfl
    (fun k s _ h => by rw [hF, h])

theorem toNat_size {u : Array UInt64} (h : u.size < 2 ^ 32) : u.size.toUInt64.toNat = u.size :=
  size_toNat (by omega)

/-! ## The reused functions -/

theorem add_bound_le (u v : Array UInt64) (hu : u.size < 2 ^ 32) (hv : v.size < 2 ^ 32) :
    compiled.add.bound (u, v) ≤ 96 * max u.size v.size + 168 := by
  rw [compiled.add.bound_eq]
  have hw := width_toNat (u := u) (v := v) (by omega) (by omega)
  have hs := loop_push_size2 (width u v) ((0 : UInt64), (#[] : Array UInt64))
    (fun j s => ((u[j.toNat]! + v[j.toNat]! + s.1) / 4294967296,
      s.2.push ((u[j.toNat]! + v[j.toNat]! + s.1) % 4294967296))) (fun _ _ => by simp)
  rw [hs]
  refine le_trans (Nat.add_le_add_right (min_le_right _ _) _) ?_
  rw [Verified.loopCost_const, hw, Verified.blockCost_eq, Verified.growCost_eq, Verified.paidGrowCost_eq]
  simp [Verified.creditCost]
  omega

theorem sub_bound_le (u v : Array UInt64) (hu : u.size < 2 ^ 32) (hv : v.size < 2 ^ 32) :
    compiled.sub.bound (u, v) ≤ 80 * max u.size v.size + 72 := by
  rw [compiled.sub.bound_eq]
  have hw := width_toNat (u := u) (v := v) (by omega) (by omega)
  refine le_trans (min_le_right _ _) ?_
  rw [Verified.loopCost_const, hw, Verified.blockCost_eq, Verified.paidGrowCost_eq]
  simp [Verified.creditCost]
  omega

theorem mul_bound_le (u v : Array UInt64) (hu : u.size < 2 ^ 32) (hv : v.size < 2 ^ 32) :
    compiled.mul.bound (u, v) ≤ 8 * (u.size + v.size) + 56 := by
  rw [compiled.mul.bound_eq, Verified.blockCost_eq, UInt64.toNat_add, toNat_size hu, toNat_size hv]
  have := Nat.mod_le (u.size + v.size) (2 ^ 64)
  omega

/-- A loop that pushes one word onto the array in the first component of its state. -/
theorem loop_push_size1 {β : Type} (n : UInt64) (init : Array UInt64 × β)
    (F : UInt64 → Array UInt64 × β → Array UInt64 × β)
    (hF : ∀ i s, (F i s).1.size = s.1.size + 1) :
    (LeanExe.loop n init F).1.size = init.1.size + n.toNat :=
  loop_induction (P := fun k (s : Array UInt64 × β) => s.1.size = init.1.size + k) rfl
    (fun k s _ h => by rw [hF, h]; omega)

theorem mulSmall_bound_le (a : Array UInt64) (m c : UInt64) (ha : a.size < 2 ^ 32) :
    compiled.mulSmall.bound (a, m, c) ≤ 96 * a.size + 168 := by
  rw [compiled.mulSmall.bound_eq]
  have hs := loop_push_size1 a.size.toUInt64 (LeanExe.build 0 fun _ => (0 : UInt64), c)
    (fun i (s : Array UInt64 × UInt64) =>
      have t := a[i.toNat]! * m + s.2
      (s.1.push (t &&& 4294967295), t >>> 32)) (fun _ _ => by simp)
  rw [hs, build_size]
  refine le_trans (Nat.add_le_add_right (min_le_right _ _) _) ?_
  rw [Verified.loopCost_const, toNat_size ha, Verified.blockCost_eq, Verified.growCost_eq,
    Verified.paidGrowCost_eq]
  simp [Verified.creditCost]
  omega

theorem shortDiv_bound_le (x : Array UInt64) (d len : UInt64) :
    compiled.shortDiv.bound (x, d, len) ≤ 24 * len.toNat + 152 := by
  rw [compiled.shortDiv.bound_eq]
  rw [loop_keep_size2 len _ _ (fun _ _ => by simp), build_size, Verified.blockCost_eq,
    Verified.growCost_eq]
  omega

theorem longDiv_bound_le (u v : Array UInt64) (t : UInt64) (hu : u.size < 2 ^ 32)
    (hv : v.size < 2 ^ 32) :
    compiled.longDiv.bound (u, v, t) ≤ 112 * u.size + 104 * v.size + 24 * t.toNat + 600 := by
  rw [compiled.longDiv.bound_eq]
  have h1 := mulSmall_bound_le v
    (1 <<< (32 - Library.Numerics.Arithmetic.Uscale.wordBits v[(t - 1).toNat]!)) 0 hv
  have h2 := mulSmall_bound_le u
    (1 <<< (32 - Library.Numerics.Arithmetic.Uscale.wordBits v[(t - 1).toNat]!)) 0 hu
  have h4 : (u.size.toUInt64 + v.size.toUInt64).toNat = u.size + v.size := by
    rw [UInt64.toNat_add, toNat_size hu, toNat_size hv]; omega
  rw [h4, toNat_size hu, Verified.blockCost_eq, Verified.blockCost_eq]
  refine le_trans (Nat.add_le_add h1 (Nat.add_le_add (Nat.add_le_add_left h2 _)
    (Nat.add_le_add_right (shortDiv_bound_le _ _ _) _))) ?_
  omega

theorem divide_bound_le (u v : Array UInt64) (hu : u.size < 2 ^ 32) (hv : v.size < 2 ^ 32) :
    compiled.divide.bound (u, v) ≤ 112 * u.size + 128 * v.size + 600 := by
  rw [compiled.divide.bound_eq]
  have h4 : (u.size.toUInt64 + v.size.toUInt64).toNat = u.size + v.size := by
    rw [UInt64.toNat_add, toNat_size hu, toNat_size hv]; omega
  split
  · rw [h4, Verified.blockCost_eq]; omega
  · split
    · have := shortDiv_bound_le u v[UInt64.toNat 0]! u.size.toUInt64
      rw [toNat_size hu] at this
      rw [h4, Verified.blockCost_eq]; omega
    · have := longDiv_bound_le u v (significant v) hu hv
      have := (significant_spec v (by omega)).1
      omega

theorem natTrim_bound_le (u : Array UInt64) (hu : u.size < 2 ^ 64) :
    compiled.natTrim.bound u ≤ 8 * u.size + 56 := by
  rw [compiled.natTrim.bound_eq, Verified.blockCost_eq]
  have := (significant_spec u (by omega)).1
  omega

/-! ## The natural exports -/

theorem add_size (u v : Array UInt64) (hu : u.size < 2 ^ 32) (hv : v.size < 2 ^ 32) :
    (add u v).size = max u.size v.size + 1 := by
  unfold add
  rw [Array.size_push, loop_push_size2 _ _ _ (fun _ _ => by simp), width_toNat (by omega) (by omega)]
  simp

theorem natAdd_bound_le (u v : Array UInt64) (hu : u.size < 2 ^ 32) (hv : v.size < 2 ^ 32) :
    compiled.natAdd.bound (u, v) ≤ 104 * max u.size v.size + 232 := by
  rw [compiled.natAdd.bound_eq]
  have h1 := add_bound_le u v hu hv
  have h2 := natTrim_bound_le (add u v) (by rw [add_size u v hu hv]; omega)
  rw [add_size u v hu hv] at h2
  omega

theorem sub_size (u v : Array UInt64) (hu : u.size < 2 ^ 32) (hv : v.size < 2 ^ 32) :
    (sub u v).size = max u.size v.size := by
  unfold sub
  rw [loop_push_size2 _ _ _ (fun _ _ => by simp), width_toNat (by omega) (by omega)]
  simp

theorem natSub_bound_le (u v : Array UInt64) (hu : u.size < 2 ^ 32) (hv : v.size < 2 ^ 32) :
    compiled.natSub.bound (u, v) ≤ 88 * max u.size v.size + 128 := by
  rw [compiled.natSub.bound_eq]
  split
  · have h1 := sub_bound_le u v hu hv
    have h2 := natTrim_bound_le (sub u v) (by rw [sub_size u v hu hv]; omega)
    rw [sub_size u v hu hv] at h2
    omega
  · have h1 := sub_bound_le v u hv hu
    have h2 := natTrim_bound_le (sub v u) (by rw [sub_size v u hv hu]; omega)
    rw [sub_size v u hv hu] at h2
    omega

theorem mul_size (u v : Array UInt64) (hu : u.size < 2 ^ 32) (hv : v.size < 2 ^ 32) :
    (mul u v).size = u.size + v.size := by
  unfold mul
  have key := loop_induction (n := v.size.toUInt64)
    (init := LeanExe.build (u.size.toUInt64 + v.size.toUInt64) fun _ => (0 : UInt64))
    (f := fun j w =>
      (LeanExe.loop u.size.toUInt64 ((0 : UInt64), w) fun i s =>
        ((u[i.toNat]! * v[j.toNat]! + s.2[(i + j).toNat]! + s.1) / 4294967296,
          s.2.set! (i + j).toNat
            ((u[i.toNat]! * v[j.toNat]! + s.2[(i + j).toNat]! + s.1) % 4294967296))).2.set!
        (j + u.size.toUInt64).toNat
        (LeanExe.loop u.size.toUInt64 ((0 : UInt64), w) fun i s =>
          ((u[i.toNat]! * v[j.toNat]! + s.2[(i + j).toNat]! + s.1) / 4294967296,
            s.2.set! (i + j).toNat
              ((u[i.toNat]! * v[j.toNat]! + s.2[(i + j).toNat]! + s.1) % 4294967296))).1)
    (fun _ (w : Array UInt64) => w.size = u.size + v.size)
    (by rw [build_size, UInt64.toNat_add, toNat_size hu, toNat_size hv]; omega)
    (fun k w _ h => by
      rw [Array.size_set!, loop_keep_size2 _ _ _ (fun _ _ => by simp)]
      exact h)
  exact key

theorem natMul_bound_le (u v : Array UInt64) (hu : u.size < 2 ^ 32) (hv : v.size < 2 ^ 32) :
    compiled.natMul.bound (u, v) ≤ 16 * (u.size + v.size) + 112 := by
  rw [compiled.natMul.bound_eq]
  have h1 := mul_bound_le u v hu hv
  have h2 := natTrim_bound_le (mul u v) (by rw [mul_size u v hu hv]; omega)
  rw [mul_size u v hu hv] at h2
  omega

theorem slice_size (w : Array UInt64) (start len : UInt64) : (slice w start len).size = len.toNat :=
  build_size _ _

/-- The cost of the division of Lean's convention for a divisor that is not empty, which the
generated bounds expand inline. -/
theorem divCost_le (u v : Array UInt64) (hu : u.size < 2 ^ 32) (hv : v.size < 2 ^ 32) :
    compiled.divide.bound (u, v) +
        (blockCost u.size.toUInt64.toNat +
            compiled.natTrim.bound (slice (divide u v) 0 u.size.toUInt64) +
          (blockCost v.size.toUInt64.toNat +
            compiled.natTrim.bound (slice (divide u v) u.size.toUInt64 v.size.toUInt64))) ≤
      128 * u.size + 144 * v.size + 824 := by
  have h1 := divide_bound_le u v hu hv
  have h2 := natTrim_bound_le (slice (divide u v) 0 u.size.toUInt64)
    (by rw [slice_size, toNat_size hu]; omega)
  have h3 := natTrim_bound_le (slice (divide u v) u.size.toUInt64 v.size.toUInt64)
    (by rw [slice_size, toNat_size hv]; omega)
  rw [slice_size, toNat_size hu] at h2
  rw [slice_size, toNat_size hv] at h3
  rw [toNat_size hu, toNat_size hv, Verified.blockCost_eq, Verified.blockCost_eq]
  omega

theorem natDivModChecked_bound_le (u v : Array UInt64) (hu : u.size < 2 ^ 32)
    (hv : v.size < 2 ^ 32) :
    compiled.natDivModChecked.bound (u, v) ≤ 128 * u.size + 144 * v.size + 824 := by
  rw [compiled.natDivModChecked.bound_eq]
  split
  · rw [show UInt64.toNat 0 = 0 from rfl, Verified.blockCost_eq]; omega
  · exact divCost_le u v hu hv

/-! ## The integer exports -/

theorem intNeg_bound_le (x : BigInt) (hx : x.mag.size < 2 ^ 32) :
    compiled.intNeg.bound x ≤ 8 * x.mag.size + 56 := by
  rw [compiled.intNeg.bound_eq]; exact natTrim_bound_le _ (by omega)

theorem intAdd_bound_le (x y : BigInt) (hx : x.mag.size < 2 ^ 32) (hy : y.mag.size < 2 ^ 32) :
    compiled.intAdd.bound (x, y) ≤ 104 * max x.mag.size y.mag.size + 232 := by
  rw [compiled.intAdd.bound_eq]
  split
  · exact natAdd_bound_le _ _ hx hy
  · have := natSub_bound_le _ _ hx hy; omega

theorem intSub_bound_le (x y : BigInt) (hx : x.mag.size < 2 ^ 32) (hy : y.mag.size < 2 ^ 32) :
    compiled.intSub.bound (x, y) ≤ 104 * max x.mag.size y.mag.size + 232 := by
  rw [compiled.intSub.bound_eq]
  split
  · exact natAdd_bound_le _ _ hx hy
  · have := natSub_bound_le _ _ hx hy; omega

theorem intMul_bound_le (x y : BigInt) (hx : x.mag.size < 2 ^ 32) (hy : y.mag.size < 2 ^ 32) :
    compiled.intMul.bound (x, y) ≤ 16 * (x.mag.size + y.mag.size) + 112 := by
  rw [compiled.intMul.bound_eq]; exact natMul_bound_le _ _ hx hy

theorem intTDivModChecked_bound_le (x y : BigInt) (hx : x.mag.size < 2 ^ 32)
    (hy : y.mag.size < 2 ^ 32) :
    compiled.intTDivModChecked.bound (x, y) ≤ 128 * x.mag.size + 144 * y.mag.size + 824 := by
  rw [compiled.intTDivModChecked.bound_eq]
  split
  · rw [show UInt64.toNat 0 = 0 from rfl, Verified.blockCost_eq]; omega
  · exact divCost_le _ _ hx hy

theorem natDivMod_size (u v : Array UInt64) (hu : u.size < 2 ^ 32) (hv : v.size < 2 ^ 32)
    (hv0 : v.size ≠ 0) : (natDivMod u v).1.size ≤ u.size ∧ (natDivMod u v).2.size ≤ v.size := by
  unfold natDivMod
  rw [size_toUInt64_beq_zero (by omega), decide_eq_false hv0, ite_eq_right (by decide)]
  dsimp only
  rw [natTrim_size, natTrim_size]
  have h1 := (significant_spec (slice (divide u v) 0 u.size.toUInt64) (by
    rw [slice_size, toNat_size hu]; omega)).1
  have h2 := (significant_spec (slice (divide u v) u.size.toUInt64 v.size.toUInt64) (by
    rw [slice_size, toNat_size hv]; omega)).1
  rw [slice_size, toNat_size hu] at h1
  rw [slice_size, toNat_size hv] at h2
  exact ⟨h1, h2⟩

theorem intEDivModChecked_bound_le (x y : BigInt) (hx : x.mag.size < 2 ^ 32)
    (hy : y.mag.size < 2 ^ 32) :
    compiled.intEDivModChecked.bound (x, y) ≤ 232 * x.mag.size + 232 * y.mag.size + 1440 := by
  rw [compiled.intEDivModChecked.bound_eq]
  split
  · rw [show UInt64.toNat 0 = 0 from rfl, Verified.blockCost_eq]; omega
  · rename_i hy0
    have hy0' : y.mag.size ≠ 0 := by
      rw [size_toUInt64_beq_zero (by omega)] at hy0; simpa using hy0
    have h1 := divCost_le x.mag y.mag hx hy
    obtain ⟨s1, s2⟩ := natDivMod_size x.mag y.mag hx hy hy0'
    refine le_trans (Nat.add_le_add_right h1 _) ?_
    split
    · have hq : (intTDivMod x y).1.mag.size ≤ x.mag.size := s1
      have hr : (intTDivMod x y).2.mag.size ≤ y.mag.size := s2
      have h2 := natAdd_bound_le (intTDivMod x y).1.mag #[1] (by omega) (by simp)
      have h3 := natSub_bound_le y.mag (intTDivMod x y).2.mag hy (by omega)
      rw [show UInt64.toNat 0 = 0 from rfl, Verified.blockCost_eq, Verified.growCost_eq]
      have h1s : (#[1] : Array UInt64).size = 1 := rfl
      have h0s : ({ toList := [] } : Array UInt64).size = 0 := rfl
      rw [h1s] at h2
      rw [h0s]
      have : max (intTDivMod x y).1.mag.size 1 ≤ x.mag.size + 1 := by omega
      have : max y.mag.size (intTDivMod x y).2.mag.size = y.mag.size := by omega
      omega
    · omega

/-- A loop that keeps the size of the array in its state. -/
theorem loop_keep_size (n : UInt64) (init : Array UInt64)
    (F : UInt64 → Array UInt64 → Array UInt64) (hF : ∀ i w, (F i w).size = w.size) :
    (LeanExe.loop n init F).size = init.size :=
  loop_induction (P := fun _ (w : Array UInt64) => w.size = init.size) rfl
    (fun k w _ h => by rw [hF, h])

theorem intToText_bound_le (x : BigInt) (hx : Digits x.mag) (hs : x.mag.size < 2 ^ 32) :
    compiled.intToText.bound x ≤ 94 * x.mag.size + 424 := by
  rw [compiled.intToText.bound_eq]
  have hK : (x.mag.size.toUInt64 + x.mag.size.toUInt64 / 14 + 2).toNat =
      x.mag.size + x.mag.size / 14 + 2 := by
    rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_div, toNat_size hs]
    simp only [UInt64.reduceToNat]
    omega
  generalize hKd : x.mag.size.toUInt64 + x.mag.size.toUInt64 / 14 + 2 = K at hK ⊢
  obtain ⟨hcs, -⟩ := chunks_spec x.mag K hx hs
  generalize chunks x.mag K = c at hcs ⊢
  have hsc := (significant_spec c (by omega)).1
  generalize significant c = sc at hsc ⊢
  have hT : (if (sc == 0) = true then (0 : UInt64) else sc - 1).toNat + 1 ≤ K.toNat := by
    by_cases h0 : sc = 0
    · rw [ite_eq_left (by simp [h0])]; simp; omega
    · rw [ite_eq_right (by simpa using h0), UInt64.toNat_sub_of_le _ _ (by
        rw [UInt64.le_iff_toNat_le]
        have : sc.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp (by rw [e]; rfl))
        simp; omega)]
      simp; omega
  generalize (if (sc == 0) = true then (0 : UInt64) else sc - 1) = t at hT ⊢
  have hdc : (Library.Numerics.Decimal.Int64Text.digitCount c[t.toNat]!).toNat ≤ 20 := by
    rw [Library.Numerics.Decimal.Int64Text.digitCount_toNat]
    exact Library.Numerics.Decimal.Int64Text.digitWords_length_le _ (UInt64.toNat_lt _)
  have hS : (if x.neg = true then (1 : UInt64) else 0).toNat ≤ 1 := by split <;> simp
  have hlen : ((if x.neg = true then (1 : UInt64) else 0) +
      Library.Numerics.Decimal.Int64Text.digitCount c[t.toNat]! + 9 * t).toNat ≤
      1 + 20 + 9 * t.toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul]
    simp only [UInt64.reduceToNat]
    have h1 := Nat.mod_le (9 * t.toNat) (2 ^ 64)
    have h2 := Nat.mod_le ((if x.neg = true then (1 : UInt64) else 0).toNat +
      (Library.Numerics.Decimal.Int64Text.digitCount c[t.toNat]!).toNat) (2 ^ 64)
    have h3 := Nat.mod_le (((if x.neg = true then (1 : UInt64) else 0).toNat +
      (Library.Numerics.Decimal.Int64Text.digitCount c[t.toNat]!).toNat) % 2 ^ 64 +
      9 * t.toNat % 2 ^ 64) (2 ^ 64)
    omega
  rw [Verified.blockCost_eq, Verified.blockCost_eq, Verified.blockCost_eq, toNat_size hs, hK]
  omega

theorem natTrim_loop_bound (C : UInt64) (F : UInt64 → Array UInt64 → Array UInt64)
    (hF : ∀ i w, (F i w).size = w.size) (hC : C.toNat < 2 ^ 32) :
    compiled.natTrim.bound (LeanExe.loop C (LeanExe.build C fun _ => (0 : UInt64)) F) ≤
      8 * C.toNat + 56 := by
  have h := natTrim_bound_le (LeanExe.loop C (LeanExe.build C fun _ => (0 : UInt64)) F)
    (by rw [loop_keep_size _ _ _ hF, build_size]; omega)
  rw [loop_keep_size _ _ _ hF, build_size] at h
  exact h

theorem intOfText_bound_le (s : Array UInt64) (hs : s.size < 2 ^ 32) :
    compiled.intOfText.bound s ≤ 2 * s.size + 128 := by
  rw [compiled.intOfText.bound_eq]
  have hn := toNat_size hs
  split
  · rw [show UInt64.toNat 0 = 0 from rfl, Verified.blockCost_eq]; omega
  · rename_i h0
    rw [size_toUInt64_beq_zero (by omega)] at h0
    have h0' : s.size ≠ 0 := by simpa using h0
    generalize hst : (if (s[UInt64.toNat 0]! == 45) = true then (1 : UInt64) else 0) = st
    have hst1 : st.toNat ≤ 1 := by rw [← hst]; split <;> simp
    have hC : ((s.size.toUInt64 - st + 8) / 9).toNat ≤ (s.size + 8) / 9 := by
      rw [UInt64.toNat_div, UInt64.toNat_add]
      simp only [UInt64.reduceToNat]
      have : (s.size.toUInt64 - st).toNat ≤ s.size := by
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hn]; omega), hn]
        omega
      have := Nat.mod_le ((s.size.toUInt64 - st).toNat + 8) (2 ^ 64)
      omega
    generalize (s.size.toUInt64 - st + 8) / 9 = C at hC ⊢
    split
    · rw [show UInt64.toNat 0 = 0 from rfl, Verified.blockCost_eq]; omega
    · split
      · refine le_trans (Nat.add_le_add_left (natTrim_loop_bound C _ (fun i w =>
          loop_keep_size2 _ _ _ (fun _ _ => by simp)) (by omega)) _) ?_
        rw [Verified.blockCost_eq]
        omega
      · rw [show UInt64.toNat 0 = 0 from rfl, Verified.blockCost_eq]; omega

end Library.Numerics.Bignum
