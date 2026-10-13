import Verified.Examples.Uscale
import Mathlib.Tactic

/-!
The value of an array of limbs as a natural number and the facts that the proofs of `Uscale`'s
routines share.  `val a` reads the limbs least significant first in base `2 ^ 32`, and `Limbs a`
states that every element is below `2 ^ 32`.  For such an array, the element at position `i`,
read as the routines read it with `a[i]!` and 0 past the end, is the base-`2 ^ 32` digit `i` of
`val a` (`getElem!_digit`), so each routine's invariant is a statement about `val a % 2 ^ (32 k)`,
the value of the first `k` limbs.  `loop_inv` is the induction principle of `LeanExe.loop`.
`mulSmall_spec` proves that `mulSmall a m c` has the value `val a · m + c`.
-/

namespace Verified.Examples.UscaleTheorem
open Uscale

/-- The value of a list of limbs, least significant first. -/
def valL : List UInt64 → ℕ
  | [] => 0
  | x :: xs => x.toNat + 2 ^ 32 * valL xs

/-- The value of an array of limbs. -/
def val (a : Array UInt64) : ℕ := valL a.toList

/-- Every element of `a` is a limb below `2 ^ 32`. -/
def Limbs (a : Array UInt64) : Prop := ∀ x ∈ a.toList, x.toNat < 2 ^ 32

/-! ### Loops -/

/-- The induction principle of `LeanExe.loop`. -/
theorem loop_inv {α : Type} (n : UInt64) (init : α) (f : UInt64 → α → α) (P : ℕ → α → Prop)
    (h0 : P 0 init) (hs : ∀ k s, k < n.toNat → P k s → P (k + 1) (f (UInt64.ofNat k) s)) :
    P n.toNat (LeanExe.loop n init f) := by
  unfold LeanExe.loop
  have key : ∀ k, k ≤ n.toNat →
      P k (Nat.fold k (fun i _ s => f (UInt64.ofNat i) s) init) := by
    intro k hk
    induction k with
    | zero => simpa using h0
    | succ k ih =>
      simp only [Nat.fold_succ]
      exact hs k _ (by omega) (ih (by omega))
  exact key n.toNat le_rfl

theorem ofNat_toNat (k : ℕ) (hk : k < 2 ^ 64) : (UInt64.ofNat k).toNat = k :=
  UInt64.toNat_ofNat_of_lt' hk

theorem size_toUInt64 (a : Array UInt64) (h : a.size < 2 ^ 64) : a.size.toUInt64.toNat = a.size := by
  simp [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' h]

/-! ### Values -/

theorem valL_lt (l : List UInt64) (h : ∀ x ∈ l, x.toNat < 2 ^ 32) : valL l < 2 ^ (32 * l.length) := by
  induction l with
  | nil => simp [valL]
  | cons x xs ih =>
    have hx := h x (by simp)
    have := ih (fun y hy => h y (by simp [hy]))
    simp only [valL, List.length_cons]
    rw [show 32 * (xs.length + 1) = 32 + 32 * xs.length by ring, pow_add]
    nlinarith

theorem val_lt (a : Array UInt64) (h : Limbs a) : val a < 2 ^ (32 * a.size) := by
  have := valL_lt a.toList h
  simpa [val] using this

theorem valL_append (l l' : List UInt64) :
    valL (l ++ l') = valL l + 2 ^ (32 * l.length) * valL l' := by
  induction l with
  | nil => simp [valL]
  | cons x xs ih =>
    simp only [List.cons_append, valL, ih, List.length_cons]
    rw [show 32 * (xs.length + 1) = 32 + 32 * xs.length by ring, pow_add]
    ring

theorem val_push (a : Array UInt64) (x : UInt64) :
    val (a.push x) = val a + 2 ^ (32 * a.size) * x.toNat := by
  simp [val, Array.toList_push, valL_append, valL]

theorem limbs_push (a : Array UInt64) (x : UInt64) (ha : Limbs a) (hx : x.toNat < 2 ^ 32) :
    Limbs (a.push x) := by
  intro y hy
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hy
  rcases hy with hy | hy
  · exact ha y hy
  · rw [hy]; exact hx

theorem val_empty : val (LeanExe.build 0 fun _ => (0 : UInt64)) = 0 := by
  simp [val, LeanExe.build, valL]

theorem size_empty : (LeanExe.build 0 fun _ => (0 : UInt64)).size = 0 := by
  simp [LeanExe.build]

theorem limbs_empty : Limbs (LeanExe.build 0 fun _ => (0 : UInt64)) := by
  intro x hx; simp [LeanExe.build] at hx

/-! ### Digits -/

theorem listDigit (l : List UInt64) (h : ∀ x ∈ l, x.toNat < 2 ^ 32) (i : ℕ) :
    (l[i]?.getD 0).toNat = valL l / 2 ^ (32 * i) % 2 ^ 32 := by
  induction l generalizing i with
  | nil => simp [valL]
  | cons x xs ih =>
    have hx := h x (by simp)
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.getD_some, valL, Nat.mul_zero, pow_zero,
        Nat.div_one]
      omega
    | succ i =>
      simp only [List.getElem?_cons_succ]
      rw [ih (fun y hy => h y (by simp [hy])) i]
      simp only [valL]
      rw [show 32 * (i + 1) = 32 + 32 * i by ring, pow_add, ← Nat.div_div_eq_div_mul]
      congr 2
      omega

/-- The element `i` of a limb array, 0 past the end, is digit `i` of its value. -/
theorem getElem!_digit (a : Array UInt64) (h : Limbs a) (i : ℕ) :
    (a[i]!).toNat = val a / 2 ^ (32 * i) % 2 ^ 32 := by
  have e : a[i]! = (a.toList[i]?).getD 0 := by
    rw [getElem!_def]
    rw [show a[i]? = a.toList[i]? from (Array.getElem?_toList).symm]
    cases a.toList[i]? <;> rfl
  rw [e]
  exact listDigit a.toList h i

theorem getElem!_lt (a : Array UInt64) (h : Limbs a) (i : ℕ) : (a[i]!).toNat < 2 ^ 32 := by
  rw [getElem!_digit a h]; exact Nat.mod_lt _ (by positivity)

/-- The value of the first `k + 1` limbs. -/
theorem mod_succ (v k : ℕ) :
    v % 2 ^ (32 * (k + 1)) = v % 2 ^ (32 * k) + 2 ^ (32 * k) * (v / 2 ^ (32 * k) % 2 ^ 32) := by
  rw [show 32 * (k + 1) = 32 * k + 32 by ring, pow_add, Nat.mod_mul]

theorem limb_eq (a : Array UInt64) (j : UInt64) (hs : a.size < 2 ^ 64) :
    limb a j = a[j.toNat]! := by
  unfold limb
  by_cases h : j < a.size.toUInt64
  · rw [if_pos h]
  · rw [if_neg h]
    have : a.size ≤ j.toNat := by
      rw [UInt64.lt_iff_toNat_lt, size_toUInt64 a hs] at h; omega
    rw [getElem!_neg a _ (by omega)]
    rfl

/-! ### Word arithmetic -/

theorem and_mask (t : UInt64) : (t &&& 0xFFFFFFFF).toNat = t.toNat % 2 ^ 32 := by
  rw [UInt64.toNat_and]
  rw [show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem shr32 (t : UInt64) : (t >>> 32).toNat = t.toNat / 2 ^ 32 := by
  rw [UInt64.toNat_shiftRight]
  rw [show (32 : UInt64).toNat % 64 = 32 from rfl, Nat.shiftRight_eq_div_pow]

theorem mul_add_toNat (x m c : UInt64) (hx : x.toNat < 2 ^ 32) (hm : m.toNat < 2 ^ 32)
    (hc : c.toNat < 2 ^ 32) : (x * m + c).toNat = x.toNat * m.toNat + c.toNat := by
  have h1 : x.toNat * m.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  rw [UInt64.toNat_add, UInt64.toNat_mul, Nat.mod_eq_of_lt (a := x.toNat * m.toNat) (by omega)]
  exact Nat.mod_eq_of_lt (by omega)

/-! ### `mulSmall` -/

theorem mulSmall_spec (a : Array UInt64) (m c : UInt64) (ha : Limbs a) (hs : a.size < 2 ^ 64)
    (hm : m.toNat < 2 ^ 32) (hc : c.toNat < 2 ^ 32) :
    Limbs (mulSmall a m c) ∧ val (mulSmall a m c) = val a * m.toNat + c.toNat ∧
      (mulSmall a m c).size = a.size + 1 := by
  unfold mulSmall
  have hloop := loop_inv a.size.toUInt64 (LeanExe.build 0 fun _ => (0 : UInt64), c)
    (fun i (s : Array UInt64 × UInt64) =>
      ((s.1.push ((a[i.toNat]! * m + s.2) &&& 0xFFFFFFFF)), (a[i.toNat]! * m + s.2) >>> 32))
    (fun k s => s.1.size = k ∧ Limbs s.1 ∧ s.2.toNat < 2 ^ 32 ∧
      val s.1 + 2 ^ (32 * k) * s.2.toNat = val a % 2 ^ (32 * k) * m.toNat + c.toNat)
    ⟨size_empty, limbs_empty, hc, by simp [val_empty, Nat.mod_one]⟩
    (by
      intro k s hk ⟨h1, h2, h3, h4⟩
      rw [size_toUInt64 a hs] at hk
      rw [ofNat_toNat k (by omega)]
      have hx := getElem!_lt a ha k
      have ht := mul_add_toNat (a[k]!) m s.2 hx hm h3
      have hxm : a[k]!.toNat * m.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      refine ⟨by simp [h1], limbs_push _ _ h2 (by rw [and_mask]; exact Nat.mod_lt _ (by norm_num)),
        by rw [shr32, ht]; exact (Nat.div_lt_iff_lt_mul (by norm_num)).mpr (by omega), ?_⟩
      rw [val_push, and_mask, shr32, ht, h1, mod_succ, ← getElem!_digit a ha k]
      rw [show 32 * (k + 1) = 32 * k + 32 by ring, pow_add]
      have hd := Nat.div_add_mod (a[k]!.toNat * m.toNat + s.2.toNat) (2 ^ 32)
      calc val s.1 + 2 ^ (32 * k) * ((a[k]!.toNat * m.toNat + s.2.toNat) % 2 ^ 32) +
            2 ^ (32 * k) * 2 ^ 32 * ((a[k]!.toNat * m.toNat + s.2.toNat) / 2 ^ 32)
          = val s.1 + 2 ^ (32 * k) * (2 ^ 32 * ((a[k]!.toNat * m.toNat + s.2.toNat) / 2 ^ 32) +
            (a[k]!.toNat * m.toNat + s.2.toNat) % 2 ^ 32) := by ring
        _ = val s.1 + 2 ^ (32 * k) * (a[k]!.toNat * m.toNat + s.2.toNat) := by rw [hd]
        _ = (val s.1 + 2 ^ (32 * k) * s.2.toNat) + 2 ^ (32 * k) * a[k]!.toNat * m.toNat := by ring
        _ = _ := by rw [h4]; ring)
  rw [size_toUInt64 a hs] at hloop
  obtain ⟨h1, h2, h3, h4⟩ := hloop
  generalize LeanExe.loop _ _ _ = s at h1 h2 h3 h4 ⊢
  refine ⟨limbs_push _ _ h2 h3, ?_, by simp [h1]⟩
  rw [val_push, h1, Nat.mod_eq_of_lt (val_lt a ha)] at *
  linarith

#print axioms loop_inv
#print axioms getElem!_digit
#print axioms mulSmall_spec

end Verified.Examples.UscaleTheorem
