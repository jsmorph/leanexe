import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring

/-! A map on words that distributes over xor is a linear map of 64 bits over GF(2), and these
lemmas represent it by its columns, the images of the powers of 2, as lists of natural numbers.
`applyList c x` is the xor of the columns `c` at the set bits of `x`, and for the columns of such a
map `f` it equals `f x` for every word `x`.  `sq` gives the columns of a map's square, `pows` the
columns of the maps `f^[2^j]`, and `jumpList` the image of a word under `f^[m]` by one product per
set bit of `m`.  The
kernel evaluates these on natural numbers, whose `^^^`, `/`, and `%` it computes on literals, so
that a theorem about `f^[m]` for a large `m` follows from one evaluation. -/

namespace Library.Random.Xorshift

open Function

/-- The xor of the columns `c` at the set bits of `x`, bit 0 first. -/
def applyList : List Nat → Nat → Nat
  | [], _ => 0
  | c :: cs, x => (if x % 2 = 1 then c else 0) ^^^ applyList cs (x / 2)

/-- The columns of `f` at the first `n` powers of 2. -/
def cols (f : Nat → Nat) (n : Nat) : List Nat := (List.range n).map fun i => f (2 ^ i)

theorem cols_succ (f : Nat → Nat) (n : Nat) :
    cols f (n + 1) = f 1 :: cols (fun y => f (2 * y)) n := by
  simp only [cols, List.range_succ_eq_map, List.map_cons, List.map_map, pow_zero]
  congr 1
  apply List.map_congr_left
  intro i _
  simp [Function.comp, pow_succ, Nat.mul_comm]

/-- `f` distributes over xor. -/
def Linear {α : Type} [XorOp α] (f : α → α) : Prop := ∀ a b, f (a ^^^ b) = f a ^^^ f b

theorem Linear.map_zero {f : Nat → Nat} (h : Linear f) : f 0 = 0 := by
  have := h 0 0
  simpa using this

/-- Doubling distributes over xor. -/
theorem two_mul_xor (a b : Nat) : 2 * (a ^^^ b) = 2 * a ^^^ 2 * b := by
  have e : ∀ y : Nat, 2 * y = y <<< 1 := fun y => by rw [Nat.shiftLeft_eq]; omega
  rw [e, e, e, Nat.shiftLeft_xor_distrib]

/-- A number is the xor of its bit 0 and twice its other bits. -/
theorem split_low_bit (x : Nat) : x = x % 2 ^^^ 2 * (x / 2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, show 2 * (x / 2) = x / 2 * 2 ^ 1 by omega, Nat.testBit_mul_two_pow,
    show x % 2 = x % 2 ^ 1 by rfl, Nat.testBit_mod_two_pow]
  cases i with
  | zero => simp
  | succ i => simp [Nat.testBit_div_two]

theorem Linear.double {f : Nat → Nat} (h : Linear f) : Linear fun y => f (2 * y) := fun a b => by
  simp only [two_mul_xor]
  exact h _ _

/-- The columns of a map that distributes over xor give its image of every number below `2^n`. -/
theorem applyList_cols {f : Nat → Nat} (hf : Linear f) :
    ∀ (n x : Nat), x < 2 ^ n → applyList (cols f n) x = f x := by
  intro n
  induction n generalizing f with
  | zero => intro x hx; simp at hx; subst hx; simp [cols, applyList, hf.map_zero]
  | succ n ih =>
    intro x hx
    rw [cols_succ, applyList, ih hf.double (x / 2) (by rw [pow_succ] at hx; omega)]
    conv => rhs; rw [split_low_bit x]
    rw [hf]
    congr 1
    split <;> rename_i h
    · rw [h]
    · rw [show x % 2 = 0 by omega, hf.map_zero]

/-- `f` maps every number to a word. -/
def WordValued (f : Nat → Nat) : Prop := ∀ y, f y < 2 ^ 64

theorem Linear.iterate {α : Type} [XorOp α] {f : α → α} (h : Linear f) : ∀ k, Linear f^[k]
  | 0 => fun _ _ => rfl
  | k + 1 => fun a b => by rw [iterate_succ_apply', iterate_succ_apply', iterate_succ_apply',
      Linear.iterate h k, h]

theorem WordValued.iterate {f : Nat → Nat} (h : WordValued f) (k : Nat) :
    WordValued f^[k + 1] := fun y => by
  rw [iterate_succ_apply']; exact h _

/-- The columns of the square of the linear map with columns `c`. -/
def sq (c : List Nat) : List Nat := c.map (applyList c)

/-- The columns of the square of a map on words. -/
theorem sq_cols {f : Nat → Nat} (hf : Linear f) (hb : WordValued f) :
    sq (cols f 64) = cols (f ∘ f) 64 := by
  simp only [sq, cols, List.map_map]
  apply List.map_congr_left
  intro i _
  exact applyList_cols hf 64 _ (hb _)

/-- The columns `c`, then those of its square, and so on, `k` in all. -/
def pows : Nat → List Nat → List (List Nat)
  | 0, _ => []
  | k + 1, c => c :: pows k (sq c)

/-- The image of `x` under the product of the maps of `ps` at the set bits of `m`. -/
def jumpList : List (List Nat) → Nat → Nat → Nat
  | [], _, x => x
  | p :: ps, m, x => jumpList ps (m / 2) (if m % 2 = 1 then applyList p x else x)

/-- `jumpList` over the tables of `f^[2^j]` and its squares computes `f^[2^j * m]` for `m` below
`2^k`. -/
theorem jumpList_pows {f : Nat → Nat} (hf : Linear f) (hb : WordValued f) :
    ∀ (k j m x : Nat), m < 2 ^ k → x < 2 ^ 64 →
      jumpList (pows k (cols f^[2 ^ j] 64)) m x = f^[2 ^ j * m] x := by
  intro k
  induction k with
  | zero => intro j m x hm _; simp at hm; subst hm; rfl
  | succ k ih =>
    intro j m x hm hx
    have hb' : WordValued f^[2 ^ j] := by
      obtain ⟨t, ht⟩ : ∃ t, 2 ^ j = t + 1 :=
        ⟨2 ^ j - 1, by have := Nat.one_le_two_pow (n := j); omega⟩
      rw [ht]; exact hb.iterate t
    have hsq : sq (cols f^[2 ^ j] 64) = cols f^[2 ^ (j + 1)] 64 := by
      rw [sq_cols (hf.iterate _) hb', ← iterate_add, pow_succ, Nat.mul_two]
    rw [pows, jumpList, hsq, ih (j + 1) (m / 2) _ (by rw [pow_succ] at hm; omega) (by
      split
      · rw [applyList_cols (hf.iterate _) 64 x hx]; exact hb' x
      · exact hx)]
    split <;> rename_i h
    · rw [applyList_cols (hf.iterate _) 64 x hx, ← iterate_add_apply]
      congr 1
      rw [pow_succ]
      have := Nat.div_add_mod m 2
      rw [h] at this
      calc 2 ^ j * 2 * (m / 2) + 2 ^ j = 2 ^ j * (2 * (m / 2) + 1) := by ring
        _ = 2 ^ j * m := by rw [this]
    · congr 1
      rw [pow_succ]
      have := Nat.div_add_mod m 2
      rw [show m % 2 = 0 by omega] at this
      calc 2 ^ j * 2 * (m / 2) = 2 ^ j * (2 * (m / 2)) := by ring
        _ = 2 ^ j * m := by rw [← this]; simp

end Library.Random.Xorshift
