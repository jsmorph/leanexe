import LeanExe.Examples.BeckExact.Integer
import Mathlib.Tactic

namespace Project.Beck.LimbArithmetic

open LeanExe.Examples.BeckExact

def Valid (digit : UInt64) : Prop := digit.toNat < 4294967296

theorem add_bound (a b carry : UInt64) (ha : Valid a) (hb : Valid b)
    (hc : carry.toNat ≤ 1) : a.toNat + b.toNat + carry.toNat < 2 ^ 64 := by
  dsimp [Valid] at *
  omega

theorem add_exact (a b carry : UInt64) (ha : Valid a) (hb : Valid b)
    (hc : carry.toNat ≤ 1) : (a + b + carry).toNat = a.toNat + b.toNat + carry.toNat := by
  have bound := add_bound a b carry ha hb hc
  have ab : a.toNat + b.toNat < 2 ^ 64 := by omega
  rw [UInt64.toNat_add, UInt64.toNat_add]
  rw [Nat.mod_eq_of_lt ab]
  exact Nat.mod_eq_of_lt bound

theorem add_carry (a b carry : UInt64) (ha : Valid a) (hb : Valid b)
    (hc : carry.toNat ≤ 1) :
    Valid ((a + b + carry) % Digits.radix) ∧
      ((a + b + carry) / Digits.radix).toNat ≤ 1 ∧
      ((a + b + carry) % Digits.radix).toNat +
        4294967296 * ((a + b + carry) / Digits.radix).toNat = a.toNat + b.toNat + carry.toNat := by
  rw [Valid, UInt64.toNat_mod, UInt64.toNat_div, add_exact a b carry ha hb hc]
  change (a.toNat + b.toNat + carry.toNat) % 4294967296 < 4294967296 ∧
    (a.toNat + b.toNat + carry.toNat) / 4294967296 ≤ 1 ∧
    (a.toNat + b.toNat + carry.toNat) % 4294967296 +
      4294967296 * ((a.toNat + b.toNat + carry.toNat) / 4294967296) = _
  refine ⟨Nat.mod_lt _ (by decide), ?_, Nat.mod_add_div _ _⟩
  dsimp [Valid] at *
  omega

theorem mul_add_bound (a b prior carry : UInt64)
    (ha : Valid a) (hb : Valid b) (hp : Valid prior) (hc : Valid carry) :
    a.toNat * b.toNat + prior.toNat + carry.toNat < 2 ^ 64 := by
  have aBound : a.toNat ≤ 4294967295 := by dsimp [Valid] at ha; omega
  have bBound : b.toNat ≤ 4294967295 := by dsimp [Valid] at hb; omega
  have product := Nat.mul_le_mul aBound bBound
  dsimp [Valid] at hp hc
  norm_num at product ⊢
  omega

theorem mul_add_exact (a b prior carry : UInt64)
    (ha : Valid a) (hb : Valid b) (hp : Valid prior) (hc : Valid carry) :
    (a * b + prior + carry).toNat = a.toNat * b.toNat + prior.toNat + carry.toNat := by
  have bound := mul_add_bound a b prior carry ha hb hp hc
  have ab : a.toNat * b.toNat < 2 ^ 64 := by omega
  have abp : a.toNat * b.toNat + prior.toNat < 2 ^ 64 := by omega
  rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul]
  rw [Nat.mod_eq_of_lt ab, Nat.mod_eq_of_lt abp]
  exact Nat.mod_eq_of_lt bound

theorem mul_carry (a b prior carry : UInt64)
    (ha : Valid a) (hb : Valid b) (hp : Valid prior) (hc : Valid carry) :
    Valid ((a * b + prior + carry) % Digits.radix) ∧
      Valid ((a * b + prior + carry) / Digits.radix) ∧
      ((a * b + prior + carry) % Digits.radix).toNat +
        4294967296 * ((a * b + prior + carry) / Digits.radix).toNat =
          a.toNat * b.toNat + prior.toNat + carry.toNat := by
  have bound := mul_add_bound a b prior carry ha hb hp hc
  rw [Valid, Valid, UInt64.toNat_mod, UInt64.toNat_div, mul_add_exact a b prior carry ha hb hp hc]
  change (a.toNat * b.toNat + prior.toNat + carry.toNat) % 4294967296 < 4294967296 ∧
    (a.toNat * b.toNat + prior.toNat + carry.toNat) / 4294967296 < 4294967296 ∧
    (a.toNat * b.toNat + prior.toNat + carry.toNat) % 4294967296 +
      4294967296 * ((a.toNat * b.toNat + prior.toNat + carry.toNat) / 4294967296) = _
  refine ⟨Nat.mod_lt _ (by decide), ?_, Nat.mod_add_div _ _⟩
  omega

#print axioms add_carry
#print axioms mul_carry

end Project.Beck.LimbArithmetic
