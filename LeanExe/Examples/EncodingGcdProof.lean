import LeanExe.Examples.EncodingGcd
import Init.Internal.Order.While

namespace LeanExe.Examples.EncodingGcd

private def loop (x y : UInt64) : MProd UInt64 UInt64 :=
  Lean.Loop.forIn (m := Id) Lean.Loop.mk (MProd.mk x y) fun _ p =>
    if p.2 != 0 then
      pure (.yield (MProd.mk p.2 (p.1 % p.2)))
    else
      pure (.done p)

private theorem loop_eq (x y : UInt64) :
    loop x y = if y != 0 then loop y (x % y) else MProd.mk x y := by
  unfold loop
  rw [Lean.Loop.forIn_eq_of_monadTail]
  by_cases h : y = 0 <;> simp [h] <;> rfl

private theorem loop_correct (x y : UInt64) :
    (loop x y).1 = UInt64.ofNat (Nat.gcd x.toNat y.toNat) := by
  suffices h : ∀ n, ∀ (x y : UInt64), y.toNat = n →
      (loop x y).1 = UInt64.ofNat (Nat.gcd x.toNat y.toNat) from h y.toNat x y rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro x y hy
    rw [loop_eq]
    by_cases hz : y = 0
    · simp [hz, Nat.gcd_zero_right]
    · simp [hz]
      have hypos : 0 < y.toNat := Nat.pos_of_ne_zero (by
        intro hzero
        exact hz (UInt64.toNat_inj.mp (by simpa using hzero)))
      have hlt : (x % y).toNat < n := by
        rw [UInt64.toNat_mod, hy]
        exact Nat.mod_lt _ (by simpa [hy] using hypos)
      rw [ih _ hlt y (x % y) rfl]
      rw [UInt64.toNat_mod]
      congr 1
      calc
        Nat.gcd y.toNat (x.toNat % y.toNat) = Nat.gcd (x.toNat % y.toNat) y.toNat := Nat.gcd_comm _ _
        _ = Nat.gcd y.toNat x.toNat := (Nat.gcd_rec _ _).symm
        _ = Nat.gcd x.toNat y.toNat := Nat.gcd_comm _ _

theorem gcd_correct (a b : UInt64) :
    gcd a b = UInt64.ofNat (Nat.gcd a.toNat b.toNat) := by
  change (loop a b).1 = _
  exact loop_correct a b

theorem gcd_symmetric (a b : UInt64) : gcd a b = gcd b a := by
  rw [gcd_correct, gcd_correct, Nat.gcd_comm]

theorem gcd_zero_right (a : UInt64) : gcd a 0 = a := by
  simp [gcd_correct]

end LeanExe.Examples.EncodingGcd
