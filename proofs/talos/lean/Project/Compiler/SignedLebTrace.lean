import Project.Artifact.Binary.Proof.Leb
import Mathlib.Tactic

namespace Project.Compiler.SignedLeb

def payload (n : Int) : Nat := (n % 128).toNat

theorem payload_bound (n : Int) : payload n < 128 := by
  unfold payload
  omega

theorem payload_value (n : Int) : (payload n : Int) = n % 128 := by
  unfold payload
  omega

def bytes : Nat → Int → List UInt8
  | 0, _ => []
  | fuel + 1, n =>
      if -64 ≤ n ∧ n < 64 then [UInt8.ofNat (payload n)]
      else UInt8.ofNat (payload n + 128) :: bytes fuel (n / 128)

open Wasm.Binary.Leb Wasm.Binary.Leb.Proof

theorem terminal_value (shift acc : Nat) (n : Int) (small : -64 ≤ n ∧ n < 64) :
    Internal.signedValue shift (payload n) acc = (acc : Int) + n * (2 ^ shift : Nat) := by
  have hp := payload_value n
  unfold Internal.signedValue
  split
  · rename_i low
    have hp' : (payload n : Int) = n := by omega
    simp only [Int.ofNat_eq_natCast]
    push_cast
    rw [hp']
  · rename_i high
    have hp' : (payload n : Int) = n + 128 := by omega
    rw [Nat.pow_add]
    simp only [Int.ofNat_eq_natCast]
    push_cast
    rw [hp']
    ring

theorem terminal_fits (width shift : Nat) (n : Int)
    (shiftFits : shift < width) (small : -64 ≤ n ∧ n < 64)
    (lower : -(2 ^ (width - shift - 1) : Int) ≤ n)
    (upper : n < (2 ^ (width - shift - 1) : Int)) :
    Internal.signedTerminalFits width shift (payload n) = true := by
  have hp := payload_value n
  unfold Internal.signedTerminalFits
  split
  · rfl
  · rename_i short
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    have power : 2 ^ (width - shift - 1) ≤ (64 : Nat) := by
      have h : width - shift - 1 ≤ 6 := by omega
      exact Nat.pow_le_pow_right (by decide) h
    have powerInt : ((2 ^ (width - shift - 1) : Nat) : Int) =
        (2 ^ (width - shift - 1) : Int) := by simp
    by_cases hn : 0 ≤ n
    · left
      have hp' : (payload n : Int) = n := by omega
      omega
    · right
      have hp' : (payload n : Int) = n + 128 := by omega
      omega

theorem trace (fuel width shift acc : Nat) (n : Int)
    (shiftFits : shift < width) (room : width ≤ shift + 7 * fuel)
    (lower : -(2 ^ (width - shift - 1) : Int) ≤ n)
    (upper : n < (2 ^ (width - shift - 1) : Int)) :
    SignedTrace width shift fuel acc (bytes fuel n)
      ((acc : Int) + n * (2 ^ shift : Nat)) := by
  induction fuel generalizing shift acc n with
  | zero => omega
  | succ fuel ih =>
    rw [bytes]
    by_cases small : -64 ≤ n ∧ n < 64
    · rw [if_pos small, ← terminal_value shift acc n small]
      have nb : (UInt8.ofNat (payload n)).toNat = payload n := by
        simp
        have := payload_bound n
        omega
      simpa only [nb, Nat.mod_eq_of_lt (payload_bound n)] using
        (SignedTrace.terminal (width := width) (shift := shift) (value := acc)
          fuel (UInt8.ofNat (payload n)) (by rw [nb]; exact payload_bound n)
          shiftFits (by simpa only [nb, Nat.mod_eq_of_lt (payload_bound n)] using
            terminal_fits width shift n shiftFits small lower upper))
    · rw [if_neg small]
      have shiftNext : shift + 7 < width := by
        by_contra h
        have powBound : (2 ^ (width - shift - 1) : Int) ≤ 64 := by
          have power : 2 ^ (width - shift - 1) ≤ (64 : Nat) :=
            Nat.pow_le_pow_right (by decide) (by omega : width - shift - 1 ≤ 6)
          exact_mod_cast power
        omega
      have fuelPositive : 0 < fuel := by omega
      have power : (2 ^ (width - shift - 1) : Int) =
          128 * 2 ^ (width - (shift + 7) - 1) := by
        have diff : width - shift - 1 = 7 + (width - (shift + 7) - 1) := by omega
        rw [diff, pow_add]
        norm_num
      have lower' : -(2 ^ (width - (shift + 7) - 1) : Int) ≤ n / 128 := by
        rw [power] at lower
        omega
      have upper' : n / 128 < (2 ^ (width - (shift + 7) - 1) : Int) := by
        rw [power] at upper
        omega
      have nb : (UInt8.ofNat (payload n + 128)).toNat = payload n + 128 := by
        simp
        have := payload_bound n
        omega
      have tail := ih (shift + 7) (acc + payload n * 2 ^ shift) (n / 128)
        shiftNext (by omega) lower' upper'
      have valueEq : ((acc + payload n * 2 ^ shift : Nat) : Int) +
          n / 128 * (2 ^ (shift + 7) : Nat) = (acc : Int) + n * (2 ^ shift : Nat) := by
        rw [Nat.pow_add]
        push_cast
        rw [payload_value]
        calc
          _ = (acc : Int) + (n % 128 + 128 * (n / 128)) * 2 ^ shift := by ring
          _ = _ := by rw [show n % 128 + 128 * (n / 128) = n by omega]
      rw [valueEq] at tail
      apply SignedTrace.next fuel (UInt8.ofNat (payload n + 128)) _ _
        (by rw [nb]; omega) fuelPositive
      simpa only [nb, Nat.add_mod, Nat.mod_self, Nat.add_zero,
        Nat.mod_eq_of_lt (payload_bound n)] using tail

end Project.Compiler.SignedLeb
