import Project.ProofKit.F64OrderComplete
import Project.ProofKit.F64Absolute

namespace Project.ProofKit.F64Adjacent
open CodeLib.IEEE64
open Project.ProofKit.F64Order
set_option exponentiation.threshold 4096

def nextUp (bits : UInt64) : UInt64 :=
  if bits = 0x8000000000000000 then 1
  else if bits < 0x8000000000000000 then bits+1 else bits-1

def nextDown (bits : UInt64) : UInt64 :=
  if bits = 0 then 0x8000000000000001
  else if bits < 0x8000000000000000 then bits-1 else bits+1

theorem unsignedScaled_succ (n : Nat) :
    unsignedScaled (n+1) = unsignedScaled n+2^(n/2^52-1) := by
  let e := n/2^52
  let f := n%2^52
  have hf : f < 2^52 := Nat.mod_lt _ (by positivity)
  have hn : n = e*2^52+f := (Nat.div_add_mod' n (2^52)).symm
  by_cases hc : f+1 < 2^52
  · have he : (n+1)/2^52 = e := by omega
    have hr : (n+1)%2^52 = f+1 := by omega
    change (if (n+1)/2^52 = 0 then (n+1)%2^52
      else (2^52+(n+1)%2^52)*2^((n+1)/2^52-1)) =
      (if e = 0 then f else (2^52+f)*2^(e-1))+2^(e-1)
    rw [he, hr]
    split <;> simp_all <;> ring
  · have hlast : f+1 = 2^52 := by omega
    have he : (n+1)/2^52 = e+1 := by omega
    have hr : (n+1)%2^52 = 0 := by omega
    change (if (n+1)/2^52 = 0 then (n+1)%2^52
      else (2^52+(n+1)%2^52)*2^((n+1)/2^52-1)) =
      (if e = 0 then f else (2^52+f)*2^(e-1))+2^(e-1)
    rw [he, hr]
    simp only [Nat.succ_ne_zero, ↓reduceIte,
      Nat.add_zero, Nat.add_sub_cancel]
    by_cases hz : e = 0
    · simp [hz]
      omega
    · have hp : 2^e = 2*2^(e-1) := by
        conv_lhs => rw [show e = (e-1)+1 by omega, pow_succ]
        ring
      rw [ite_eq_right hz, hp]
      calc
        2^52*(2*2^(e-1)) = (2^52+(f+1))*2^(e-1) := by rw [hlast]; ring
        _ = (2^52+f)*2^(e-1)+2^(e-1) := by ring

theorem unsigned_word_value (bits : UInt64) (h : bits.toNat < 2^63) :
    value bits = (unsignedScaled bits.toNat : ℝ)/(2:ℝ)^1074 := by
  have hs : Wasm.IEEE64.sign bits = false := by
    simpa only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] using h
  have hm : Wasm.IEEE64.scaledMagnitude bits = unsignedScaled bits.toNat := by
    rw [scaledMagnitude_abs, absBits_toNat, Nat.mod_eq_of_lt h]
  simp only [value, Wasm.IEEE64.scaledValue, hs, Bool.false_eq_true, ite_false,
    Int.cast_natCast, hm]

theorem positive_successor_gap (bits : UInt64)
    (h : bits.toNat+1 < 2^63) :
    value (bits+1)-value bits = (2:ℝ)^(bits.toNat/2^52-1)/(2:ℝ)^1074 := by
  have hs : (bits+1).toNat = bits.toNat+1 := by
    rw [UInt64.toNat_add]
    change (bits.toNat+1)%2^64 = bits.toNat+1
    exact Nat.mod_eq_of_lt (by omega)
  rw [unsigned_word_value (bits+1) (by omega), unsigned_word_value bits (by omega),
    hs, unsignedScaled_succ]
  push_cast
  ring

theorem nextUp_nonnegative_eq (bits : UInt64) (h : bits.toNat < 2^63) :
    nextUp bits = bits+1 := by
  have hs : bits < 0x8000000000000000 := UInt64.lt_iff_toNat_lt.mpr h
  have hz : bits ≠ 0x8000000000000000 := by
    intro he
    rw [he] at hs
    exact (by decide : ¬((0x8000000000000000 : UInt64) < 0x8000000000000000)) hs
  simp [nextUp, hz, hs]

theorem nextUp_nonnegative_gap (bits : UInt64) (h : bits.toNat+1 < 2^63) :
    value (nextUp bits)-value bits =
      (2:ℝ)^(bits.toNat/2^52-1)/(2:ℝ)^1074 := by
  rw [nextUp_nonnegative_eq bits (by omega)]
  exact positive_successor_gap bits h

theorem nextUp_nonnegative_lt (bits : UInt64) (h : bits.toNat+1 < 2^63) :
    value bits < value (nextUp bits) := by
  have hg := nextUp_nonnegative_gap bits h
  have hp : (0:ℝ) < (2:ℝ)^(bits.toNat/2^52-1)/(2:ℝ)^1074 := by positivity
  linarith

theorem zero_endpoints :
    nextUp 0 = 1 ∧ nextUp 0x8000000000000000 = 1 ∧
    nextDown 0 = 0x8000000000000001 ∧
    nextDown 0x8000000000000000 = 0x8000000000000001 := by decide +kernel

theorem transition_endpoints :
    nextUp 0x000FFFFFFFFFFFFF = 0x0010000000000000 ∧
    nextDown 0x0010000000000000 = 0x000FFFFFFFFFFFFF ∧
    nextUp 0x7FEFFFFFFFFFFFFF = 0x7FF0000000000000 ∧
    nextDown 0xFFEFFFFFFFFFFFFF = 0xFFF0000000000000 := by decide +kernel

#print axioms unsignedScaled_succ
#print axioms positive_successor_gap
#print axioms nextUp_nonnegative_lt
#print axioms zero_endpoints
#print axioms transition_endpoints
end Project.ProofKit.F64Adjacent
