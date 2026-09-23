import LeanExe.Signed32
import Interpreter.Wasm.IEEE32
import Mathlib.Tactic

namespace Project.ProofKit.QuantizedInt32
open LeanExe.Signed32

theorem decode_toInt (value : UInt32) :
    decode value = (Int32.ofUInt32 value).toInt := by
  simp only [decode, Int32.toInt, Int32.toBitVec, BitVec.toInt_eq_toNat_cond]
  change (if value.toNat < 2 ^ 31 then (value.toNat : Int) else value.toNat - 2 ^ 32) =
    if 2 * value.toNat < 2 ^ 32 then (value.toNat : Int) else value.toNat - 2 ^ 32
  split_ifs <;> omega

theorem decode_talos (value : UInt32) : decode value = Wasm.IEEE32.signedI32Value value := by
  simp only [decode, Wasm.IEEE32.signedI32Value, Wasm.IEEE32.sign, decide_eq_true_eq]
  split_ifs <;> omega

theorem extend8_toNat (value : UInt32) :
    (extend8Bits value).toNat =
      if value.toNat % 256 < 128 then value.toNat % 256
      else 4294967040 + value.toNat % 256 := by
  have mask : (value &&& 255).toNat = value.toNat % 256 := by
    rw [UInt32.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod value.toNat 8
  have hm : value.toNat % 256 < 2 ^ 8 := Nat.mod_lt _ (by decide)
  by_cases h : value.toNat % 256 < 128
  · have hh : value &&& 255 < 128 := by
      simpa [UInt32.lt_iff_toNat_lt, mask] using h
    simp only [extend8Bits, hh, h, ↓reduceIte, mask]
  · have hh : ¬value &&& 255 < 128 := by
      simpa [UInt32.lt_iff_toNat_lt, mask] using h
    simp only [extend8Bits, hh, h, ↓reduceIte, UInt32.toNat_or, mask]
    rw [Nat.or_comm]
    exact (Nat.two_pow_add_eq_or_of_lt hm 16777215).symm

theorem decode_extend8 (value : UInt8) :
    decode (extend8Bits value.toUInt32) =
      if value.toNat < 128 then (value.toNat : Int) else value.toNat - 256 := by
  unfold decode
  rw [extend8_toNat]
  have hv := value.toNat_lt
  simp only [UInt8.toNat_toUInt32, Nat.mod_eq_of_lt hv]
  split_ifs <;> (try simp only [Nat.cast_add, Nat.cast_ofNat]) <;> omega

theorem byte_range (value : UInt8) (reserved : value ≠ 128) :
    |decode (extend8Bits value.toUInt32)| ≤ 127 := by
  rw [decode_extend8, abs_le]
  have hv := value.toNat_lt
  have hn : value.toNat ≠ 128 := by
    intro h
    apply reserved
    exact UInt8.toNat.inj h
  split_ifs <;> omega

theorem add_exact (left right : UInt32)
    (lower : -(2 ^ 31) ≤ decode left + decode right)
    (upper : decode left + decode right < 2 ^ 31) :
    decode (left + right) = decode left + decode right := by
  simp only [decode_toInt] at *
  change ((Int32.ofUInt32 left) + (Int32.ofUInt32 right)).toInt = _
  rw [Int32.toInt_add]
  exact Int.bmod_eq_of_le lower upper

theorem mul_exact (left right : UInt32)
    (lower : -(2 ^ 31) ≤ decode left * decode right)
    (upper : decode left * decode right < 2 ^ 31) :
    decode (left * right) = decode left * decode right := by
  simp only [decode_toInt] at *
  change ((Int32.ofUInt32 left) * (Int32.ofUInt32 right)).toInt = _
  rw [Int32.toInt_mul]
  exact Int.bmod_eq_of_le lower upper

def sumPrefix (x w : Nat → Int) (length : Nat) : Int :=
  ∑ i ∈ Finset.range length, x i * w i

theorem prefix_bound (x w : Nat → Int) (length : Nat)
    (hx : ∀ i < length, |x i| ≤ 127) (hw : ∀ i < length, |w i| ≤ 127) :
    |sumPrefix x w length| ≤ (length : Int) * 16129 := by
  unfold sumPrefix
  calc
    |∑ i ∈ Finset.range length, x i * w i| ≤
        ∑ i ∈ Finset.range length, |x i * w i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range length, (16129 : Int) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      have hxi := hx i (Finset.mem_range.mp hi)
      have hwi := hw i (Finset.mem_range.mp hi)
      nlinarith [abs_nonneg (x i), abs_nonneg (w i)]
    _ = (length : Int) * 16129 := by simp

theorem prefix_representable (x w : Nat → Int) (length : Nat) (hl : length ≤ 3072)
    (hx : ∀ i < length, |x i| ≤ 127) (hw : ∀ i < length, |w i| ≤ 127) :
    -(2 ^ 31) ≤ sumPrefix x w length ∧ sumPrefix x w length < 2 ^ 31 := by
  have h := prefix_bound x w length hx hw
  rw [abs_le] at h
  omega

def wordPrefix (x w : Nat → UInt32) (length : Nat) : UInt32 :=
  (List.range length).foldl (fun accumulator i => accumulator + x i * w i) 0

theorem wordPrefix_exact (x w : Nat → UInt32) (length : Nat) (hl : length ≤ 3072)
    (hx : ∀ i < length, |decode (x i)| ≤ 127)
    (hw : ∀ i < length, |decode (w i)| ≤ 127) :
    decode (wordPrefix x w length) = sumPrefix (decode ∘ x) (decode ∘ w) length := by
  induction length with
  | zero => simp [wordPrefix, sumPrefix, decode]
  | succ length ih =>
    have previous := ih (by omega) (fun i hi => hx i (by omega)) (fun i hi => hw i (by omega))
    have hxn := hx length (by omega)
    have hwn := hw length (by omega)
    have productBound : |decode (x length) * decode (w length)| ≤ 16129 := by
      rw [abs_mul]
      nlinarith [abs_nonneg (decode (x length)), abs_nonneg (decode (w length))]
    have productExact := mul_exact (x length) (w length)
      (by rw [abs_le] at productBound; omega)
      (by rw [abs_le] at productBound; omega)
    have bound := prefix_representable (decode ∘ x) (decode ∘ w) (length + 1) hl hx hw
    have sumStep : sumPrefix (decode ∘ x) (decode ∘ w) (length + 1) =
        sumPrefix (decode ∘ x) (decode ∘ w) length + decode (x length) * decode (w length) := by
      simp only [sumPrefix, Finset.sum_range_succ, Function.comp_apply]
    rw [sumStep] at bound ⊢
    have step : wordPrefix x w (length + 1) = wordPrefix x w length + x length * w length := by
      simp only [wordPrefix, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [step, add_exact]
    · rw [previous, productExact]
    · simpa only [previous, productExact] using bound.1
    · simpa only [previous, productExact] using bound.2

#print axioms byte_range
#print axioms add_exact
#print axioms mul_exact
#print axioms prefix_representable
#print axioms wordPrefix_exact

end Project.ProofKit.QuantizedInt32
