import Project.ProofKit.F64ArithmeticBounds

namespace Project.ProofKit.F64SequentialSum
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

def sum (words : List UInt64) (initial : UInt64 := 0) : UInt64 :=
  words.foldl Wasm.IEEE64.add initial

theorem sum_error_aux (limit : Nat) (bound : ℝ) (hb : 0 ≤ bound)
    (hSmall : (limit : ℝ)*(limit+1)*arithmeticEpsilon ≤ 1)
    (hLarge : ((limit : ℝ)+1)*(bound+1) < (2:ℝ)^1023)
    (words : List UInt64) (initial : UInt64) (exactValue : ℝ) (count : Nat)
    (hCount : count+words.length ≤ limit)
    (hInitial : Finite initial) (hExact : |exactValue| ≤ (count : ℝ)*bound)
    (hError : |value initial-exactValue| ≤
      (count : ℝ)*((limit : ℝ)+1)*(bound+1)*arithmeticEpsilon)
    (hWords : ∀ word ∈ words, Finite word ∧ |value word| ≤ bound) :
    Finite (sum words initial) ∧
      |value (sum words initial)-(exactValue+(words.map value).sum)| ≤
        ((count+words.length : Nat) : ℝ)*((limit : ℝ)+1)*(bound+1)*arithmeticEpsilon := by
  induction words generalizing initial exactValue count with
  | nil => simpa only [sum, List.foldl_nil, List.map_nil, List.sum_nil,
      add_zero, List.length_nil, Nat.cast_zero] using And.intro hInitial hError
  | cons word rest ih =>
    obtain ⟨hFinite, hBound⟩ := hWords word (by simp)
    have hCount' : count+1 ≤ limit := by simp only [List.length_cons] at hCount; omega
    have hCountReal : (count : ℝ)+1 ≤ limit := by exact_mod_cast hCount'
    have heps : 0 ≤ arithmeticEpsilon := F64ArithmeticBounds.epsilon_pos.le
    have hLimit : (0:ℝ) ≤ limit := Nat.cast_nonneg _
    have hSlack : (count : ℝ)*((limit : ℝ)+1)*(bound+1)*arithmeticEpsilon ≤ bound+1 := by
      have hc : (count : ℝ) ≤ limit := by linarith
      calc
        _ ≤ (limit : ℝ)*((limit : ℝ)+1)*(bound+1)*arithmeticEpsilon := by gcongr
        _ = ((limit : ℝ)*(limit+1)*arithmeticEpsilon)*(bound+1) := by ring
        _ ≤ bound+1 := by nlinarith
    have hMagnitude := F64ArithmeticBounds.magnitude_of_error _ _ _ _ hError hExact
    have hAddBound : |value initial+value word| ≤ ((limit : ℝ)+1)*(bound+1) := by
      have ht := (abs_add_le (value initial) (value word)).trans (add_le_add hMagnitude hBound)
      nlinarith
    have hStep := F64ArithmeticBounds.add_error_scaled initial word hInitial hFinite
      (((limit : ℝ)+1)*(bound+1)) hLarge hAddBound
    have hNextExact : |exactValue+value word| ≤ ((count+1 : Nat) : ℝ)*bound := by
      have ht := (abs_add_le exactValue (value word)).trans (add_le_add hExact hBound)
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using ht
    have hNextError : |value (Wasm.IEEE64.add initial word)-(exactValue+value word)| ≤
        ((count+1 : Nat) : ℝ)*((limit : ℝ)+1)*(bound+1)*arithmeticEpsilon := by
      have ht := abs_sub_le (value (Wasm.IEEE64.add initial word))
        (value initial+value word) (exactValue+value word)
      rw [add_sub_add_right_eq_sub] at ht
      have hh := ht.trans (add_le_add hStep.2 hError)
      calc
        _ ≤ arithmeticEpsilon*(((limit : ℝ)+1)*(bound+1)) +
            (count : ℝ)*((limit : ℝ)+1)*(bound+1)*arithmeticEpsilon := hh
        _ = ((count+1 : Nat) : ℝ)*((limit : ℝ)+1)*(bound+1)*arithmeticEpsilon := by
          push_cast
          ring
    have hTail := ih (Wasm.IEEE64.add initial word) (exactValue+value word) (count+1)
      (by simp only [List.length_cons] at hCount; omega) hStep.1 hNextExact hNextError
      (fun x hx => hWords x (by simp [hx]))
    simpa only [sum, List.foldl_cons, List.map_cons, List.sum_cons, List.length_cons,
      Nat.add_assoc, Nat.add_comm 1, add_assoc] using hTail

theorem sum_error (limit : Nat) (bound : ℝ) (hb : 0 ≤ bound)
    (hSmall : (limit : ℝ)*(limit+1)*arithmeticEpsilon ≤ 1)
    (hLarge : ((limit : ℝ)+1)*(bound+1) < (2:ℝ)^1023)
    (words : List UInt64) (hLength : words.length ≤ limit)
    (hWords : ∀ word ∈ words, Finite word ∧ |value word| ≤ bound) :
    Finite (sum words) ∧
      |value (sum words)-(words.map value).sum| ≤
        (words.length : ℝ)*((limit : ℝ)+1)*(bound+1)*arithmeticEpsilon := by
  have hZero : value (0 : UInt64) = 0 := by
    norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
      Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction]
  have h := sum_error_aux limit bound hb hSmall hLarge words 0 0 0
    (by simpa using hLength) (by unfold CodeLib.IEEE64.Finite; decide)
    (by simp) (by simp [hZero]) hWords
  simpa using h

theorem array_sum_error (limit : Nat) (bound : ℝ) (hb : 0 ≤ bound)
    (hSmall : (limit : ℝ)*(limit+1)*arithmeticEpsilon ≤ 1)
    (hLarge : ((limit : ℝ)+1)*(bound+1) < (2:ℝ)^1023)
    (words : Array UInt64) (hLength : words.size ≤ limit)
    (hWords : ∀ word ∈ words, Finite word ∧ |value word| ≤ bound) :
    Finite (words.foldl Wasm.IEEE64.add 0) ∧
      |value (words.foldl Wasm.IEEE64.add 0)-(words.toList.map value).sum| ≤
        (words.size : ℝ)*((limit : ℝ)+1)*(bound+1)*arithmeticEpsilon := by
  simpa only [sum, Array.foldl_toList, Array.length_toList] using
    sum_error limit bound hb hSmall hLarge words.toList (by simpa using hLength)
      (by simpa using hWords)

#print axioms sum_error
#print axioms array_sum_error
end Project.ProofKit.F64SequentialSum
