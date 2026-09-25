import Project.ProofKit.QuantizationError
import CodeLib.IEEE32.Roundoff
import Project.ProofKit.GreedyMaximum

namespace Project.ProofKit.F32LogitCertificate
open CodeLib.IEEE32

def check (reference quantized : Array UInt32) (errors : Array Nat) (shift : Int) (winner : Nat) : Bool :=
  winner < reference.size && quantized.size == reference.size && errors.size == reference.size &&
    (List.range reference.size).all (fun i =>
      Wasm.IEEE32.isFinite reference[i]! && Wasm.IEEE32.isFinite quantized[i]! &&
      decide ((Wasm.IEEE32.scaledValue quantized[i]! - Wasm.IEEE32.scaledValue reference[i]! - shift).natAbs ≤ errors[i]!) &&
      (i == winner || decide (Wasm.IEEE32.scaledValue reference[winner]! - Wasm.IEEE32.scaledValue reference[i]! >
        (errors[winner]! : Int) + errors[i]!)))

noncomputable def realError (bound : Nat) : ℝ := bound / (2 : ℝ) ^ 149

theorem check_fields (reference quantized : Array UInt32) (errors : Array Nat) (shift : Int) (winner : Nat)
    (h : check reference quantized errors shift winner = true) :
    winner < reference.size ∧ quantized.size = reference.size ∧ errors.size = reference.size ∧
      ∀ i < reference.size, Finite reference[i]! ∧ Finite quantized[i]! ∧
        (Wasm.IEEE32.scaledValue quantized[i]! - Wasm.IEEE32.scaledValue reference[i]! - shift).natAbs ≤ errors[i]! ∧
        (i ≠ winner → Wasm.IEEE32.scaledValue reference[winner]! - Wasm.IEEE32.scaledValue reference[i]! >
          (errors[winner]! : Int) + errors[i]!) := by
  simpa only [check, CodeLib.IEEE32.Finite, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, or_iff_not_imp_left, and_assoc] using h

theorem scaled_error (reference quantized : UInt32) (error : Nat) (shift : Int)
    (h : (Wasm.IEEE32.scaledValue quantized - Wasm.IEEE32.scaledValue reference - shift).natAbs ≤ error) :
    |value quantized - (shift : ℝ) / 2 ^ 149 - value reference| ≤ realError error := by
  have hReal : |(Wasm.IEEE32.scaledValue quantized : ℝ) - Wasm.IEEE32.scaledValue reference - shift| ≤ (error : ℝ) := by
    have hInteger : |Wasm.IEEE32.scaledValue quantized - Wasm.IEEE32.scaledValue reference - shift| ≤ (error : Int) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast h
    exact_mod_cast hInteger
  simp only [value, realError, ← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 149)]
  convert div_le_div_of_nonneg_right hReal (by positivity : (0 : ℝ) ≤ 2 ^ 149) using 1 <;> congr 1 <;> ring

theorem sound (reference quantized : Array UInt32) (errors : Array Nat) (shift : Int) (winner : Nat)
    (h : check reference quantized errors shift winner = true) :
    winner < reference.size ∧ quantized.size = reference.size ∧
      (∀ i < reference.size, |value quantized[i]! - (shift : ℝ) / 2 ^ 149 - value reference[i]!| ≤ realError errors[i]!) ∧
      (∀ i < reference.size, i ≠ winner → value quantized[winner]! > value quantized[i]!) := by
  obtain ⟨hWinner, hSize, _, hFields⟩ := check_fields reference quantized errors shift winner h
  refine ⟨hWinner, hSize, fun i hi => scaled_error _ _ _ shift (hFields i hi).2.2.1, ?_⟩
  intro i hi hNe
  have hErrorI : |Wasm.IEEE32.scaledValue quantized[i]! -
      Wasm.IEEE32.scaledValue reference[i]! - shift| ≤ (errors[i]! : Int) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast (hFields i hi).2.2.1
  have hErrorWinner : |Wasm.IEEE32.scaledValue quantized[winner]! -
      Wasm.IEEE32.scaledValue reference[winner]! - shift| ≤ (errors[winner]! : Int) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast (hFields winner hWinner).2.2.1
  obtain ⟨_, hErrorI⟩ := abs_le.mp hErrorI
  obtain ⟨hErrorWinner, _⟩ := abs_le.mp hErrorWinner
  have hMargin := (hFields i hi).2.2.2 hNe
  have hScaled : Wasm.IEEE32.scaledValue quantized[i]! < Wasm.IEEE32.scaledValue quantized[winner]! := by omega
  have hReal : (Wasm.IEEE32.scaledValue quantized[i]! : ℝ) < Wasm.IEEE32.scaledValue quantized[winner]! := by
    exact_mod_cast hScaled
  exact div_lt_div_of_pos_right hReal (by positivity)

theorem greedy (reference quantized : Array UInt32) (errors : Array Nat) (shift : Int) (winner : Nat)
    (h : check reference quantized errors shift winner = true) :
    GreedyMaximum.index (fun i => Wasm.IEEE32.scaledValue quantized[i]!) quantized.size = winner := by
  obtain ⟨hWinner, hSize, _, hUnique⟩ := sound reference quantized errors shift winner h
  apply GreedyMaximum.unique _ _ winner (by omega)
  intro i hi hNe
  have hReal := hUnique i (by omega) hNe
  have hScaled : (Wasm.IEEE32.scaledValue quantized[i]! : ℝ) < Wasm.IEEE32.scaledValue quantized[winner]! :=
    (div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 ^ 149)).mp hReal
  exact_mod_cast hScaled

#print axioms greedy
#print axioms check_fields
#print axioms scaled_error
#print axioms sound
end Project.ProofKit.F32LogitCertificate
