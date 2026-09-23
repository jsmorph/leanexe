import LeanExe.Models.Gpt2.Cached
import Project.Gpt2CachedStep.GeluForwardError
import Project.Gpt2CachedStep.LayerNorm.Numerical
import Project.ProofKit.F32PairError

namespace Project.Gpt2CachedStep.PointwiseError
open LeanExe.Models.Gpt2 Project.ProofKit CodeLib.IEEE32
open LayerNorm.Numerical (word_generate)

theorem add_source (left right : ByteArray) (i : Nat) (hi : i < left.size / 4) :
    word (addRows left right) i = LeanExe.Float32.addBits (word left i) (word right i) := by
  exact word_generate _ _ i hi

theorem add_error (left right : ByteArray) (i : Nat) (hi : i < left.size / 4)
    (L R el er : ℝ) (bound : Nat) (hl : CodeLib.IEEE32.Finite (word left i)) (hr : CodeLib.IEEE32.Finite (word right i))
    (hb : bound ≤ 276)
    (hRange : (Wasm.IEEE32.scaledValue (word left i) + Wasm.IEEE32.scaledValue (word right i)).natAbs < 2 ^ bound)
    (hLeft : |value (word left i) - L| ≤ el) (hRight : |value (word right i) - R| ≤ er) :
    CodeLib.IEEE32.Finite (word (addRows left right) i) ∧
      |value (word (addRows left right) i) - (L + R)| ≤ F32AdditionBounds.epsilon bound + (el + er) := by
  rw [add_source left right i hi]
  exact F32ErrorPropagation.add _ _ _ _ _ _ _ hl hr hb hRange hLeft hRight

theorem activate_source (input : ByteArray) (i : Nat) (hi : i < input.size / 4) :
    word (activate input) i = gelu (word input i) := by
  exact word_generate _ _ i hi

theorem activate_error (input : ByteArray) (i : Nat) (hi : i < input.size / 4)
    (reference inputError : ℝ) (b : GeluForwardError.Bounds)
    (hf : CodeLib.IEEE32.Finite (word input i))
    (hRange : ¬F32Order.absBits (word input i) > 0x41000000 → GeluForwardError.Ranges (F32Order.absBits (word input i)) b)
    (he : |value (word input i) - reference| ≤ inputError) :
    CodeLib.IEEE32.Finite (word (activate input) i) ∧
      |value (word (activate input) i) - Project.Gelu.Real.gelu reference| ≤
        GeluForwardError.error (word input i) b + 4 * inputError := by
  rw [activate_source input i hi]
  exact GeluForwardError.reference_error _ _ _ _ hf hRange he

theorem cache_lookup_error (cache qkv cache' qkv' : ByteArray) (layer position source offset : Nat)
    (cacheError qkvError : Nat → ℝ)
    (hc : ∀ j, |value (word cache j) - value (word cache' j)| ≤ cacheError j)
    (hq : ∀ j, |value (word qkv j) - value (word qkv' j)| ≤ qkvError j) :
    |value (cachedKv cache qkv layer position source offset) - value (cachedKv cache' qkv' layer position source offset)| ≤
      if source < position then cacheError ((source * 12 + layer) * 1536 + offset) else qkvError (768 + offset) := by
  by_cases hh : source < position
  · simp only [cachedKv, ite_eq_left hh]
    exact hc ((source * 12 + layer) * 1536 + offset)
  · simp only [cachedKv, ite_eq_right hh]
    exact hq (768 + offset)

#print axioms add_error
#print axioms activate_error
#print axioms cache_lookup_error
end Project.Gpt2CachedStep.PointwiseError
