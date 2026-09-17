import Project.TinyGpt2.CheckpointCoefficients
import Project.TinyGpt2.Rows
import Project.ProofKit.F64Bounded

namespace Project.TinyGpt2.Checkpoint
open CodeLib.IEEE64 Project.ProofKit F64Horner

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem embedding_words_bounded :
    (words.toList.take 1040).all
      (fun word => decide (F64Order.absBits word ≤ 0x3FE0000000000000)) = true := by
  decide +kernel

theorem embedding_word_bounded (i : Nat) (hi : i < 1040) :
    Finite words[i]! ∧ |value words[i]!| ≤ 1/2 := by
  have hw : i < words.size := by rw [words_size]; omega
  have hm : words[i]! ∈ words.toList.take 1040 := by
    apply List.mem_iff_getElem.mpr
    refine ⟨i, by simp only [List.length_take, Array.length_toList]; omega, ?_⟩
    simp only [List.getElem_take, Array.getElem_toList, getElem!_pos, hw]
  have hb := List.all_eq_true.mp embedding_words_bounded _ hm
  have he : F64Order.absBits 0x3FE0000000000000 = 0x3FE0000000000000 := by
    decide +kernel
  have hf : Finite 0x3FE0000000000000 := by unfold CodeLib.IEEE64.Finite; decide +kernel
  have h := (F64Order.absBits_le_iff words[i]! 0x3FE0000000000000 hf).mp
    (by simpa only [he, decide_eq_true_eq] using hb)
  have hv : value 0x3FE0000000000000 = (1:ℝ)/2 := by
    have hdecode : F64Rational.decode 0x3FE0000000000000 = 1/2 := by decide +kernel
    rw [← F64Rational.decode_cast, hdecode]
    norm_num
  simpa only [hv, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)] using h

theorem embedding_error (token position : UInt64)
    (ht : token.toNat < 256) (hp : position.toNat < 4) (i : Fin 4) :
    Approximation (rowWords (embedding words token position) i)
      (decodeRow (loadRow words (4*token.toNat)) i+
        decodeRow (loadRow words (1024+4*position.toNat)) i)
      (1001/1000) (128*arithmeticEpsilon) := by
  have htrow (i : Fin 4) :
      Finite (rowWords (loadRow words (4*token.toNat)) i) ∧
        |decodeRow (loadRow words (4*token.toNat)) i| ≤ 1/2 := by
    simpa only [decodeRow, loadRow_words] using
      embedding_word_bounded (4*token.toNat+i.val) (by omega)
  have hprow (i : Fin 4) :
      Finite (rowWords (loadRow words (1024+4*position.toNat)) i) ∧
        |decodeRow (loadRow words (1024+4*position.toNat)) i| ≤ 1/2 := by
    simpa only [decodeRow, loadRow_words] using
      embedding_word_bounded (1024+4*position.toNat+i.val) (by omega)
  have he := addRows_error (loadRow words (4*token.toNat))
    (loadRow words (1024+4*position.toNat))
    (fun j => ⟨(htrow j).1, (htrow j).2.trans (by norm_num)⟩)
    (fun j => ⟨(hprow j).1, (hprow j).2.trans (by norm_num)⟩) i
  have hs := (abs_add_le _ _).trans (add_le_add (htrow i).2 (hprow i).2)
  have hm := F64ArithmeticBounds.magnitude_of_error _ _ _ _ he.accuracy hs
  simpa only [embedding, Layout.token, Layout.position, Nat.zero_add] using
    (show Approximation _ _ (1001/1000) (128*arithmeticEpsilon) from
      ⟨he.finite, hm.trans (by norm_num [arithmeticEpsilon]), he.accuracy⟩)

theorem embedding_valid (token position : UInt64)
    (ht : token.toNat < 256) (hp : position.toNat < 4) :
    LayerNorm.ValidRow (rowWords (embedding words token position)) := by
  intro i
  have h := embedding_error token position ht hp i
  exact ⟨h.finite, h.magnitude.trans (by norm_num)⟩

#print axioms embedding_valid
end Project.TinyGpt2.Checkpoint
