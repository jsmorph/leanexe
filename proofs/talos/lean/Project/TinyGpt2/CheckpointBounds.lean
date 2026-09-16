import Project.TinyGpt2.CheckpointWords
import Project.LayerNorm.Bounds

namespace Project.TinyGpt2.Checkpoint

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem all_bounded : words.toList.all LayerNorm.bounded = true := by decide +kernel

theorem word_bounded (i : Nat) (hi : i < words.size) :
    CodeLib.IEEE64.Finite words[i] ∧ |CodeLib.IEEE64.value words[i]| ≤ 4 := by
  apply (LayerNorm.bounded_iff _).mp
  exact Array.all_eq_true.mp (by simpa only [Array.all_toList] using all_bounded) i hi

#print axioms word_bounded
end Project.TinyGpt2.Checkpoint
