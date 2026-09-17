import Project.TinyGpt2.Checked
import Project.TinyGpt2.NumericalLogits

namespace Project.TinyGpt2
open CodeLib.IEEE64

theorem inferChecked_accept (weights : Array UInt64) (bound : UInt64)
    (tokens : Real.Tokens) (ha : F64Clip.accepted Layout.size bound weights = true) :
    inferChecked weights bound (tokenWords tokens 0) (tokenWords tokens 1)
        (tokenWords tokens 2) (tokenWords tokens 3) =
      infer (F64Clip.prepare Layout.size bound weights) (tokenWords tokens 0)
        (tokenWords tokens 1) (tokenWords tokens 2) (tokenWords tokens 3) := by
  have h0 := tokenWords_valid tokens 0
  have h1 := tokenWords_valid tokens 1
  have h2 := tokenWords_valid tokens 2
  have h3 := tokenWords_valid tokens 3
  simp [inferChecked, UInt64.lt_iff_toNat_lt, h0, h1, h2, h3,
    F64Clip.prepare_size Layout.size bound weights ha]

theorem inferChecked_reject (weights : Array UInt64) (bound t0 t1 t2 t3 : UInt64)
    (ha : F64Clip.accepted Layout.size bound weights = false) :
    inferChecked weights bound t0 t1 t2 t3 = #[] := by
  have hEmpty : F64Clip.prepare Layout.size bound weights = #[] := by
    simp [F64Clip.prepare, ha]
  simp only [inferChecked, hEmpty]
  norm_num [Layout.size]

theorem inferChecked_reject_token (weights : Array UInt64) (bound t0 t1 t2 t3 : UInt64)
    (hToken : 256 ≤ t0.toNat ∨ 256 ≤ t1.toNat ∨ 256 ≤ t2.toNat ∨ 256 ≤ t3.toNat) :
    inferChecked weights bound t0 t1 t2 t3 = #[] := by
  rcases hToken with h | h | h | h <;>
    simp [inferChecked, UInt64.lt_iff_toNat_lt, Nat.not_lt.mpr h]

theorem inferChecked_bounded (weights : Array UInt64) (bound : UInt64)
    (tokens : Real.Tokens) (ha : F64Clip.accepted Layout.size bound weights = true) :
    ∀ token : Fin 256, Affine.Bounded
      (inferChecked weights bound (tokenWords tokens 0) (tokenWords tokens 1)
        (tokenWords tokens 2) (tokenWords tokens 3))[token.val]! 1260 := by
  rw [inferChecked_accept weights bound tokens ha]
  exact clipped_infer_bounded bound weights ha (tokenWords tokens) (tokenWords_valid tokens)

theorem inferChecked_accuracy (weights : Array UInt64) (bound : UInt64)
    (tokens : Real.Tokens) (ha : F64Clip.accepted Layout.size bound weights = true) (j : Fin 256) :
    |value (inferChecked weights bound (tokenWords tokens 0) (tokenWords tokens 1)
      (tokenWords tokens 2) (tokenWords tokens 3))[j.val]!-
      Real.logits (parameters (F64Clip.prepare Layout.size bound weights)) tokens 3 j| ≤
        ErrorBudget.logits (value bound) (Real.sqrt (1/100000))
          (Real.sqrt (1/100000)) (Real.sqrt (1/100000)) := by
  rw [inferChecked_accept weights bound tokens ha]
  exact clipped_infer_accuracy bound weights ha tokens j

theorem inferChecked_error_magnitude (weights : Array UInt64) (bound : UInt64)
    (tokens : Real.Tokens) (ha : F64Clip.accepted Layout.size bound weights = true) (j : Fin 256) :
    |value (inferChecked weights bound (tokenWords tokens 0) (tokenWords tokens 1)
      (tokenWords tokens 2) (tokenWords tokens 3))[j.val]!-
      Real.logits (parameters (F64Clip.prepare Layout.size bound weights)) tokens 3 j| ≤
        1260+12*(value bound)^2+value bound := by
  have hc := (inferChecked_bounded weights bound tokens ha j).2
  have hr := clipped_real_logits_magnitude bound weights ha tokens 3 j
  exact (abs_sub _ _).trans (by simpa only [add_assoc] using add_le_add hc hr)

#print axioms inferChecked_accept
#print axioms inferChecked_reject
#print axioms inferChecked_reject_token
#print axioms inferChecked_bounded
#print axioms inferChecked_accuracy
#print axioms inferChecked_error_magnitude
end Project.TinyGpt2
