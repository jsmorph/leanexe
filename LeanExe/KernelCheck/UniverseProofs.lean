import LeanExe.KernelCheck.Universe
import Init.Data.UInt.Lemmas
import Lean.Elab.Tactic.Omega

namespace LeanExe.KernelCheck

/-- Mathematical impredicative maximum on unbounded natural levels. -/
def imaxNat (u v : Nat) : Nat := if v = 0 then 0 else max u v

theorem maxLevel_correct (u v : UInt64) :
    (maxLevel u v).toNat = max u.toNat v.toNat := by
  unfold maxLevel
  split
  · next h =>
      have hnat := UInt64.lt_iff_toNat_lt.mp h
      exact (Nat.max_eq_right (Nat.le_of_lt hnat)).symm
  · next h =>
      have hnat : ¬ u.toNat < v.toNat := by simpa [UInt64.lt_iff_toNat_lt] using h
      exact (Nat.max_eq_left (Nat.le_of_not_gt hnat)).symm

theorem imaxLevel_correct (u v : UInt64) :
    (imaxLevel u v).toNat = imaxNat u.toNat v.toNat := by
  by_cases h : v = 0
  · simp [imaxLevel, imaxNat, h]
  · have hn : v.toNat ≠ 0 := by
      intro eq
      apply h
      apply UInt64.toNat.inj
      simpa using eq
    simp [imaxLevel, imaxNat, h, hn, maxLevel_correct]

private theorem claim_accept_iff (actual expected : UInt64) :
    (if expected == actual then (0 : UInt64) else 1) = 0 ↔
      expected.toNat = actual.toNat := by
  by_cases h : expected = actual <;> simp [h, UInt64.toNat_inj]

private theorem claim_reject_iff (actual expected : UInt64) :
    (if expected == actual then (0 : UInt64) else 1) = 1 ↔
      expected.toNat ≠ actual.toNat := by
  by_cases h : expected = actual <;> simp [h, UInt64.toNat_inj]

theorem checkMax_accept_iff (u v expected : UInt64) :
    checkLevelOp 0 u v expected = 0 ↔ expected.toNat = max u.toNat v.toNat := by
  simpa [checkLevelOp, maxLevel_correct] using claim_accept_iff (maxLevel u v) expected

theorem checkIMax_accept_iff (u v expected : UInt64) :
    checkLevelOp 1 u v expected = 0 ↔ expected.toNat = imaxNat u.toNat v.toNat := by
  simpa [checkLevelOp, imaxLevel_correct] using claim_accept_iff (imaxLevel u v) expected

theorem checkMax_reject_iff (u v expected : UInt64) :
    checkLevelOp 0 u v expected = 1 ↔ expected.toNat ≠ max u.toNat v.toNat := by
  simpa [checkLevelOp, maxLevel_correct] using claim_reject_iff (maxLevel u v) expected

theorem checkIMax_reject_iff (u v expected : UInt64) :
    checkLevelOp 1 u v expected = 1 ↔ expected.toNat ≠ imaxNat u.toNat v.toNat := by
  simpa [checkLevelOp, imaxLevel_correct] using claim_reject_iff (imaxLevel u v) expected

theorem checkLevelOp_unsupported (op u v expected : UInt64) (h0 : op ≠ 0) (h1 : op ≠ 1) :
    checkLevelOp op u v expected = 3 := by
  simp [checkLevelOp, h0, h1]

end LeanExe.KernelCheck
