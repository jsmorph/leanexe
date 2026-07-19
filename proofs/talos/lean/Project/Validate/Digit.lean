import Project.Validate.Program
import Project.Common
import LeanExe.Examples.AsciiDigits
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block

/-!
# Byte classification for `validateGeneric`

`func0` decides whether a byte value is an ASCII digit.  `digitFlag` is its
arithmetic specification.
-/

namespace Project.Validate.Spec

open Wasm
open Project.Common
open LeanExe.Examples.AsciiDigits

set_option maxHeartbeats 64000000

def digitFlag (b : UInt64) : UInt64 :=
  if 48 ≤ b ∧ b ≤ 57 then 1 else 0

theorem digitFlag_toUInt64 (b : UInt8) :
    digitFlag b.toUInt64 = if isAsciiDigit b then 1 else 0 := by
  unfold digitFlag isAsciiDigit
  by_cases h48 : 48 ≤ b.toNat
  · by_cases h57 : b.toNat ≤ 57
    · simp [h48, h57, UInt64.le_iff_toNat_le]
    · simp [h48, h57, UInt64.le_iff_toNat_le]
  · simp [h48, UInt64.le_iff_toNat_le]

/-- `func0` decides whether a byte value is an ASCII digit. -/
theorem func0_terminates (env : HostEnv Unit) (st : Store Unit) (b : UInt64) :
    TerminatesWith (m := «module») (id := 0) (initial := st) (env := env) [.i64 b]
      (fun st' vs => st' = st ∧ vs = [.i64 (digitFlag b)]) := by
  apply TerminatesWith.of_wp_entry_for (f := func0Def)
  · simp [«module»]
  · change wp «module» func0 _ st
      { params := [.i64 b], locals := [.i64 0], values := [] } env
    unfold func0
    wp_run
    refine wp_iff_cons rfl ?_
    by_cases h48 : (48 : UInt64) ≤ b
    · rw [if_pos (by simp [h48])]
      wp_run
      refine wp_iff_cons rfl ?_
      by_cases h57 : b ≤ (57 : UInt64)
      · rw [if_pos (by simp [h57])]
        wp_run
        simp [func0Def, digitFlag, h48, h57]
      · rw [if_neg (by simp [h57])]
        wp_run
        simp [func0Def, digitFlag, h48, h57]
    · rw [if_neg (by simp [h48])]
      wp_run
      simp [func0Def, digitFlag, h48]

end Project.Validate.Spec
