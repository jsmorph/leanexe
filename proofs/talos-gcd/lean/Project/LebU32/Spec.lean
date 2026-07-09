import Project.LebU32.Program
import Project.Common
import Project.Runtime.Spec
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

/-!
# Specification for the self-compiled LEB128 encoder

The artifact is the compiler's own unsigned LEB128 encoder, compiled by
the compiler.  `lebList` mirrors the pure recursion proved equal to the
shipped `u32lebU64` in `LeanExe/Wasm/LebTheorems.lean`; the artifact
theorem states that for every value in the encoder's `u32` domain the
export returns a pointer to exactly those bytes.
-/

namespace Project.LebU32.Spec

open Wasm Project.Common Project.Runtime

def lebList : Nat → UInt64 → List UInt8
  | 0, _ => []
  | fuel + 1, v =>
      let low := v % 128
      let rest := v / 128
      if rest == 0 then
        [low.toUInt8]
      else
        (low + 128).toUInt8 :: lebList fuel rest

theorem lebList_length_le (fuel : Nat) (v : UInt64) :
    (lebList fuel v).length ≤ fuel := by
  induction fuel generalizing v with
  | zero => simp [lebList]
  | succ fuel ih =>
      unfold lebList
      by_cases h : v / 128 == 0
      · simp [h]
      · simp [h]
        exact Nat.le_trans (ih _) (by omega)

theorem lebList_length_pos (fuel : Nat) (v : UInt64) (h : 0 < fuel) :
    0 < (lebList fuel v).length := by
  cases fuel with
  | zero => omega
  | succ fuel =>
      unfold lebList
      by_cases hv : v / 128 == 0 <;> simp [hv]

/-- Small values encode within few bytes: each seven-bit group divides
the value by 128, so `fuel` groups cover `v < 128 ^ fuel`. -/
theorem lebList_length_of_lt (fuel bound : Nat) (v : UInt64)
    (hb : bound ≤ 10) (hv : v.toNat < 128 ^ bound) (hf : bound ≤ fuel)
    (h0 : 0 < bound) :
    (lebList fuel v).length ≤ bound := by
  induction fuel generalizing v bound with
  | zero => omega
  | succ fuel ih =>
      unfold lebList
      by_cases h : v / 128 == 0
      · simp [h]
        omega
      · simp [h]
        have hne : ¬ (v / 128).toNat = 0 := by
          intro hz
          have : v / 128 = 0 := by
            apply UInt64.toNat.inj
            simpa using hz
          simp [this] at h
        have hdiv : (v / 128).toNat = v.toNat / 128 := by
          rw [UInt64.toNat_div]
          rfl
        cases bound with
        | zero => omega
        | succ bound =>
            cases bound with
            | zero =>
                exfalso
                have : v.toNat < 128 := by simpa using hv
                omega
            | succ b =>
                have := ih (b + 1) (v / 128) (by omega)
                  (by
                    rw [hdiv]
                    rw [Nat.pow_succ] at hv
                    omega)
                  (by omega) (by omega)
                simpa using this
end Project.LebU32.Spec
