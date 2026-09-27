import Project.Lidar.QueryGeometry
import LeanExe.WGSL.UIntCertificate
import Mathlib.Algebra.BigOperators.Fin

namespace Project.Lidar.ExactQuery
open LeanExe.WGSL

def lane (input : UInt.Input) (i : Nat) : UInt.Input := { input with direction := i }

/-- The summary reads the four resident scan results with the same parameters. -/
def results (kernel : UInt.Expr) (input : UInt.Input) : UInt.Input :=
  ⟨fun i => if i < 4 then kernel.eval32 (lane input i) else 0, input.params, 0⟩

def InRange (hit : ℝ → Prop) (range : Nat) : Prop :=
  ∃ t, 0 ≤ t ∧ t ≤ (range : ℝ) ∧ hit t

/-- Count selected beams that intersect geometry in range, not obstacles. -/
noncomputable def hitCount (input : UInt.Input) (hits : Nat → ℝ → Prop) : Nat := by
  classical
  exact ∑ i : Fin 4, if Summary.requested (input.params 3) i = true ∧
    InRange (hits i) (input.params 2) then 1 else 0

/-- The host's nearest-distance decoding; `none` is its reported miss. -/
def decodeNearest (range word : Nat) : Option Nat :=
  if word % 8192 ≤ range then some (word % 8192) else none

theorem first_inRange {hit : ℝ → Prop} {range answer : Nat}
    (first : Continuous.FirstHit hit range answer) :
    answer ≤ range ↔ InRange hit range := by
  constructor
  · intro h
    exact ⟨answer, Nat.cast_nonneg _, by exact_mod_cast h, first.2.1 h⟩
  · rintro ⟨t, nonneg, within, hit⟩
    have h := le_trans (first.2.2 t nonneg within hit) within
    exact_mod_cast h

theorem count_correct (input : UInt.Input) (hits : Nat → ℝ → Prop)
    (first : ∀ i, i < 4 → Continuous.FirstHit (hits i) (input.params 2) (input.scene i)) :
    Summary.count input = hitCount input hits := by
  classical
  have one (i : Nat) (hi : i < 4) : Summary.hits input i =
      if Summary.requested (input.params 3) i = true ∧ InRange (hits i) (input.params 2)
      then 1 else 0 := by
    simp [Summary.hits, ← first_inRange (first i hi)]
  simp only [hitCount, Fin.sum_univ_succ]
  simp [Summary.count, one, Nat.add_assoc]

/-- Meaning of both fields after decoding the one-word GPU readback. -/
def Decoded (input : UInt.Input) (hits : Nat → ℝ → Prop) (word : Nat) : Prop :=
  word / 8192 = hitCount input hits ∧
  Continuous.FirstHit (QueryGeometry.Hit input hits) (input.params 2) (word % 8192) ∧
  (decodeNearest (input.params 2) word = none ↔
    ¬ InRange (QueryGeometry.Hit input hits) (input.params 2)) ∧
  (∀ distance, decodeNearest (input.params 2) word = some distance →
    distance ≤ input.params 2 ∧
    Continuous.FirstHit (QueryGeometry.Hit input hits) (input.params 2) distance)

theorem decoded (input : UInt.Input) (hits : Nat → ℝ → Prop)
    (rangeBound : input.params 2 ≤ 4095)
    (first : ∀ i, i < 4 → Continuous.FirstHit (hits i) (input.params 2) (input.scene i)) :
    Decoded input hits (Summary.count input * 8192 + Summary.nearest input) := by
  have nearest := QueryGeometry.nearest_first input hits first
  have bound := nearest.1
  obtain ⟨count, distance⟩ := Summary.decode input (by omega)
  refine ⟨count.trans (count_correct input hits first), ?_, ?_, ?_⟩
  · rwa [distance]
  · simp only [decodeNearest, distance, ite_eq_right_iff, Option.some_ne_none, imp_false]
    exact not_congr (first_inRange nearest)
  · intro d h
    simp only [decodeNearest, distance] at h
    split at h
    · cases h
      exact ⟨by assumption, nearest⟩
    · cases h

/-- Actual scan and summary artifacts compose with the geometric readback
contract. Host buffer transfer and device conformance remain assumptions. -/
def Verified (scanSource summarySource : String) (kernel : UInt.Expr)
    (input : UInt.Input) (hits : Nat → ℝ → Prop) : Prop :=
  (∀ i, i < 4 → UInt.Executes scanSource (lane input i) (kernel.eval32 (lane input i))) ∧
  (let resident := results kernel input
   let word := Summary.count resident * 8192 + Summary.nearest resident
   UInt.Executes summarySource resident word ∧ Decoded resident hits word)

theorem verified (scanSource summarySource : String) (kernel : UInt.Expr)
    (scanCertified : UInt.Certified scanSource kernel)
    (summaryCertified : UInt.Certified summarySource LidarSummary.kernel)
    (input : UInt.Input) (bounded : input.Bounded 4095) (mask : input.params 3 < 16)
    (hits : Nat → ℝ → Prop)
    (first : ∀ i, i < 4 → Continuous.FirstHit (hits i) (input.params 2)
      (kernel.eval32 (lane input i))) :
    Verified scanSource summarySource kernel input hits := by
  have residentFirst : ∀ i, i < 4 → Continuous.FirstHit (hits i) (input.params 2)
      ((results kernel input).scene i) := by
    intro i hi
    simpa [results, hi] using first i hi
  have residentBound : (results kernel input).Bounded 4096 := by
    refine ⟨?_, fun i => Nat.le_trans (bounded.2.1 i) (by decide), by change 0 ≤ 4096; omega⟩
    intro i
    by_cases hi : i < 4
    · have h := (residentFirst i hi).1
      have hr := bounded.2.1 2
      omega
    · simp [results, hi]
  refine ⟨fun i _ => UInt.certified_executes scanCertified _, ?_,
    decoded _ hits (bounded.2.1 2) residentFirst⟩
  rw [← Summary.correct _ residentBound mask]
  exact UInt.certified_executes summaryCertified _

#print axioms verified
end Project.Lidar.ExactQuery
