import Project.Beck.Preservation
import Mathlib.Data.List.MinMax

namespace Project.Beck.Boundary

open LeanExe.Examples.Beck

abbrev Step := UInt64 × UInt64

def candidate (x : Point) (d : Array UInt64) (job : Nat) : Step :=
  (gap x.denominator x.numerators[job]! d[job]!, magnitude d[job]!)

def select (next old : Step) : Step :=
  if next.2 != 0 then
    if old.2 == 0 || next.1 * old.2 < old.1 * next.2 then next else old
  else old

def ratio (step : Step) : ℚ := (step.1.toNat : ℚ) / step.2.toNat

def winner (get : Nat → Step) (jobs : List Nat) : Option Nat :=
  (jobs.filter fun job => (get job).2 != 0).argmin (fun job => ratio (get job))

theorem boundaryStep_eq (input : Input) (x : Point) (d : Array UInt64) :
    boundaryStep input x d =
      (List.range input.jobs).foldl (fun old job => select (candidate x d job) old) (0, 0) := by
  simp only [boundaryStep, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
  simp only [Id.run, bind, pure]
  have step : (fun (job : Nat) (old : Step) =>
      if magnitude d[job]! != 0 then
        if old.2 == 0 || gap x.denominator x.numerators[job]! d[job]! * old.2 < old.1 * magnitude d[job]!
        then ForInStep.yield (gap x.denominator x.numerators[job]! d[job]!, magnitude d[job]!)
        else ForInStep.yield old
      else ForInStep.yield old) =
      (fun job old => ForInStep.yield (select (candidate x d job) old)) := by
    funext job old
    simp only [select, candidate, ← apply_ite ForInStep.yield]
    rfl
  rw [step]
  exact List.forIn_pure_yield_eq_foldl (m := Id) _ _

theorem winner_member (get : Nat → Step) (jobs : List Nat) (job : Nat)
    (h : winner get jobs = some job) : job ∈ jobs ∧ (get job).2 ≠ 0 := by
  have member := List.argmin_mem h
  simpa [winner] using member

theorem fold_eq_winner (get : Nat → Step) (jobs : List Nat)
    (compare : ∀ i ∈ jobs, ∀ j ∈ jobs, (get i).2 ≠ 0 → (get j).2 ≠ 0 →
      ((get i).1 * (get j).2 < (get j).1 * (get i).2 ↔ ratio (get i) < ratio (get j))) :
    jobs.foldl (fun old job => select (get job) old) (0, 0) =
      ((winner get jobs).map get).getD (0, 0) := by
  induction jobs using List.reverseRecOn with
  | nil => simp [winner]
  | append_singleton jobs job ih =>
    have previous := ih (by intro i hi j hj; exact compare i (by simp [hi]) j (by simp [hj]))
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, previous]
    by_cases nonzero : (get job).2 ≠ 0
    · have filter : (jobs ++ [job]).filter (fun j => (get j).2 != 0) =
          (jobs.filter fun j => (get j).2 != 0) ++ [job] := by simp [nonzero]
      simp only [winner, filter, List.argmin_concat]
      change select (get job) (((winner get jobs).map get).getD (0, 0)) =
        ((Option.casesOn (motive := fun _ => Option Nat) (winner get jobs) (some job)
          (fun old => if ratio (get job) < ratio (get old) then some job else some old)).map get).getD (0, 0)
      cases h : winner get jobs with
      | none => simp [select, nonzero]
      | some old =>
        have member := winner_member get jobs old h
        have comparison := compare job (by simp) old (by simp [member.1]) nonzero member.2
        simp [select, nonzero, member.2, comparison]
        split_ifs <;> rfl
    · have filter : (jobs ++ [job]).filter (fun j => (get j).2 != 0) =
          jobs.filter (fun j => (get j).2 != 0) := by simp [nonzero]
      simp [select, nonzero, winner, filter]

theorem product_exact (a b : UInt64) (ha : a.toNat ≤ 2 * 120 ^ 5) (hb : b.toNat ≤ 120) :
    (a * b).toNat = a.toNat * b.toNat := by
  rw [UInt64.toNat_mul]
  apply Nat.mod_eq_of_lt
  have bound := Nat.mul_le_mul ha hb
  norm_num at bound ⊢
  omega

theorem compare_small (a b : Step)
    (ha : a.1.toNat ≤ 2 * 120 ^ 5 ∧ a.2.toNat ≤ 120)
    (hb : b.1.toNat ≤ 2 * 120 ^ 5 ∧ b.2.toNat ≤ 120)
    (an : a.2 ≠ 0) (bn : b.2 ≠ 0) :
    a.1 * b.2 < b.1 * a.2 ↔ ratio a < ratio b := by
  have ap : 0 < a.2.toNat := Nat.pos_of_ne_zero (by intro h; exact an (UInt64.toNat_inj.mp h))
  have bp : 0 < b.2.toNat := Nat.pos_of_ne_zero (by intro h; exact bn (UInt64.toNat_inj.mp h))
  rw [UInt64.lt_iff_toNat_lt, product_exact _ _ ha.1 hb.2, product_exact _ _ hb.1 ha.2,
    ratio, ratio, div_lt_div_iff₀ (by exact_mod_cast ap) (by exact_mod_cast bp)]
  exact_mod_cast Iff.rfl

theorem boundaryStep_spec (input : Input) (x : Point) (d : Array UInt64)
    (distances : ∀ job < input.jobs, (gap x.denominator x.numerators[job]! d[job]!).toNat ≤ 2 * 120 ^ 5)
    (speeds : ∀ job < input.jobs, (magnitude d[job]!).toNat ≤ 120)
    (moving : ∃ job < input.jobs, d[job]! ≠ 0) :
    ∃ first < input.jobs, d[first]! ≠ 0 ∧ boundaryStep input x d = candidate x d first ∧
      ∀ job < input.jobs, d[job]! ≠ 0 →
        (boundaryStep input x d).1.toNat * (magnitude d[job]!).toNat ≤
          (gap x.denominator x.numerators[job]! d[job]!).toNat * (boundaryStep input x d).2.toNat := by
  have comparison (i : Nat) (hi : i ∈ List.range input.jobs) (j : Nat) (hj : j ∈ List.range input.jobs) :=
    compare_small (candidate x d i) (candidate x d j)
      ⟨distances i (List.mem_range.mp hi), speeds i (List.mem_range.mp hi)⟩
      ⟨distances j (List.mem_range.mp hj), speeds j (List.mem_range.mp hj)⟩
  have result := fold_eq_winner (candidate x d) (List.range input.jobs) comparison
  cases chosen : winner (candidate x d) (List.range input.jobs) with
  | none =>
    have empty : (List.range input.jobs).filter (fun job => (candidate x d job).2 != 0) = [] :=
      List.argmin_eq_none.mp chosen
    obtain ⟨job, hj, hn⟩ := moving
    have member : job ∈ (List.range input.jobs).filter (fun job => (candidate x d job).2 != 0) := by
      simp [candidate, hj, Arithmetic.magnitude_zero, hn]
    simp [empty] at member
  | some first =>
    have member := winner_member (candidate x d) (List.range input.jobs) first chosen
    have nonzero : d[first]! ≠ 0 := by simpa [candidate, Arithmetic.magnitude_zero] using member.2
    have stepEq : boundaryStep input x d = candidate x d first := by
      rw [boundaryStep_eq, result, chosen]
      rfl
    refine ⟨first, List.mem_range.mp member.1, nonzero, stepEq, ?_⟩
    intro job hj hn
    have eligible : job ∈ (List.range input.jobs).filter (fun j => (candidate x d j).2 != 0) := by
      simp [candidate, hj, Arithmetic.magnitude_zero, hn]
    have least := List.le_of_mem_argmin eligible chosen
    have firstPositive : 0 < (candidate x d first).2.toNat :=
      Nat.pos_of_ne_zero (by intro h; exact member.2 (UInt64.toNat_inj.mp h))
    have jobPositive : 0 < (candidate x d job).2.toNat := by
      apply Nat.pos_of_ne_zero
      intro h
      exact hn ((Arithmetic.magnitude_zero _).mp (UInt64.toNat_inj.mp h))
    rw [ratio, ratio, div_le_div_iff₀ (by exact_mod_cast firstPositive) (by exact_mod_cast jobPositive)] at least
    rw [stepEq]
    exact_mod_cast least

end Project.Beck.Boundary
