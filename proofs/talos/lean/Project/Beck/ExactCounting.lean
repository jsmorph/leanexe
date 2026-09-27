import LeanExe.Examples.BeckExact
import Project.Beck.Rounding

namespace Project.Beck.ExactCounting

open LeanExe.Examples.BeckExact
open LeanExe.Examples.Beck (Input)
open Finset

def members (input : Input) (category : Fin input.categories) : Finset (Fin input.jobs) :=
  univ.filter fun job => input.incidence[job.val * input.categories + category.val]! = 1

def live (input : Input) (point : Point) : Finset (Fin input.jobs) :=
  univ.filter fun job => frozen point job.val = false

def protectedRows (input : Input) (point : Point) : Finset (Fin input.categories) :=
  univ.filter fun category => input.overlap < liveCount input point category.val

theorem liveCount_sum (input : Input) (point : Point) (category : ℕ) :
    liveCount input point category = ∑ job : Fin input.jobs,
      if !frozen point job.val && input.incidence[job.val * input.categories + category]! == 1
      then 1 else 0 := by
  have add (test : Bool) (total : ℕ) :
      (if test then total + 1 else total) = total + if test then 1 else 0 := by
    cases test <;> simp
  simp only [liveCount, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
  simp only [Id.run, bind, pure, ← apply_ite ForInStep.yield]
  have callback : (fun (job total : ℕ) => ForInStep.yield
      (if !frozen point job && input.incidence[job * input.categories + category]! == 1
       then total + 1 else total)) =
      (fun (job total : ℕ) => ForInStep.yield (total +
        if !frozen point job && input.incidence[job * input.categories + category]! == 1
        then 1 else 0)) := by
    funext job total
    congr 1
    exact add _ _
  rw [callback]
  have fold (f : ℕ → ℕ) :
      (forIn (List.range input.jobs) 0 (fun job total => ForInStep.yield (total + f job)) : Id ℕ) =
        ((List.range input.jobs).map f).sum := by
    rw [List.sum_eq_foldl, List.foldl_map]
    exact List.forIn_pure_yield_eq_foldl (m := Id) (fun job total => total + f job) 0
  rw [fold, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range, Finset.sum_range]

theorem liveCount_card (input : Input) (point : Point) (category : Fin input.categories) :
    liveCount input point category.val =
      ((live input point).filter fun job => job ∈ members input category).card := by
  rw [liveCount_sum]
  have sets : ((live input point).filter fun job => job ∈ members input category) =
      univ.filter (fun job : Fin input.jobs =>
        (!frozen point job.val && input.incidence[job.val * input.categories + category.val]! == 1) = true) := by
    ext job
    simp [live, members]
  rw [sets, Finset.card_filter]

theorem protected_fewer (input : Input) (point : Point)
    (overlap : ∀ job : Fin input.jobs,
      (univ.filter fun category => job ∈ members input category).card ≤ input.overlap)
    (nonempty : (live input point).Nonempty) :
    (protectedRows input point).card < (live input point).card := by
  have equal : protectedRows input point =
      Rounding.protectedCategories (members input) (live input point) input.overlap := by
    ext category
    simp [protectedRows, Rounding.protectedCategories, liveCount_card]
  rw [equal]
  exact Rounding.protected_card_lt _ _ _ overlap nonempty

#print axioms protected_fewer

end Project.Beck.ExactCounting
