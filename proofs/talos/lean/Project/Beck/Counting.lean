import Project.Beck.Basis
import Project.Beck.Rounding

namespace Project.Beck.Counting

open LeanExe.Examples.Beck
open Finset

def members (input : Input) (category : Fin input.categories) : Finset (Fin input.jobs) :=
  univ.filter fun job => input.incidence[job.val * input.categories + category.val]! = 1

def live (input : Input) (x : Point) : Finset (Fin input.jobs) :=
  univ.filter fun job => frozen x job.val = false

theorem liveCount_sum (input : Input) (x : Point) (category : Nat) :
    liveCount input x category =
      ∑ job : Fin input.jobs,
        if (!frozen x job.val && input.incidence[job.val * input.categories + category]! == 1)
        then 1 else 0 := by
  have step (p : Bool) (n : Nat) : (if p then n + 1 else n) = n + if p then 1 else 0 := by
    cases p <;> simp
  simp only [liveCount, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
  simp only [Id.run, bind, pure, ← apply_ite ForInStep.yield]
  have callback : (fun (j acc : Nat) => ForInStep.yield
      (if (!frozen x j && input.incidence[j * input.categories + category]! == 1)
       then acc + 1 else acc)) =
      (fun (j acc : Nat) => ForInStep.yield (acc +
        if (!frozen x j && input.incidence[j * input.categories + category]! == 1)
        then 1 else 0)) := by
    funext j acc
    congr 1
    exact step _ _
  rw [callback]
  have fold (f : Nat → Nat) :
      (forIn (List.range input.jobs) 0 (fun j acc => ForInStep.yield (acc + f j)) : Id Nat) =
        ((List.range input.jobs).map f).sum := by
    rw [List.sum_eq_foldl, List.foldl_map]
    exact List.forIn_pure_yield_eq_foldl (m := Id) (fun j acc => acc + f j) 0
  rw [fold, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range, Finset.sum_range]

theorem liveCount_card (input : Input) (x : Point) (category : Fin input.categories) :
    liveCount input x category.val =
      ((live input x).filter fun job => job ∈ members input category).card := by
  rw [liveCount_sum]
  have sets : ((live input x).filter fun job => job ∈ members input category) =
      univ.filter (fun job : Fin input.jobs =>
        (!frozen x job.val && input.incidence[job.val * input.categories + category.val]! == 1) = true) := by
    ext job
    simp [live, members]
  rw [sets, Finset.card_filter]

def protectedRows (input : Input) (x : Point) : Finset (Fin input.categories) :=
  univ.filter fun category => input.overlap < liveCount input x category.val

theorem protected_eq (input : Input) (x : Point) :
    protectedRows input x = Rounding.protectedCategories (members input) (live input x) input.overlap := by
  ext category
  simp [protectedRows, Rounding.protectedCategories, liveCount_card]

theorem protected_fewer (input : Input) (x : Point)
    (overlap : ∀ job : Fin input.jobs,
      (univ.filter fun category => job ∈ members input category).card ≤ input.overlap)
    (nonempty : (live input x).Nonempty) :
    (protectedRows input x).card < (live input x).card := by
  rw [protected_eq]
  exact Rounding.protected_card_lt _ _ _ overlap nonempty

end Project.Beck.Counting
