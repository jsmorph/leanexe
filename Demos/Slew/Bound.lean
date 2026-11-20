import Demos.Slew.Verified
import Demos.Slew.Search
import Demos.Slew.Valid

/-! The allocation bound of the slew planner.  `compiled.plan.bound` is the number of bytes by
which the module's `plan` can raise the allocator's `top`, which `compiled.plan.bound_eq` states
as a Lean function of the input, and `plan_bound` bounds it by 123,464 for every input.
`slew_trapFree` then states that the module computes `plan` without a trap whenever `top` can
rise by that much within the memory's cap.

The search state holds four arrays of `n = nw + 2` words, which `initial` builds.  `round` and
`relax` take the state as an owned parameter, so the loop of `search` moves the state into
`round`, which moves it into `relax`, and both update the arrays in place: their bounds are 0
(`round_bound`), and the bound of `search` is that of `initial` (`search_bound`).  `validInput`
bounds `nw` by 1,024, so `n` is at most 1,026.  `output` builds `8 + 11 k` words for a path of
`k ≤ n` edges, since `pathLength` counts at most one edge for each step of its fuel `n`
(`pathLength_le`).  The bound ignores the reuse of freed blocks. -/

namespace Demos.Slew.Bound

open Demos.Slew Demos.Slew.Verified Demos.Slew.Search Demos.Slew.Valid
open _root_.Verified (blockCost blockCost_eq)

/-- A round allocates nothing: it updates the search's arrays in place. -/
theorem round_bound (xs : Array Float) (d : Dims) (n settleTicks : UInt64) (s : Search) :
    compiled.round.bound (xs, d, n, settleTicks, ⟨s⟩) = 0 :=
  compiled.round.bound_eq xs d n settleTicks s

/-- `initial` builds four arrays of `n` words, and the rounds allocate nothing. -/
theorem search_bound (xs : Array Float) (d : Dims) (n settleTicks : UInt64) :
    compiled.search.bound (xs, d, n, settleTicks) ≤ 4 * blockCost n.toNat := by
  rw [compiled.search.bound_eq, compiled.initial.bound_eq]
  omega


theorem statusOnly_bound (status : Float) (examined : UInt64) :
    compiled.statusOnly.bound (status, examined) = 88 := by
  rw [compiled.statusOnly.bound_eq, blockCost_eq]
  rfl

/-- `output` builds at most `8 + 11 n` words. -/
theorem output_bound (xs : Array Float) (d : Dims) (s : Search) (n settleTicks : UInt64)
    (hn : n.toNat ≤ 1026) :
    compiled.output.bound (xs, d, s, n, settleTicks) ≤ blockCost (8 + 11 * n.toNat) := by
  rw [compiled.output.bound_eq]
  have hk := pathLength_le s n
  split
  · rw [statusOnly_bound, blockCost_eq]; omega
  · have e : (8 + 11 * pathLength s n).toNat = 8 + 11 * (pathLength s n).toNat := by
      rw [UInt64.toNat_add, UInt64.toNat_mul]; simp only [UInt64.reduceToNat]; omega
    rw [e]
    simp only [blockCost_eq]
    omega

/-- **The allocation bound of the slew planner.**  For every input, the bytes by which the
module's `plan` can raise `top` are at most 123,464: four arrays of at most 1,026 words built by
`initial` and an output of at most 11,294 words. -/
theorem plan_bound (xs : Array Float) : compiled.plan.bound xs ≤ 123464 := by
  rw [compiled.plan.bound_eq]
  split
  · rw [statusOnly_bound]; omega
  split
  · rw [statusOnly_bound]; omega
  split
  · rw [statusOnly_bound]; omega
  rename_i hv _ _
  have hnw := (valid_good (by simpa using hv)).2.2
  set n := (dims xs).nw + 2
  have hn : n.toNat = (dims xs).nw.toNat + 2 := by
    rw [UInt64.toNat_add]; simp only [UInt64.reduceToNat]; omega
  refine Nat.le_trans (Nat.add_le_add (search_bound xs (dims xs) n _)
    (output_bound xs (dims xs) _ n _ (by omega))) ?_
  have h1 : blockCost n.toNat ≤ 8264 := by rw [blockCost_eq]; omega
  have h3 : blockCost (8 + 11 * n.toNat) ≤ 90408 := by rw [blockCost_eq]; omega
  omega

/-- The module's entry 28 computes `plan` without a trap whenever `top` can rise by 123,464
bytes within the memory's cap, and raises `top` by at most that much. -/
theorem slew_trapFree : LeanExe.Pipeline.ImplementsA false compiled.module 28 (fun x => plan x)
    (fun _ heap store => heap.Within store compiled.module 123464)
    (fun _ heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + 123464) :=
  compiled.plan.trapFree.mono (fun x _ _ h => h.mono (plan_bound x))
    fun x _ _ _ _ _ h => h.trans (Nat.add_le_add_left (plan_bound x) _)

end Demos.Slew.Bound
