import Demos.Slew.Verified
import Demos.Slew.Search
import Demos.Slew.Valid

/-! The allocation bound of the slew planner.  `compiled.plan.bound` is the number of bytes by
which the module's `plan` can raise the allocator's `top`, which `compiled.plan.bound_eq` states
as a Lean function of the input, and `plan_bound` bounds it by 68,020,488 for every input.
`slew_trapFree` then states that the module computes `plan` without a trap whenever `top` can
rise by that much within the memory's cap.

The search state holds four arrays of `n = nw + 2` words.  `initial` builds them, and each round
of `search` copies them, since `round` takes the state as a parameter and the verified compiler
borrows record parameters, and `relax` copies them again.  `validInput` bounds `nw` by 1,024, so
`n` is at most 1,026, and the search runs at most `n + 1` rounds (`search_bound`).  `output`
builds `8 + 11 k` words for a path of `k ≤ n` edges, since `pathLength` counts at most one edge
for each step of its fuel `n` (`pathLength_le`).  The bound counts every copy and ignores the
reuse of freed blocks. -/

namespace Demos.Slew.Bound

open Demos.Slew Demos.Slew.Verified Demos.Slew.Search Demos.Slew.Valid
open _root_.Verified (blockCost blockCost_eq)

theorem relax_ok (xs : Array Float) (d : Dims) (n u settleTicks : UInt64) (s : Search) :
    (relax xs d n u settleTicks s).ok = s.ok := by
  unfold relax
  dsimp only
  refine LeanExe.Dialect.loop_induction (P := fun _ (st : Search) => st.ok = s.ok) rfl ?_
  intro k st _ hst
  split
  · exact hst
  · split
    · exact hst
    · split
      · split
        · exact hst
        · exact hst
      · exact hst

theorem round_ok (xs : Array Float) (d : Dims) (n settleTicks : UInt64) (s : Search) :
    (round xs d n settleTicks s).ok = s.ok := by
  unfold round
  generalize selectNext s n = p
  obtain ⟨u, c⟩ := p
  dsimp only
  split
  · rfl
  · split
    · rfl
    · exact relax_ok _ _ _ _ _ _

/-- The four arrays of a round's state have `n` entries each. -/
def Sized (xs : Array Float) (d : Dims) (n : UInt64) (s : Search) : Prop :=
  Inv xs d n s ∧ s.ok.size = n.toNat

theorem round_bound {xs : Array Float} {d : Dims} {n settleTicks : UInt64} {s : Search}
    (h : Sized xs d n s) :
    compiled.round.bound (xs, d, n, settleTicks, s) ≤ 8 * blockCost n.toNat := by
  obtain ⟨hi, hok⟩ := h
  rw [compiled.round.bound_eq, compiled.relax.bound_eq]
  simp only [hi.costSize, hi.parentSize, hi.doneSize, hok, size_set]
  split
  · omega
  · split <;> omega

/-- `initial` builds four arrays of `n` words, and each of at most `n + 1` rounds copies them
twice. -/
theorem search_bound (xs : Array Float) (d : Dims) (n settleTicks : UInt64)
    (hn : n.toNat + 1 < 2 ^ 64) :
    compiled.search.bound (xs, d, n, settleTicks) ≤
      4 * blockCost n.toNat + (n.toNat + 1) * (8 * blockCost n.toNat) := by
  rw [compiled.search.bound_eq, compiled.initial.bound_eq]
  have hn1 : (n + 1).toNat = n.toNat + 1 := by
    rw [UInt64.toNat_add]; simp only [UInt64.reduceToNat]; omega
  refine Nat.add_le_add (by omega) ?_
  refine Nat.le_trans (_root_.Verified.loopCost_le (fun _ s => Sized xs d n s)
    (fun _ => 8 * blockCost n.toNat) ?hcost ?hstep ?hI) ?_
  case hcost =>
    intro k s hs
    have := round_bound (s := s) (settleTicks := settleTicks) hs
    split <;> omega
  case hstep =>
    intro k s hs _
    exact ⟨round_inv hs.1 settleTicks,
      (congrArg Array.size (round_ok xs d n settleTicks s)).trans hs.2⟩
  case hI => exact ⟨initial_inv xs d n, LeanExe.Dialect.build_size _ _⟩
  exact Nat.le_of_eq (by rw [_root_.Verified.sumBelow_const, hn1])

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
module's `plan` can raise `top` are at most 68,020,488: four arrays of at most 1,026 words
built by `initial`, two copies of them in each of at most 1,027 rounds, and an output of at most
11,294 words. -/
theorem plan_bound (xs : Array Float) : compiled.plan.bound xs ≤ 68020488 := by
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
  refine Nat.le_trans (Nat.add_le_add (search_bound xs (dims xs) n _ (by omega))
    (output_bound xs (dims xs) _ n _ (by omega))) ?_
  have h1 : blockCost n.toNat ≤ 8264 := by rw [blockCost_eq]; omega
  have h2 : (n.toNat + 1) * (8 * blockCost n.toNat) ≤ 1027 * (8 * 8264) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h3 : blockCost (8 + 11 * n.toNat) ≤ 90408 := by rw [blockCost_eq]; omega
  omega

/-- The module's entry 28 computes `plan` without a trap whenever `top` can rise by 68,020,488
bytes within the memory's cap, and raises `top` by at most that much. -/
theorem slew_trapFree : LeanExe.Pipeline.ImplementsA false compiled.module 28 (fun x => plan x)
    (fun _ heap store => heap.Within store compiled.module 68020488)
    (fun _ heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + 68020488) :=
  compiled.plan.trapFree.mono (fun x _ _ h => h.mono (plan_bound x))
    fun x _ _ _ _ _ h => h.trans (Nat.add_le_add_left (plan_bound x) _)

end Demos.Slew.Bound
