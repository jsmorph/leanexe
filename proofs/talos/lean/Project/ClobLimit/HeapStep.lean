import Project.ClobLimit.HeapProgram
import Project.ClobMatchFuel.LoopBranches

/-! The internal matcher's two allocation-bearing branches inherit the checked
source result, reusable-free-list state, allocator counters, and decreasing
loop measure from the exported matcher. The caller supplies the exact frame
relation established by the internal dispatcher. -/
namespace Project.ClobLimit.HeapStep
open Wasm Project.ClobFindBest.Model Project.LocalRegion
open Project.ClobMatchFuel Project.ClobMatchFuel.LoopInvariant
open Project.ClobLimit.HeapProgram

/-- A fallthrough assertion transported to the internal local layout. -/
def Post (P : AssertionF Unit) : Assertion Unit
  | .Fallthrough st target => ∃ source, layout.Related source target ∧ P st source
  | _ => False

set_option Elab.async false in
theorem full_spec (env : HostEnv Unit) (ctx : Context) (st : Store Unit)
    (base target : Locals) (data : RunningData) (facts : RunningFacts ctx st base data)
    (bounds : LoopBounds.StepBounds ctx st data) (hFuel : data.fuel ≠ 0) (i : Nat)
    (hRemaining : data.remaining ≠ 0)
    (hFind : findBestL data.orders ctx.taker = some i)
    (hQty : data.orders[i]!.oqty ≤ data.remaining)
    (hFrame : layout.Related
      (Iteration.quantityFrame base data.bookOwner data.book ctx.taker i data.orders[i]!) target) :
    wp Project.ClobLimit.«module» fullProg
      (Post (fun st1 s1 => RunningAt ctx st1 s1 ∧ measure st1 s1 < measure st base))
      st target env := by
  let P : Assertion Unit := fun c => match c with
    | .Fallthrough st1 s1 => RunningAt ctx st1 s1 ∧ measure st1 s1 < measure st base
    | _ => False
  have hSource : wp Project.ClobMatchFuel.«module» Iteration.fullBranchProg P st
      (Iteration.quantityFrame base data.bookOwner data.book ctx.taker i data.orders[i]!) env := by
    simpa only [List.append_nil] using
      (LoopBranches.full_spec env ctx st base data facts bounds hFuel i hRemaining
        hFind hQty P [] (by
          intro st1 s1 hRunning hMeasure
          simpa only [wp_simp, P] using And.intro hRunning hMeasure))
  exact wp_transport layout.frame SearchRegion.searchShift env st _ target _ hFrame
    full_portable full_allowed P _ (by
      intro a b h hP
      cases h <;> simp only [P] at hP
      all_goals try contradiction
      exact ⟨_, by assumption, hP⟩) hSource

set_option Elab.async false in
theorem partial_spec (env : HostEnv Unit) (ctx : Context) (st : Store Unit)
    (base target : Locals) (data : RunningData) (facts : RunningFacts ctx st base data)
    (bounds : LoopBounds.StepBounds ctx st data) (hFuel : data.fuel ≠ 0) (i : Nat)
    (hRemaining : data.remaining ≠ 0)
    (hFind : findBestL data.orders ctx.taker = some i)
    (hQty : ¬data.orders[i]!.oqty ≤ data.remaining)
    (hFrame : layout.Related
      (Iteration.quantityFrame base data.bookOwner data.book ctx.taker i data.orders[i]!) target) :
    wp Project.ClobLimit.«module» partialProg
      (Post (fun st1 s1 => CompletedAt ctx st1 s1 ∧ measure st1 s1 < measure st base))
      st target env := by
  let P : Assertion Unit := fun c => match c with
    | .Fallthrough st1 s1 => CompletedAt ctx st1 s1 ∧ measure st1 s1 < measure st base
    | _ => False
  have hSource : wp Project.ClobMatchFuel.«module» PartialBranch.partialBranchProg P st
      (Iteration.quantityFrame base data.bookOwner data.book ctx.taker i data.orders[i]!) env := by
    simpa only [List.append_nil] using
      (LoopBranches.partial_spec env ctx st base data facts bounds hFuel i hRemaining
        hFind hQty P [] (by
          intro st1 s1 hCompleted hMeasure
          simpa only [wp_simp, P] using And.intro hCompleted hMeasure))
  exact wp_transport layout.frame SearchRegion.searchShift env st _ target _ hFrame
    partial_portable partial_allowed P _ (by
      intro a b h hP
      cases h <;> simp only [P] at hP
      all_goals try contradiction
      exact ⟨_, by assumption, hP⟩) hSource

#print axioms full_spec
#print axioms partial_spec
end Project.ClobLimit.HeapStep
