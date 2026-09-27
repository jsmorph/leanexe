import Project.ClobLimit.HeapFrames

/-! Transport the complete selected-maker path, including its quantity test.
The two allocator branches keep the shared matcher's invariant and measure. -/
namespace Project.ClobLimit.HeapSelect
open Wasm Project.Clob Project.ClobFindBest.Model Project.LocalRegion Project.FunctionRegion
open Project.ClobMatchFuel Project.ClobMatchFuel.LoopInvariant
open Project.ClobLimit.HeapProgram
set_option maxRecDepth 1048576
set_option maxHeartbeats 8000000

def sourceProg : Program := SelectedMaker.readProg ++
  [.localGet 38, .localGet 18, .leUI64,
   .iff 0 0 Iteration.fullBranchProg PartialBranch.partialBranchProg]

def program : Program := readProg ++
  [.localGet 32, .localGet 10, .leUI64, .iff 0 0 fullProg partialProg]

theorem program_eq : program = rename sourceProg := rfl

theorem portable : Project.FunctionRegion.PortableProgram SearchRegion.SearchDomain sourceProg := by
  prove_portable
  all_goals simp [SearchRegion.SearchDomain]

theorem allowed : AllowedProgram Domain sourceProg := by
  repeat' (first | exact True.intro | apply And.intro)
  all_goals simp [AllowedInstruction, Domain]

set_option Elab.async false in
theorem source_spec (env : HostEnv Unit) (ctx : Context) (st : Store Unit)
    (base : Locals) (data : RunningData) (facts : RunningFacts ctx st base data)
    (hFuel : data.fuel ≠ 0) (i : Nat) (hRemaining : data.remaining ≠ 0)
    (hFind : findBestL data.orders ctx.taker = some i) :
    wp Project.ClobMatchFuel.«module» sourceProg
      (fun c => match c with
        | .Fallthrough st1 s1 => Invariant ctx st1 s1 ∧ measure st1 s1 < measure st base
        | _ => False)
      st (Iteration.searchFrame base data.bookOwner data.book ctx.taker (some i)) env := by
  rcases facts.locals with ⟨hp, hl, hv, hf, ho, ht, hs, hpr, hq, hbo, hb, htr, hr, _⟩
  have hb' : base.locals[6]? = some (.i64 data.book) := by
    simpa [Locals.get, hp, hl] using hb
  have hr' : base.locals[9] = .i64 data.remaining := by
    simpa [Locals.get, hp, hl] using hr
  have hLength : data.orders.length < 4294967296 := by
    have h := facts.book32
    unfold fixedArrayBytes at h
    omega
  have hi := findBestL_some_lt data.orders ctx.taker i hFind
  have bounds := LoopBounds.of_running ctx st base data facts hFuel
  unfold sourceProg
  apply SelectedMaker.read_spec env st
    (Iteration.searchFrame base data.bookOwner data.book ctx.taker (some i)) data.book data.orders i
    (by simpa [Iteration.searchFrame] using hp)
    (by simp [Iteration.searchFrame, Iteration.searchLocals, hl]) rfl
    (by simpa [Iteration.searchFrame, Iteration.searchLocals, hl] using hb')
    (by simp [Iteration.searchFrame, Iteration.searchLocals, hl, optionPayload])
    hLength hi facts.bookOwned.2
  wp_run_with [SelectedMaker.cacheFrame, SelectedMaker.cacheLocals,
    Iteration.searchFrame, Iteration.searchLocals, hp, hl, hr']
  refine wp_iff_cons rfl ?_
  simp only [← List.getElem!_eq_getElem?_getD]
  let P : Assertion Unit := fun c => match c with
    | .Fallthrough st1 s1 => Invariant ctx st1 s1 ∧ measure st1 s1 < measure st base
    | _ => False
  by_cases hQty : data.orders[i]!.oqty ≤ data.remaining
  · rw [if_pos hQty]
    have hBranch : wp Project.ClobMatchFuel.«module» Iteration.fullBranchProg P st
        (Iteration.quantityFrame base data.bookOwner data.book ctx.taker i data.orders[i]!) env := by
      simpa only [List.append_nil] using
        (LoopBranches.full_spec env ctx st base data facts bounds hFuel i hRemaining hFind hQty P []
          (by intro st1 s1 hRun hMeasure; simpa [wp_simp, P, Invariant] using And.intro (Or.inl hRun) hMeasure))
    refine wp.imp hBranch ?_
    intro c hc
    cases c <;> simp only [P] at hc
    rename_i st1 s1
    rcases hc with ⟨hInv, hm⟩
    have hValues := hInv.values
    have hFrame : { s1 with values := [] } = s1 := by
      cases s1
      simp_all
    simpa [wp_simp, hFrame] using And.intro hInv hm
  · rw [if_neg hQty]
    have hBranch : wp Project.ClobMatchFuel.«module» PartialBranch.partialBranchProg P st
        (Iteration.quantityFrame base data.bookOwner data.book ctx.taker i data.orders[i]!) env := by
      simpa only [List.append_nil] using
        (LoopBranches.partial_spec env ctx st base data facts bounds hFuel i hRemaining hFind hQty P []
          (by intro st1 s1 hDone hMeasure; simpa [wp_simp, P, Invariant] using And.intro (Or.inr hDone) hMeasure))
    refine wp.imp hBranch ?_
    intro c hc
    cases c <;> simp only [P] at hc
    rename_i st1 s1
    rcases hc with ⟨hInv, hm⟩
    have hValues := hInv.values
    have hFrame : { s1 with values := [] } = s1 := by
      cases s1
      simp_all
    simpa [wp_simp, hFrame] using And.intro hInv hm

set_option Elab.async false in
theorem spec (env : HostEnv Unit) (ctx : Context) (st : Store Unit)
    (base target : Locals) (data : RunningData) (facts : RunningFacts ctx st base data)
    (hFuel : data.fuel ≠ 0) (i : Nat) (hRemaining : data.remaining ≠ 0)
    (hFind : findBestL data.orders ctx.taker = some i)
    (h : layout.Related base target) :
    wp Project.ClobLimit.«module» program
      (HeapStep.Post (fun st1 s1 => Invariant ctx st1 s1 ∧ measure st1 s1 < measure st base))
      st (HeapFrames.searchFrame target data.bookOwner data.book ctx.taker (some i)) env := by
  rw [program_eq]
  refine wp_transport layout.frame SearchRegion.searchShift env st _ _ sourceProg
    (HeapFrames.search_related base target h data.bookOwner data.book ctx.taker (some i))
    portable allowed _ _ ?_ (source_spec env ctx st base data facts hFuel i hRemaining hFind)
  intro a b hAB hP
  cases hAB <;> simp only at hP
  exact ⟨_, by assumption, hP⟩

#print axioms spec
end Project.ClobLimit.HeapSelect
