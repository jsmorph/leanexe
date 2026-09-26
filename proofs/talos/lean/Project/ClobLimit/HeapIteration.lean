import Project.ClobLimit.HeapDispatch
import Project.ClobLimit.HeapInvariant

namespace Project.ClobLimit.HeapIteration
open Wasm Project.Clob Project.ClobFindBest.Model Project.LocalRegion
open Project.ClobLimit.HeapProgram Project.ClobLimit.HeapFrames
open Project.ClobMatchFuel.LoopInvariant
set_option maxRecDepth 1048576
set_option maxHeartbeats 8000000

set_option Elab.async false in
theorem stop_spec (env : HostEnv Unit) (ctx : Context) (st : Store Unit)
    (base source target : Locals) (data : RunningData) (facts : RunningFacts ctx st base data)
    (hFuel : data.fuel ≠ 0)
    (hStop : data.remaining = 0 ∨ findBestL data.orders ctx.taker = none)
    (h : layout.Related source target) (hSameFuel : source.get 0 = base.get 0)
    (bookOwner tradesOwner : Value)
    (Q : Assertion Unit) (rest : Program)
    (hDone : ∀ st1 s1, HeapInvariant.Invariant ctx st1 s1 →
      HeapInvariant.measure st1 s1 < ClobMatchFuel.LoopInvariant.measure st base →
      wp Project.ClobLimit.«module» rest Q st1 s1 env) :
    wp Project.ClobLimit.«module» rest Q st
      (completeTarget target bookOwner tradesOwner data.book data.trades data.remaining) env := by
  let s1 := completeSource source bookOwner tradesOwner data.book data.trades data.remaining
  have hRelation := complete_related source target h bookOwner tradesOwner data.book data.trades data.remaining
  have hResult := complete_result source bookOwner tradesOwner data.book data.trades data.remaining
    h.sourceParams h.sourceLocals
  have hFuelResult : s1.get 0 = some (.i64 data.fuel) := by
    rw [complete_fuel source bookOwner tradesOwner data.book data.trades data.remaining h.sourceParams,
      hSameFuel]
    exact facts.locals.2.2.2.1
  have hc := ClobMatchFuel.LoopCompletion.of_stop ctx st base data facts hFuel hStop s1 hResult hFuelResult
  apply hDone st _ ⟨s1, hRelation, Or.inr hc⟩
  rw [HeapInvariant.measure_eq st hRelation, measure_completed hc, measure_running facts]
  omega

set_option Elab.async false in
theorem spec (env : HostEnv Unit) (ctx : Context) (st : Store Unit)
    (base target : Locals) (data : RunningData) (facts : RunningFacts ctx st base data)
    (h : layout.Related base target) (hFuel : data.fuel ≠ 0)
    (Q : Assertion Unit) (rest : Program)
    (hDone : ∀ st1 s1, HeapInvariant.Invariant ctx st1 s1 →
      HeapInvariant.measure st1 s1 < HeapInvariant.measure st target →
      wp Project.ClobLimit.«module» rest Q st1 s1 env) :
    wp Project.ClobLimit.«module» (dispatchProg ++ rest) Q st target env := by
  rcases facts.locals with ⟨hp, hl, hv, hf, ho, ht, hs, hpr, hq, hbo, hb, htr, hr, _⟩
  have htp := h.targetParams
  have htl := h.targetLocals
  change target.params.length = 11 at htp
  change target.locals.length = 78 at htl
  have hValues := h.values.trans hv
  have hLength : data.orders.length < 4294967296 := by
    have hh := facts.book32
    unfold fixedArrayBytes at hh
    omega
  have hDone' : ∀ st1 s1, HeapInvariant.Invariant ctx st1 s1 →
      HeapInvariant.measure st1 s1 < measure st base →
      wp Project.ClobLimit.«module» rest Q st1 s1 env := by
    intro st1 s1 hi hm
    apply hDone st1 s1 hi
    simpa only [HeapInvariant.measure_eq st h] using hm
  apply HeapDispatch.dispatch_spec env st target data.bookOwner data.book data.trades data.remaining
    (target.params[8]'(by omega)) ctx.taker data.orders htp htl hValues
  · simpa [slots] using (h.reads 9 (by simp [Domain])).trans ho
  · simpa [slots] using (h.reads 10 (by simp [Domain])).trans ht
  · simpa [slots] using (h.reads 11 (by simp [Domain])).trans hs
  · simpa [slots] using (h.reads 12 (by simp [Domain])).trans hpr
  · simpa [slots] using (h.reads 13 (by simp [Domain])).trans hq
  · simpa [slots] using (h.reads 14 (by simp [Domain])).trans hbo
  · simpa [slots] using (h.reads 15 (by simp [Domain])).trans hb
  · simp [Locals.get, htp]
  · simpa [slots] using (h.reads 17 (by simp [Domain])).trans htr
  · simpa [slots] using (h.reads 18 (by simp [Domain])).trans hr
  · exact hLength
  · exact facts.bookOwned.2
  · intro hz
    exact stop_spec env ctx st base base target data facts hFuel (Or.inl hz) h rfl _ _ Q rest hDone'
  · intro hn
    apply stop_spec env ctx st base _ _ data facts hFuel (Or.inr hn)
      (search_related base target h data.bookOwner data.book ctx.taker none) _ _ _ Q rest hDone'
    simp [ClobMatchFuel.Iteration.searchFrame, ClobMatchFuel.Iteration.searchLocals, Locals.get, hp, hl]
  · intro i hn hi
    refine wp.imp (HeapSelect.spec env ctx st base target data facts hFuel i hn hi h) ?_
    intro c hc
    cases c <;> simp only [HeapStep.Post] at hc
    rename_i st1 target1
    rcases hc with ⟨source, hr, hi, hm⟩
    have hv := hr.values.trans hi.values
    have hTarget : { target1 with values := [] } = target1 := by
      cases target1
      simp_all
    have hx := hDone' _ _ ⟨source, hr, hi⟩ (by simpa only [HeapInvariant.measure_eq _ hr] using hm)
    simpa [HeapDispatch.selectedPost, HeapDispatch.zeroIffPost, wp_simp, hTarget] using hx

#print axioms spec
end Project.ClobLimit.HeapIteration
