import Project.ClobLimit.HeapLoop
import Project.ClobMatchFuel.LoopResult

namespace Project.ClobLimit.HeapResult
open Wasm Project.ClobLimit.HeapProgram
open Project.ClobMatchFuel.LoopInvariant (Context)
open Project.ClobMatchFuel.LoopResult
set_option maxRecDepth 1048576

def outputValues (ctx : Context) (data : OutputData) (bookOwner tradesOwner : Value) : List Value :=
  [.i64 ctx.result.remaining, .i64 data.trades, tradesOwner, .i64 data.book, bookOwner]

set_option Elab.async false in
theorem spec (env : HostEnv Unit) (ctx : Context) (st : Store Unit)
    (base : Locals) (hExit : HeapInvariant.ExitAt ctx st base)
    (Q : Assertion Unit) (rest : Program)
    (hDone : ∀ (data : OutputData) (bookOwner tradesOwner : Value) (final : Locals),
      final.values = outputValues ctx data bookOwner tradesOwner →
      OutputAt ctx st data → wp Project.ClobLimit.«module» rest Q st final env) :
    wp Project.ClobLimit.«module» (resultProg ++ rest) Q st base env := by
  obtain ⟨source, hr, hExit⟩ := hExit
  have hp := hr.targetParams
  have hl := hr.targetLocals
  change base.params.length = 11 at hp
  change base.locals.length = 78 at hl
  have hv := hr.values.trans hExit.values
  rcases hExit with ⟨data, facts⟩ | ⟨data, facts, hf⟩
  · rcases facts.result with ⟨hb, ht, hrem, hd, hsp, hsl, hsv⟩
    have hd' : base.get 18 = some (.i64 1) := by
      have h := hr.reads 24 (by simp [Domain])
      simpa [slots, Locals.get, hsp, hsl] using h.trans (by simpa [Locals.get, hsp, hsl] using hd)
    have hb' : base.get 14 = some (.i64 data.book) := by
      exact (hr.reads 21 (by simp [Domain])).trans (by simpa [Locals.get, hsp, hsl] using hb)
    have ht' : base.get 16 = some (.i64 data.trades) := by
      exact (hr.reads 22 (by simp [Domain])).trans (by simpa [Locals.get, hsp, hsl] using ht)
    have hrem' : base.get 17 = some (.i64 ctx.result.remaining) := by
      exact (hr.reads 23 (by simp [Domain])).trans (by simpa [Locals.get, hsp, hsl] using hrem)
    have hbl : base.locals[3] = .i64 data.book := by simpa [Locals.get, hp, hl] using hb'
    have htl : base.locals[5] = .i64 data.trades := by simpa [Locals.get, hp, hl] using ht'
    have hrl : base.locals[6] = .i64 ctx.result.remaining := by simpa [Locals.get, hp, hl] using hrem'
    have hdl : base.locals[7] = .i64 1 := by simpa [Locals.get, hp, hl] using hd'
    unfold resultProg
    wp_run_with [hp, hl, hv, hdl]
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_run_with [hp, hl, hv, hbl, htl, hrl]
    apply hDone (completedOutputData data) base.locals[2] base.locals[4]
    · rfl
    · exact of_completed facts
  · rcases facts.locals with ⟨hsp, hsl, hsv, hsf, ho, htr, hs, hpr, hq, hbo, hb, ht, hrem, hob, hot, hd, _⟩
    have hd' : base.get 18 = some (.i64 0) := (hr.reads 24 (by simp [Domain])).trans hd
    have hb' : base.get 7 = some (.i64 data.book) := (hr.reads 15 (by simp [Domain])).trans hb
    have ht' : base.get 9 = some (.i64 data.trades) := (hr.reads 17 (by simp [Domain])).trans ht
    have hrem' : base.get 10 = some (.i64 data.remaining) := (hr.reads 18 (by simp [Domain])).trans hrem
    have hbo' : base.get 6 = some (.i64 data.bookOwner) := (hr.reads 14 (by simp [Domain])).trans hbo
    have hbl : base.params[7] = .i64 data.book := by simpa [Locals.get, hp, hl] using hb'
    have htl : base.params[9] = .i64 data.trades := by simpa [Locals.get, hp, hl] using ht'
    have hrl : base.params[10] = .i64 data.remaining := by simpa [Locals.get, hp, hl] using hrem'
    have hbol : base.params[6] = .i64 data.bookOwner := by simpa [Locals.get, hp, hl] using hbo'
    have hdl : base.locals[7] = .i64 0 := by simpa [Locals.get, hp, hl] using hd'
    have hSource := facts.source
    rw [hf] at hSource
    simp only [UInt64.toNat_zero, Project.ClobMatchFuel.Model.matchFuelL] at hSource
    unfold resultProg
    wp_run_with [hp, hl, hv, hdl]
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    wp_run_with [hp, hl, hv, hbl, htl, hrl, hbol]
    apply hDone (runningOutputData data) (.i64 data.bookOwner) base.params[8]
    · simp [outputValues, runningOutputData, hSource, Project.ClobMatchFuel.LoopInvariant.RunningData.sourceState]
    · exact of_zero_running facts hf

#print axioms spec
end Project.ClobLimit.HeapResult
