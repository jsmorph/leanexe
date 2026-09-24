import Project.ClobLimit.HeapIteration
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

namespace Project.ClobLimit.HeapLoop
open Wasm Project.LocalRegion Project.ClobLimit.HeapProgram
open Project.ClobLimit.HeapInvariant
open Project.ClobMatchFuel.LoopInvariant (Context RunningFacts)

set_option maxRecDepth 1048576

theorem guard_shape : guardProg = Project.ProofKit.FuelGuard.program 0 18 := rfl

def bodyProg : Program := guardProg ++ (dispatchProg ++ [.br 0])

theorem loop_shape : loopProg = [.block 0 0 [.loop 0 0 bodyProg]] := by
  simp only [loopProg, bodyProg, List.append_assoc]

set_option Elab.async false in
theorem spec (env : HostEnv Unit) (ctx : Context) (st : Store Unit)
    (base : Locals) (hInvariant : Invariant ctx st base)
    (Q : Assertion Unit) (rest : Program)
    (hDone : ∀ st1 s1, ExitAt ctx st1 s1 →
      wp Project.ClobLimit.«module» rest Q st1 s1 env) :
    wp Project.ClobLimit.«module» (loopProg ++ rest) Q st base env := by
  have hBaseValues := hInvariant.values
  rw [loop_shape]
  simp only [List.cons_append, List.nil_append]
  apply wp_block_cons
  apply wp_loop_cons (Inv := Invariant ctx) (μ := measure)
  · exact hInvariant
  · rintro st1 target ⟨source, hr, hi⟩
    have hValues := hr.values.trans hi.values
    have hTarget : { target with values := [] } = target := by
      cases target
      simp_all
    have hReadFuel := hr.reads 0 (by simp [Domain])
    have hReadDone := hr.reads 24 (by simp [Domain])
    change target.get 0 = source.get 0 at hReadFuel
    change target.get 18 = source.get 24 at hReadDone
    rcases hi with ⟨data, facts⟩ | ⟨data, facts⟩
    · rcases facts.locals with ⟨hp, hl, hv, hf, ho, ht, hs, hpr, hq, hbo, hb, htr, hrem, hob, hot, hd, _⟩
      have hfTarget := hReadFuel.trans hf
      have hdTarget := hReadDone.trans hd
      by_cases hz : data.fuel = 0
      · have hf0 : target.get 0 = some (.i64 0) := by simpa [hz] using hfTarget
        unfold bodyProg
        rw [guard_shape]
        apply Project.ProofKit.FuelGuard.zeroFuel_spec 0 18 Project.ClobLimit.«module» env st1 target
          hValues hf0
        simpa [wp_simp, hBaseValues, hValues, hTarget] using
          hDone st1 target ⟨source, hr, Or.inr ⟨data, facts, hz⟩⟩
      · unfold bodyProg
        rw [guard_shape]
        apply Project.ProofKit.FuelGuard.program_spec 0 18 Project.ClobLimit.«module» env st1 target
          data.fuel 0 hValues hfTarget hdTarget
        rw [if_neg (by simp [hz])]
        apply HeapIteration.spec env ctx st1 source target data facts hr hz
        intro st2 target2 hi2 hm
        have hv2 := hi2.values
        have ht2 : { target2 with values := [] } = target2 := by
          cases target2
          simp_all
        simpa [wp_simp, hValues, hv2, ht2] using And.intro hi2 hm
    · rcases facts.result with ⟨hb, ht, hrem, hd, hp, hl, hv⟩
      have hdSource : source.get 24 = some (.i64 1) := by
        simpa [Locals.get, hp, hl] using hd
      have hdTarget := hReadDone.trans hdSource
      have hfTarget := hReadFuel.trans facts.fuelLocal
      unfold bodyProg
      rw [guard_shape]
      apply Project.ProofKit.FuelGuard.program_spec 0 18 Project.ClobLimit.«module» env st1 target
        data.fuel 1 hValues hfTarget hdTarget
      simpa [wp_simp, hBaseValues, hValues, hTarget] using
        hDone st1 target ⟨source, hr, Or.inl ⟨data, facts⟩⟩

#print axioms spec
end Project.ClobLimit.HeapLoop
