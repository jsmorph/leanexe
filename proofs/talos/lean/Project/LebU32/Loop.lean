import Project.LebU32.Dispatch
import Project.ProofKit.FuelGuard
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

namespace Project.LebU32.Spec
open Wasm Project.Common Project.ProofKit Project.EulerRiemann.Execution

theorem encodingInvariant_values {seed : Heap} {initial : Store Unit} {input : UInt64}
    {current : Store Unit} {frame : Locals} (h : encodingInvariant seed initial input current frame) :
    frame.values = [] := by
  rcases h with h | h
  · obtain ⟨_, _, _, facts⟩ := h
    exact facts.frame.values
  · obtain ⟨_, _, hFrame, _⟩ := h
    exact hFrame.values

theorem loop_spec (env : HostEnv Unit) (seed : Heap) (initial current : Store Unit)
    (input : UInt64) (base : Locals) (hInvariant : encodingInvariant seed initial input current base)
    (hLength : (lebList 10 input).length ≤ 5)
    (hFit : seed.top.toNat + 112 < 4294967296)
    (hMemory : seed.top.toNat + 112 ≤ initial.mem.pages * 65536)
    (hPages : initial.mem.pages ≤ 65536) (hCap : initial.mem.pages ≤ initial.memoryCap «module» 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ final result, FinishedState seed initial input final result → wp «module» rest Q final result env) :
    wp «module» ([.block 0 0 [.loop 0 0 loopCode]] ++ rest) Q current base env := by
  have hBaseValues := encodingInvariant_values hInvariant
  have hShape : loopCode = FuelGuard.program 0 9 ++ dispatchCode := rfl
  simp only [List.cons_append, List.nil_append]
  apply wp_block_cons
  apply wp_loop_cons (Inv := encodingInvariant seed initial input) (μ := encodingMeasure)
  · exact hInvariant
  · intro current' frame hState
    have hValues := encodingInvariant_values hState
    have hEmpty : ({ frame with values := [] } : Locals) = frame := Frame.ext _ _ rfl rfl hValues.symm
    rcases hState with hRunning | hFinished
    · obtain ⟨count, value, bytes, facts⟩ := hRunning
      have hCount : count ≤ 4 := by have := facts.bound; omega
      have hFuel : frame.get 0 = some (.i64 (UInt64.ofNat (10 - count))) := by
        simp [Locals.get, facts.frame.params]
      have hFlag : frame.get 9 = some (.i64 0) := by
        simpa [Locals.get, facts.frame.params, facts.frame.locals] using facts.frame.done
      have hNonzero : UInt64.ofNat (10 - count) ≠ 0 := by
        intro hZero
        have hNat := congrArg UInt64.toNat hZero
        simp only [UInt64.toNat_ofNat', Nat.reducePow, show (0 : UInt64).toNat = 0 from rfl] at hNat
        omega
      rw [hShape]
      apply FuelGuard.program_spec 0 9 «module» env current' frame (UInt64.ofNat (10 - count)) 0
        hValues hFuel hFlag
      simp only [hNonzero, ne_eq, not_false_eq_true, and_self, ite_true]
      change wp «module» (dispatchCode ++ []) _ current' frame env
      apply dispatch_spec env seed initial current' input value frame count bytes facts
        hLength hFit hMemory hPages hCap
      intro final result hFinal hDecrease
      have hFinalValues := encodingInvariant_values hFinal
      have hFinalEmpty : ({ result with values := [] } : Locals) = result := Frame.ext _ _ rfl rfl hFinalValues.symm
      simpa [wp_simp, hValues, hFinalValues, hFinalEmpty] using And.intro hFinal hDecrease
    · obtain ⟨bytes, hBytes, hFrame, hStorage⟩ := hFinished
      have hFuel : frame.get 0 = some (.i64 (UInt64.ofNat (11 - (lebList 10 input).length))) := by
        simpa [Locals.get, hFrame.params] using hFrame.fuel
      have hFlag : frame.get 9 = some (.i64 1) := by
        simpa [Locals.get, hFrame.params, hFrame.locals] using hFrame.done
      rw [hShape]
      apply FuelGuard.program_spec 0 9 «module» env current' frame _ 1 hValues hFuel hFlag
      simpa [wp_simp, hBaseValues, hValues, hEmpty] using
        hDone current' frame ⟨bytes, hBytes, hFrame, hStorage⟩

#print axioms loop_spec
end Project.LebU32.Spec
