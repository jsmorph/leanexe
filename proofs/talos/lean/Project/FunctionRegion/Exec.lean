import Project.FunctionRegion.Step
import Project.FunctionRegion.NoTail

/-!
# Function-region semantic transport

A closed portable function region has the same interpreter behavior after its
function indices and direct calls are renamed.  The final theorem transports
fuel-free `TerminatesWith` specifications between the two modules.
Memory-observing instructions use the declaration equality recorded by `Shift`.
-/

namespace Project.FunctionRegion

open Wasm

private theorem exec_eq_of_one
    (hOne : ∀ (env : HostEnv α) st s inst,
      PortableInstruction domain inst →
      execOne fuel target st s (renameInstruction rename inst) env =
        execOne fuel source st s inst env)
    (env : HostEnv α) (st : Store α) (s : Locals) (program : Program)
    (hPortable : PortableProgram domain program) :
    exec fuel target st s (renameProgram rename program) env =
      exec fuel source st s program env := by
  induction program generalizing st s with
  | nil => simp only [renameProgram, exec]
  | cons inst rest restIH =>
      cases hPortable with
      | cons _ _ hInst hRest =>
          simp only [renameProgram, exec]
          rw [hOne env st s inst hInst]
          cases hResult : execOne fuel source st s inst env
          <;> simp only
          case Fallthrough nextStore nextLocals =>
            exact restIH nextStore nextLocals hRest

private theorem run_eq_of_exec
    (hShift : Shift source target rename domain)
    (hExec : ∀ (env : HostEnv α) st s program,
      PortableProgram domain program →
      exec fuel target st s (renameProgram rename program) env =
        exec fuel source st s program env)
    (env : HostEnv α) (st : Store α) (args : List Value) (id : Nat)
    (hDomain : domain id) :
    run fuel target (rename id) st args env =
      run fuel source id st args env := by
  obtain ⟨f, hSource, hTarget, hPortable⟩ := hShift.functions id hDomain
  simp only [run, hShift.sourceImports, hShift.targetImports,
    List.getElem?_nil, List.length_nil, Nat.sub_zero]
  rw [hTarget, hSource]
  simp only [renameFunction, Function.numParams, Function.toLocals]
  rw [hExec env st
    { params := (args.take f.params.length).reverse,
      locals := f.locals.map ValueType.zero,
      values := [] }
    f.body hPortable]
  cases hResult : exec fuel source st
      { params := (args.take f.params.length).reverse,
        locals := f.locals.map ValueType.zero,
        values := [] }
      f.body env <;> try rfl
  case Break label callStore callLocals =>
    cases label <;> rfl
  case ReturnCall callId callStore callValues =>
    exact (portableProgram_noReturnCall hPortable callId callStore callValues
      hResult).elim

private theorem semantics_eq_aux (hShift : Shift source target rename domain) :
    ∀ fuel,
      (∀ (env : HostEnv α) st s inst,
        PortableInstruction domain inst →
        execOne fuel target st s (renameInstruction rename inst) env =
          execOne fuel source st s inst env) ∧
      (∀ (env : HostEnv α) st s program,
        PortableProgram domain program →
        exec fuel target st s (renameProgram rename program) env =
          exec fuel source st s program env) ∧
      (∀ (env : HostEnv α) st args id,
        domain id →
        run fuel target (rename id) st args env =
          run fuel source id st args env) := by
  intro fuel
  induction fuel with
  | zero =>
      have hOne : ∀ (env : HostEnv α) st s inst,
          PortableInstruction domain inst →
          execOne 0 target st s (renameInstruction rename inst) env =
            execOne 0 source st s inst env := by
        intro env st s inst hPortable
        cases hPortable <;> simp only [renameInstruction, execOne.eq_def]
      have hExec := exec_eq_of_one hOne
      exact ⟨hOne, hExec, run_eq_of_exec hShift hExec⟩
  | succ fuel ih =>
      obtain ⟨ihOne, ihExec, ihRun⟩ := ih
      have hOne := execOne_succ hShift.memory ihOne ihExec ihRun
      have hExec := exec_eq_of_one hOne
      exact ⟨hOne, hExec, run_eq_of_exec hShift hExec⟩

theorem run_eq (hShift : Shift source target rename domain) (id : Nat)
    (hDomain : domain id) :
    run fuel target (rename id) st args env =
      run fuel source id st args env :=
  (semantics_eq_aux hShift fuel).2.2 env st args id hDomain

theorem terminatesWith
    (hShift : Shift source target rename domain) (id : Nat)
    (hDomain : domain id)
    (hSource : TerminatesWith env source id st args post) :
    TerminatesWith env target (rename id) st args post := by
  obtain ⟨minimumFuel, hFuel⟩ := hSource
  refine ⟨minimumFuel, fun fuel hMinimum => ?_⟩
  obtain ⟨values, finalStore, hRun, hPost⟩ := hFuel fuel hMinimum
  exact ⟨values, finalStore, by rw [run_eq hShift id hDomain]; exact hRun, hPost⟩

end Project.FunctionRegion
