import Verified.Wasi.CostFunctionRun
import Verified.Wasi.CostEffectSpec
import Verified.Wasi.CostCodeSpec
import Verified.Wasi.CompilerFacts

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem CostEffectSpec.here {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {function : EffectFunc pureSigs effectSigs}
    {rest : EffectProg pureSigs effectSigs} {pool : Bytes.LiteralPool} {index typeIdx : Nat}
    (facts : CompilerFacts source target pure (rest.funs pure.funs) pool) (sourceHost : HostEnv Unit)
    (lookup : target.funcs[index]? = some (function.function source typeIdx pool))
    (form : Encoding.ProgramForm (releaseWhere function.params
      (paramSlots function.params function.modes 1) (fun i => !function.body.uses i)))
    (closed : Relocation.programClosed source.funcs.length (releaseWhere function.params
      (paramSlots function.params function.modes 1) (fun i => !function.body.uses i)) = true)
    (ready : function.body.Ready source function.positions (paramSlots function.params function.modes 1)
      (1 + widthSum function.params) (fun _ => false) pool)
    (covered : function.body.Covered pool) (place : function.body.placeArgs = true)
    (bodySpec : CostCommandCodeSpec source target pure rest pool function.body) :
    CostEffectSpec source target pure (.cons function rest) .here (3 + index) pool := by
  intro World host targetHost depth heap initial params args budget aborts
    valid at_ rep separate input scratch cap resources
  rw [PureTransport.memoryCap_zero_eq facts.layout.memoryCap] at cap
  refine cost_effectFunction_run facts.imports lookup rep.length ?_
  refine cost_function_body_wp (sourceHost := sourceHost) facts.runtime facts.layout facts.profile
    form closed at_ rep separate input scratch facts.poolApart cap ?_ ?_
  · intro high
    cases state : aborts with
    | true => rfl
    | false =>
        have fits := (resources state).2.entry
        have below : depth < depthLimit := by
          simpa only [Resource.entryFits, decide_eq_true_eq] using fits
        exact False.elim ((UInt64.not_le.mpr below) high)
  · intro middleHeap middle middleLocals below parameters positions values top sameWorld sameCap
      at_ vars safe apart cap
    have execution := bodySpec World host targetHost depth args
      (paramSlots function.params function.modes 1) (fun _ => false) function.positions
      (1 + widthSum function.params) middleHeap middle middleLocals budget aborts
      valid below (by rw [parameters]; rfl) positions
      (by simpa only [Bool.false_or] using vars) at_
      (by simpa only [Bool.false_or] using safe)
      (by simpa only [Bool.false_or] using apart) cap
      (by
        rw [parameters, List.length_cons, rep.length]
        change widthSum function.params + 1 ≤ 1 + widthSum function.params
        omega)
      (by simp only [EffectFunc.positions]; omega) ready covered place
      (fun noAbort => by
        obtain ⟨within, bounded⟩ := resources noAbort
        refine ⟨within.shift (c1 := 0) (c2 := budget) ?_ (by omega) sameCap, ?_⟩
        · rw [top]
          omega
        · rw [sameWorld]
          simpa only [entryModes, paramSlots_modes] using bounded.body)
    simpa only [Bool.false_or] using execution

end Verified.Wasi
