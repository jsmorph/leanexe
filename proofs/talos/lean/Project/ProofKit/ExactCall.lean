import Project.ProofKit.CallRemainder
import Interpreter.Wasm.Wp.Call

namespace Wasm

theorem wp_call_exact_append {env : HostEnv α} {m : Module} {id : Nat}
    {st : Store α} {s : Locals} {args out : List Value} {f : Function}
    {rest : Program} {Q : Assertion α}
    (hRun : TerminatesWith env m id st args
      (fun final values => final = st ∧ values = out))
    (hImp : m.imports[id]? = none)
    (hf : m.funcs[id-m.imports.length]? = some f)
    (hlen : args.length = f.numParams) (tail : List Value)
    (hargs : s.values = args ++ tail)
    (hPost : wp m rest Q st { s with values := out ++ tail } env) :
    wp m (.call id :: rest) Q st s env := by
  have h := hRun.append_args hImp hf hlen tail
  rw [← hargs] at h
  refine wp_call_tw h ?_
  rintro st' values ⟨out', rfl, rfl, rfl⟩
  exact hPost

#print axioms wp_call_exact_append
end Wasm
