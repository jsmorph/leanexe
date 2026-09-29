import CodeLib.Entry

namespace Wasm

theorem run_append_of_success {env : HostEnv α} {m : Module} {id : Nat}
    {initial final : Store α} {args values : List Value} {f : Function} {fuel : Nat}
    (hImp : m.imports[id]? = none)
    (hf : m.funcs[id - m.imports.length]? = some f)
    (hlen : args.length = f.numParams)
    (h : run fuel m id initial args env = .Success values final)
    (rest : List Value) :
    run fuel m id initial (args ++ rest) env = .Success (values ++ rest) final := by
  rw [run_eq hImp] at h ⊢
  simp only [hf] at h ⊢
  have ht : (args ++ rest).take f.numParams = args := by simp [← hlen]
  have hd : (args ++ rest).drop f.numParams = rest := by simp [← hlen]
  simp only [ht, hd] at *
  simp only [← hlen, List.take_length, List.drop_length, List.append_nil] at h
  cases he : exec fuel m initial (f.toLocals args.reverse) f.body env <;>
    simp only [he] at h ⊢
  all_goals simp_all
  all_goals split at h <;> simp_all

theorem TerminatesWith.append_args {env : HostEnv α} {m : Module} {id : Nat}
    {initial : Store α} {args : List Value} {f : Function}
    {P : Store α → List Value → Prop}
    (h : TerminatesWith env m id initial args P)
    (hImp : m.imports[id]? = none)
    (hf : m.funcs[id - m.imports.length]? = some f)
    (hlen : args.length = f.numParams) (rest : List Value) :
    TerminatesWith env m id initial (args ++ rest)
      (fun st values => ∃ out, values = out ++ rest ∧ P st out) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun fuel hFuel => ?_⟩
  obtain ⟨values, final, hRun, hP⟩ := hN fuel hFuel
  exact ⟨values ++ rest, final, run_append_of_success hImp hf hlen hRun rest,
    values, rfl, hP⟩

#print axioms run_append_of_success
#print axioms TerminatesWith.append_args
end Wasm
