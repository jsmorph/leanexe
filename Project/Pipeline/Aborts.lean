import CodeLib.Entry
import Project.ProofKit.CallRemainder

/-! `ReturnsOrAborts`: every run with enough fuel either returns values that satisfy the
postcondition or traps at an `unreachable` instruction.  The compiler emits `unreachable`
only where the allocator cannot grow memory and where an array is too long for memory,
so the predicate describes the result of every call that completes and of no other. -/

namespace Wasm

variable {α : Type} {env : HostEnv α} {m : Module} {id : Nat} {initial : Store α}
  {args : List Value} {P : Store α → List Value → Prop}

/-- Every run of entry `id` with at least some fuel returns values satisfying `P` or
traps at `unreachable`. -/
def ReturnsOrAborts (env : HostEnv α) (m : Module) (id : Nat) (initial : Store α)
    (args : List Value) (P : Store α → List Value → Prop) : Prop :=
  ∃ N, ∀ fuel ≥ N, (∃ vs st, run fuel m id initial args env = .Success vs st ∧ P st vs) ∨
    ∃ st, run fuel m id initial args env = .Trap st "unreachable"

theorem TerminatesWith.returnsOrAborts (h : TerminatesWith env m id initial args P) :
    ReturnsOrAborts env m id initial args P := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun fuel hFuel => .inl (hN fuel hFuel)⟩

theorem ReturnsOrAborts.mono {Q : Store α → List Value → Prop}
    (h : ReturnsOrAborts env m id initial args P) (hPQ : ∀ st vs, P st vs → Q st vs) :
    ReturnsOrAborts env m id initial args Q := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun fuel hFuel => ?_⟩
  rcases hN fuel hFuel with ⟨vs, st, hRun, hP⟩ | hTrap
  · exact .inl ⟨vs, st, hRun, hPQ st vs hP⟩
  · exact .inr hTrap

theorem run_append_of_trap {final : Store α} {f : Function} {fuel : Nat} {msg : String}
    (hImp : m.imports[id]? = none) (hf : m.funcs[id - m.imports.length]? = some f)
    (hlen : args.length = f.numParams) (h : run fuel m id initial args env = .Trap final msg)
    (rest : List Value) :
    run fuel m id initial (args ++ rest) env = .Trap final msg := by
  rw [run_eq hImp] at h ⊢
  simp only [hf] at h ⊢
  have ht : (args ++ rest).take f.numParams = args := by simp [← hlen]
  have ht' : args.take f.numParams = args := by simp [← hlen]
  simp only [ht, ht'] at h ⊢
  cases he : exec fuel m initial (f.toLocals args.reverse) f.body env <;>
    simp only [he] at h ⊢
  case Break n _ _ => cases n <;> simp at h
  case ReturnCall fid st vs =>
    cases hr : runTail fuel m fid st vs env <;> simp only [hr] at h ⊢ <;> simp_all
  all_goals simp_all

theorem ReturnsOrAborts.append_args {f : Function}
    (h : ReturnsOrAborts env m id initial args P)
    (hImp : m.imports[id]? = none) (hf : m.funcs[id - m.imports.length]? = some f)
    (hlen : args.length = f.numParams) (rest : List Value) :
    ReturnsOrAborts env m id initial (args ++ rest)
      (fun st values => ∃ out, values = out ++ rest ∧ P st out) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun fuel hFuel => ?_⟩
  rcases hN fuel hFuel with ⟨values, final, hRun, hP⟩ | ⟨final, hRun⟩
  · exact .inl ⟨values ++ rest, final, run_append_of_success hImp hf hlen hRun rest,
      values, rfl, hP⟩
  · exact .inr ⟨final, run_append_of_trap hImp hf hlen hRun rest⟩

/-- The entry rule: a body whose `wp` reaches `P` or the `unreachable` trap gives
`ReturnsOrAborts`. -/
theorem ReturnsOrAborts.of_wp_entry_for {f : Function}
    (hf : m.funcs[id - m.imports.length]? = some f)
    (h : wp m f.body
        (fun c => match c with
          | .Fallthrough st' s' =>
              P st' (s'.values.take f.results.length ++ args.drop f.numParams)
          | .Return st' vs =>
              P st' (vs.take f.results.length ++ args.drop f.numParams)
          | .Trap _ msg => msg = "unreachable"
          | _ => False)
        initial (f.toLocals (args.take f.numParams).reverse) env)
    (hImp : m.imports[id]? = none := by rfl) :
    ReturnsOrAborts env m id initial args P := by
  unfold wp at h
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun fuel hfuel => ?_⟩
  have hQ := hN fuel hfuel
  rw [run_eq hImp]; simp only [hf]
  cases hexec : exec fuel m initial (f.toLocals (args.take f.numParams).reverse) f.body env with
  | Fallthrough st' s' =>
    rw [hexec] at hQ
    exact .inl ⟨s'.values.take f.results.length ++ args.drop f.numParams, st', rfl, hQ⟩
  | Return st' vs =>
    rw [hexec] at hQ
    exact .inl ⟨vs.take f.results.length ++ args.drop f.numParams, st', rfl, hQ⟩
  | Trap st' msg =>
    rw [hexec] at hQ
    exact .inr ⟨st', by simp only at hQ; rw [hQ]⟩
  | Break n st' s' => rw [hexec] at hQ; exact hQ.elim
  | Invalid msg => rw [hexec] at hQ; exact hQ.elim
  | OutOfFuel => rw [hexec] at hQ; exact hQ.elim
  | ReturnCall fid st' vs => rw [hexec] at hQ; exact hQ.elim
  | Throwing tag targs st' s' => rw [hexec] at hQ; exact hQ.elim

/-- The call rule: a callee that returns with `Post` or aborts gives the caller's `wp`
when its assertion accepts the `unreachable` trap. -/
theorem wp_call_returnsOrAborts {st : Store α} {s : Locals} {rest : Program} {Q : Assertion α}
    {Post : Store α → List Value → Prop}
    (hRun : ReturnsOrAborts env m id st s.values Post)
    (hTrap : ∀ st', Q (.Trap st' "unreachable"))
    (hPost : ∀ st' vs, Post st' vs → wp m rest Q st' { s with values := vs } env) :
    wp m (.call id :: rest) Q st s env := by
  obtain ⟨N, hN⟩ := hRun
  rcases hN N le_rfl with ⟨vs, st', hRun, hPost_vs⟩ | ⟨st', hRun⟩
  · exact wp_call_at ⟨N, fun fuel hFuel => by
      rw [run_fuel_mono hFuel (by rw [hRun]; intro h; cases h)]
      exact ⟨vs, st', hRun, hPost_vs⟩⟩ hPost
  · unfold wp
    refine ⟨N + 1, fun fuel hFuel => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [exec_call_cons, run_fuel_mono (by omega : f ≥ N) (by rw [hRun]; intro h; cases h), hRun]
    exact hTrap st'

end Wasm
