import Project.Compiler.ScalarEvaluation

namespace Project.Compiler.ScalarLowering

open Project.ProofKit.ScalarTransition (State)
open LeanExe.Wasm.ScalarDescriptor (Expr Cond)

/-- Execution of the actual emitted structured instructions, interpreted in
Talos. The source store is preserved; scratch locals may change. This theorem
does not yet claim correspondence with encoded or decoded module bytes. -/
theorem expression_execution (e : Expr) (scratch : Nat)
    {source : LeanExe.IR.ScalarStore} {state : State} {value : UInt64}
    (evaluation : e.eval source = some value) (agree : Agrees source state)
    (above : source.length ≤ scratch)
    (room : scratch + e.scratchWidth ≤ capacity state)
    (values : List Wasm.Value) (m : Wasm.Module) (env : Wasm.HostEnv α) (store : Wasm.Store α) :
    ∃ code next, program (e.emit scratch) = some code ∧ Agrees source next ∧
      capacity next = capacity state ∧
      Wasm.wp m code (fun outcome => outcome = .Fallthrough store (next.toLocals (.i64 value :: values)))
        store (state.toLocals values) env := by
  obtain ⟨next, computed, preserved, size⟩ := expression_eval e scratch evaluation agree above room
  refine ⟨(expression e).program scratch, next, expression_program e scratch, preserved, size, ?_⟩
  have executed := Project.ProofKit.ScalarTransition.Expr.program_spec
    (expression e) scratch state next value values m env store []
    (fun outcome => outcome = .Fallthrough store (next.toLocals (.i64 value :: values)))
    computed (by simp)
  simpa using executed

theorem state_get_flatten (state : State) (index : Nat) :
    state.get index = (state.params ++ state.locals)[index]? := by
  unfold State.get
  by_cases hp : index < state.params.length
  · simp [hp, List.getElem?_append_left hp]
  · rw [List.getElem?_append_right (by omega)]
    by_cases hl : index < state.params.length + state.locals.length
    · simp [hp, hl]
    · have out : state.locals[index - state.params.length]? = none :=
        List.getElem?_eq_none (by omega)
      simp [hp, hl, out]

theorem agrees_of_flatten {source : LeanExe.IR.ScalarStore} {state : State}
    (extra : List Wasm.Value) (flat : state.params ++ state.locals = source.map Wasm.Value.i64 ++ extra) :
    Agrees source state := by
  intro index value read
  have bound := (List.getElem?_eq_some_iff.mp read).1
  rw [state_get_flatten, flat, List.getElem?_append_left (by simpa using bound)]
  simp [List.getElem?_map, read]

def scalarState (args : List UInt64) (scratchWidth : Nat) : State :=
  { params := args.map Wasm.Value.i64
    locals := List.replicate (scratchWidth + 1) (.i64 0) }

theorem scalarState_agrees (args : List UInt64) (width : Nat) :
    Agrees (args ++ [0]) (scalarState args width) := by
  apply agrees_of_flatten (List.replicate width (.i64 0))
  simp [scalarState, List.replicate_succ, List.append_assoc]

@[simp] theorem scalarState_capacity (args : List UInt64) (width : Nat) :
    capacity (scalarState args width) = args.length + 1 + width := by
  simp [capacity, scalarState]
  omega

end Project.Compiler.ScalarLowering
