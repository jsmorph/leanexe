import Project.Compiler.ScalarStatements

namespace Project.ProofKit.ScalarTransition

/-- A finite execution trace for a loop's checked condition and body. -/
inductive WhileTrace (condition : Expr .bool) (body : Stmt) (scratch : Nat) :
    State → State → Nat → Prop where
  | done (tested : condition.eval scratch current = some (false, final)) :
      WhileTrace condition body scratch current final 0
  | step (tested : condition.eval scratch current = some (true, afterCondition))
      (executed : body.eval scratch afterCondition = some afterBody)
      (rest : WhileTrace condition body scratch afterBody final count) :
      WhileTrace condition body scratch current final (count + 1)

/-- A finite trace supplies a decreasing iteration count for the existing loop rule. -/
theorem WhileTrace.program_spec {condition : Expr .bool} {body : Stmt} {scratch count : Nat}
    {initial final : State} (trace : WhileTrace condition body scratch initial final count)
    (values : List Wasm.Value) (module_ : Wasm.Module) (env : Wasm.HostEnv α) (store : Wasm.Store α)
    (rest : Wasm.Program) (Q : Wasm.Assertion α)
    (next : Wasm.wp module_ rest Q store (final.toLocals values) env) :
    Wasm.wp module_ (whileProgram scratch condition body ++ rest) Q store (initial.toLocals values) env := by
  classical
  let Inv := fun current => ∃ count, WhileTrace condition body scratch current final count
  let measure := fun current => if h : Inv current then Nat.find h else 0
  apply whileProgram_spec condition body scratch initial values module_ env store rest Q Inv measure
  · exact ⟨count, trace⟩
  · intro current invariant
    have selected := Nat.find_spec invariant
    generalize countEq : Nat.find invariant = remaining at selected
    cases selected with
    | done tested => exact ⟨false, final, tested, next⟩
    | step tested executed tail =>
      have tailInv : Inv _ := ⟨_, tail⟩
      refine ⟨true, _, tested, _, executed, tailInv, ?_⟩
      have bound := Nat.find_min' tailInv tail
      simp only [measure, dite_eq_left tailInv, dite_eq_left invariant, countEq]
      omega

end Project.ProofKit.ScalarTransition
