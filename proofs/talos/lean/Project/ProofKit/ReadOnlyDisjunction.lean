import Project.ProofKit.ReadOnlyBoolean

namespace Project.ProofKit.ReadOnlyDisjunction
open Wasm PackedFloatFrame ReadOnlyBoolean

def program (body : Program) : Program :=
  [.iff 0 1 [.const 1] (body ++ [.constI64 0, .eqI64, .eqz, .eqz]) [] [.i32]]

def negateProgram : Program := [.constI64 0, .eqI64, .eqz, .eqz]

def canonicalProgram : Program :=
  [.iff 0 1 [.constI64 1] [.constI64 0] [] [.i64], .constI64 1, .eqI64,
   .iff 0 1 [.constI64 1] [.constI64 0] [] [.i64], .constI64 0, .eqI64, .eqz]

theorem negate_spec (module_ : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (frame : Locals) (answer : Bool)
    (hValues : frame.values = [.i64 (if answer then 1 else 0)])
    (Q : Assertion Unit) (rest : Program)
    (hNext : wp module_ rest Q initial
      { frame with values := [.i32 (if !answer then 1 else 0)] } env) :
    wp module_ (negateProgram ++ rest) Q initial frame env := by
  cases answer <;> simp only [negateProgram, List.cons_append, List.nil_append] <;>
    wp_packed_frame [hValues] <;> exact hNext

theorem canonical_spec (module_ : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (frame : Locals) (answer : Bool)
    (hValues : frame.values = [.i32 (if answer then 1 else 0)])
    (Q : Assertion Unit) (rest : Program)
    (hNext : wp module_ rest Q initial frame env) :
    wp module_ (canonicalProgram ++ rest) Q initial frame env := by
  have hFrame : { frame with values := [.i32 (if answer then 1 else 0)] } = frame := by
    cases frame
    simp_all
  cases answer <;> simp only [canonicalProgram, List.cons_append, List.nil_append,
    wp_iff_control_types]
  all_goals
    refine wp_iff_cons hValues ?_
    first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]
    wp_packed_frame []
    refine wp_iff_cons rfl ?_
    first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]
    wp_packed_frame []
    rw [← hFrame] at hNext
    exact hNext

theorem program_spec (module_ : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (params : List Value) (localCount : Nat) (body : Program) (answer rejected : Bool)
    (hBody : BodySpec module_ env initial params localCount body answer)
    (frame : Locals) (hParams : frame.params = params)
    (hLength : frame.locals.length = localCount)
    (hValues : frame.values = [.i32 (if rejected then 1 else 0)])
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ result, result.params = params → result.locals.length = localCount →
      result.values = [.i32 (if rejected || !answer then 1 else 0)] →
      wp module_ rest Q initial result env) :
    wp module_ (program body ++ rest) Q initial frame env := by
  cases rejected
  · simp only [program, List.cons_append, List.nil_append, wp_iff_control_types]
    refine wp_iff_cons hValues ?_
    rw [ite_eq_right (by decide)]
    apply hBody { frame with values := [] } hParams hLength rfl
    intro result hResultParams hResultLength hResultValues
    cases answer <;> wp_packed_frame [hResultValues]
    all_goals exact hNext _ hResultParams hResultLength rfl
  · simp only [program, List.cons_append, List.nil_append, wp_iff_control_types]
    refine wp_iff_cons hValues ?_
    rw [ite_eq_left (by decide)]
    wp_packed_frame []
    exact hNext _ hParams hLength rfl

#print axioms program_spec
end Project.ProofKit.ReadOnlyDisjunction
