import Project.ProofKit.PackedFloatFrame

namespace Project.ProofKit.ReadOnlyBoolean
open Wasm PackedFloatFrame

def andProgram (body : Program) : Program :=
  [.iff 0 1 (body ++ [.constI64 0, .eqI64, .eqz]) [.const 0] [] [.i32]]

def BodySpec (module_ : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (params : List Value) (localCount : Nat) (body : Program) (answer : Bool) : Prop :=
  ∀ frame, frame.params = params → frame.locals.length = localCount → frame.values = [] →
    ∀ (Q : Assertion Unit) (rest : Program),
      (∀ result, result.params = params → result.locals.length = localCount →
        result.values = [.i64 (if answer then 1 else 0)] → wp module_ rest Q initial result env) →
      wp module_ (body ++ rest) Q initial frame env

theorem and_spec (module_ : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (params : List Value) (localCount : Nat) (body : Program) (answer accepted : Bool)
    (hBody : BodySpec module_ env initial params localCount body answer)
    (frame : Locals) (hParams : frame.params = params)
    (hLength : frame.locals.length = localCount)
    (hValues : frame.values = [.i32 (if accepted then 1 else 0)])
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ result, result.params = params → result.locals.length = localCount →
      result.values = [.i32 (if accepted && answer then 1 else 0)] →
      wp module_ rest Q initial result env) :
    wp module_ (andProgram body ++ rest) Q initial frame env := by
  cases accepted
  · simp only [andProgram, List.cons_append, List.nil_append, wp_iff_control_types]
    refine wp_iff_cons hValues ?_
    rw [ite_eq_right (by decide)]
    wp_packed_frame []
    exact hNext _ hParams hLength rfl
  · simp only [andProgram, List.cons_append, List.nil_append, wp_iff_control_types]
    refine wp_iff_cons hValues ?_
    rw [ite_eq_left (by decide)]
    apply hBody { frame with values := [] } hParams hLength rfl
    intro result hResultParams hResultLength hResultValues
    cases answer <;> wp_packed_frame [hResultValues]
    all_goals exact hNext _ hResultParams hResultLength rfl

theorem chain_spec (entries : List (Program × Bool))
    (module_ : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (params : List Value) (localCount : Nat) (accepted : Bool)
    (hBodies : ∀ entry ∈ entries, BodySpec module_ env initial params localCount entry.1 entry.2)
    (frame : Locals) (hParams : frame.params = params)
    (hLength : frame.locals.length = localCount)
    (hValues : frame.values = [.i32 (if accepted then 1 else 0)])
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ result, result.params = params → result.locals.length = localCount →
      result.values = [.i32 (if entries.foldl (fun valid entry => valid && entry.2) accepted
        then 1 else 0)] → wp module_ rest Q initial result env) :
    wp module_ (entries.flatMap (fun entry => andProgram entry.1) ++ rest) Q initial frame env := by
  induction entries generalizing frame accepted with
  | nil => exact hNext frame hParams hLength hValues
  | cons entry entries ih =>
    simp only [List.flatMap_cons, List.append_assoc]
    apply and_spec module_ env initial params localCount entry.1 entry.2 accepted
      (hBodies entry (by simp)) frame hParams hLength hValues
    intro next hNextParams hNextLength hNextValues
    apply ih (accepted && entry.2)
      (fun item hItem => hBodies item (List.mem_cons_of_mem entry hItem))
      next hNextParams hNextLength hNextValues
    exact hNext

#print axioms chain_spec
#print axioms and_spec
end Project.ProofKit.ReadOnlyBoolean
