import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Tactic
import Project.TalosCompat

namespace Project.ProofKit.AliasGuards
open Wasm

@[simp] theorem get_with_values (frame : Locals) (values : List Value) (i : Nat) :
    ({ frame with values := values } : Locals).get i = frame.get i := rfl

theorem restore_values (frame : Locals) (h : frame.values = [.i32 1]) :
    ({ params := frame.params, locals := frame.locals, values := [.i32 1] } : Locals) = frame := by
  cases frame
  simp_all

/-- Short-circuit comparisons emitted before releasing a potentially aliased owner. -/
def program (owner : Nat) (kept : List Nat) : Wasm.Program :=
  kept.map fun slot => .iff 0 1
    [.localGet owner, .localGet slot, .eqI64, .eqz] [.const 0] [] [.i32]

/-- Distinct kept roots preserve a true guard and every caller local. -/
theorem distinct (m : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals) (owner : Nat) (kept : List Nat) (root : UInt64)
    (hValues : frame.values = [.i32 1])
    (hOwner : frame.get owner = some (.i64 root))
    (hProtected : ∀ slot ∈ kept, ∃ other : UInt64,
      frame.get slot = some (.i64 other) ∧ root ≠ other)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp m rest Q st frame env) :
    wp m (program owner kept ++ rest) Q st frame env := by
  induction kept with
  | nil => simpa [program] using hNext
  | cons slot slots ih =>
    obtain ⟨other, hOther, hNe⟩ := hProtected slot (by simp)
    simp only [program, List.map_cons, List.cons_append]
    simp only [wp_iff_control_types]
    apply wp_iff_cons hValues
    rw [ite_eq_left (by decide : (1 : UInt32) ≠ 0)]
    simp only [wp_localGet_cons, get_with_values, hOwner, hOther,
      wp_eqI64_cons, wp_eqz_cons, hNe, ite_false, ite_true, wp_nil]
    simpa only [program, List.take_succ_cons, List.take_zero, List.drop_zero, List.nil_append, List.append_nil,
      restore_values frame hValues] using
      ih (fun s hs => hProtected s (by simp [hs]))

#print axioms distinct
end Project.ProofKit.AliasGuards
